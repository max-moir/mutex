import Veil

-- Language options
set_option linter.dupNamespace false
set_option veil.printCounterexamples true


veil module Mutex

type node
type ticket

instantiate tot : TotalOrder node
open TotalOrder

-- Nodes
relation critical : node → Prop
function choosing : node → Prop
function trying : node → Prop
function number   : node → ℕ

#gen_state

#print State

-- Initial state
after_init {
  critical N := False;
  choosing N := False;
  number N := 0;
}

#print initialState?


action choose (n : node)  = {
  require ¬ choosing n;
  choosing n := True;

  -- Find ticket value greater than all others
  let t_max ← fresh;
  require ∀ j, j ≠ n → number j < t_max;
  number n := t_max;

  choosing n := False;
  trying n := True;
}


-- Try to enter CS
action enter (i : node) = {
  require trying i;
  require number i != 0;
  require critical i = False;

  require ∀ j, j ≠ i →
    (choosing j = False) ∧
    ((number j = 0) ∨
     (number i < number j) ∨
     (number i = number j ∧ le i j ∧ ¬ le j i)
     );

  critical i := True;
  trying i := False;
}

-- Exit CS
action exit (n : node) = {
  require critical n
  critical n := False
  number n := 0
}



-- Invariants

-- safety [mutex] (critical I ∧ critical J) → I = J

invariant [different_vals]
  number I ≠ 0 →
    number I = number J →
      I = J

-- invariant [critical_lowest]
--   critical I →
--     ∀ J, J ≠ I →
--       number I < number J

#gen_spec
#check_invariants

end Mutex
