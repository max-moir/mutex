import Veil

-- Language options
set_option linter.dupNamespace false
set_option veil.printCounterexamples true


veil module Mutex

type node
type ticket

instantiate tot : TotalOrderWithMinimum node
open TotalOrderWithMinimum

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


action choose (i : node)  = {
  require ¬ choosing i;
  choosing i := True;

  -- Find ticket value greater than all others
  let t_max ← fresh;
  require ∀ j, j ≠ i → number j < t_max;
  number i := t_max;

  choosing i := False;
  trying i := True;
}


-- Try to enter CS
action enter (i : node) = {
  require trying i;
  require number i != 0;
  require critical i = False;

  -- Only allow enter if not choosing
  require ∀ j, j ≠ i → choosing j = False;

  -- Only allow enter if i holds the smallest non-zero ticket number
  require ∀ j, j ≠ i →
    (number j = 0) ∨
    (number i < number j) ∨
    (number i = number j ∧ lt i j);

  critical i := True;
  trying i := False;
}

-- Exit CS
action exit (i : node) = {
  require critical i
  critical i := False
  number i := 0
}



-- Invariants

safety [mutex] (critical I ∧ critical J) → I = J

invariant [different_vals]
  number I ≠ 0 →
    number I = number J →
      I = J

invariant [critical_lowest]
  critical I →
     ∀ J, J ≠ I →
       number I < number J



#gen_spec
#check_invariants

end Mutex
