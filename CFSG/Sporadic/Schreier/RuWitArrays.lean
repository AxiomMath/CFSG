module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Sporadic.Schreier.RuWitDefs

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native

@[expose] def ruMRunA : Array ℕ × Array ℕ × Bool := slotRunA 4060 ruMProg ruA0A ruA1A

@[expose] def ruM1A : Array ℕ := ruMRunA.1

@[expose] def ruM2A : Array ℕ := ruMRunA.2.1

@[expose] def ruSeedWordA (w : List ℤ) : Array ℕ :=
  wordA 4060 #[ruA0A, ruA1A] #[ruInv ruA0A, ruInv ruA1A] w

@[expose] def ruMWordA (w : List ℤ) : Array ℕ :=
  wordA 4060 #[ruM1A, ruM2A] #[ruInv ruM1A, ruInv ruM2A] w

@[expose] def ruRwA : Array ℕ := ruMWordA ruRMWord

@[expose] def ruWwA : Array ℕ := ruSeedWordA ruAlignmentSeedWord

@[expose] def ruUwA : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 ruWwA ruRwA) (ruInv ruWwA)) ruA0A

@[expose] def ruHwA : Array ℕ := compA 4060 (powA 4060 ruUwA 7) ruWwA

@[expose] def ruLGensA : Array (Array ℕ) :=
  (ruLMWords.map fun x => compA 4060 (compA 4060 ruHwA (ruMWordA x)) (ruInv ruHwA)).toArray

@[expose] def ruFusXA (i : ℕ) : Array ℕ := wordA 4060 ruSGensA (ruSGensA.map ruInv) (ruFusRec i).1

@[expose] def ruFusGA (i : ℕ) : Array ℕ := ruSeedWordA (ruFusRec i).2.1

@[expose] def ruFusHA (i : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 (compA 4060 (compA 4060 (compA 4060 (ruFusGA i) ruA0A)
    (ruInv (ruFusGA i))) (ruFusXA i)) ((ruFusD i - 1) / 2)) (ruFusGA i)

@[expose] def ruYpA (p : ℕ) : Array ℕ := wordA 4060 ruLGensA (ruLGensA.map ruInv) (ruObsRec p).1

end CFSG.Sporadic.RuSchreier
