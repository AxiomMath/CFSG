module

public import CFSG.Sporadic.Schreier.RuDefs

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def ruM1 : Equiv.Perm (Fin 4060) := (slotRun ruMProg ruA0 ruA1).1

@[expose] def ruM2 : Equiv.Perm (Fin 4060) := (slotRun ruMProg ruA0 ruA1).2

@[expose] def ruRw : Equiv.Perm (Fin 4060) := evalSigned [ruM1, ruM2] ruRMWord

@[expose] def ruWw : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] ruAlignmentSeedWord

@[expose] def ruUw : Equiv.Perm (Fin 4060) := ruWw * ruRw * ruWw⁻¹ * ruA0

@[expose] def ruHw : Equiv.Perm (Fin 4060) := ruUw ^ 7 * ruWw

@[expose] def ruLGens : List (Equiv.Perm (Fin 4060)) :=
  ruLMWords.map fun x => ruHw * evalSigned [ruM1, ruM2] x * ruHw⁻¹

@[expose] def ruLGen (i : ℕ) : Equiv.Perm (Fin 4060) := ruLGens.getD (i - 1) 1

@[expose] def ruL : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {g | g ∈ ruLGens}

@[expose] def ruFusRec (i : ℕ) : List ℤ × List ℤ × ℕ := ruSylowFusion.getD (i - 1) ([], [], 1)

@[expose] def ruFusX (i : ℕ) : Equiv.Perm (Fin 4060) := evalSigned ruSGens (ruFusRec i).1

@[expose] def ruFusG (i : ℕ) : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] (ruFusRec i).2.1

@[expose] def ruFusD (i : ℕ) : ℕ := (ruFusRec i).2.2

@[expose] def ruFusH (i : ℕ) : Equiv.Perm (Fin 4060) :=
  (ruFusG i * ruA0 * (ruFusG i)⁻¹ * ruFusX i) ^ ((ruFusD i - 1) / 2) * ruFusG i

@[expose] def ruObsRec (p : ℕ) : List ℤ × ℕ := (ruOddNormalObstructions.lookup p).getD ([], 0)

@[expose] def ruYp (p : ℕ) : Equiv.Perm (Fin 4060) := evalSigned ruLGens (ruObsRec p).1

@[expose] def ruObsConj (p : ℕ) : ℕ := (ruObsRec p).2

end CFSG.Sporadic.RuSchreier
