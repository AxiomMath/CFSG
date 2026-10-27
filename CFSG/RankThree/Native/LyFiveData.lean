
module

public import CFSG.RankThree.Native.LyConjugationBase

public noncomputable section

namespace CFSG.RankThree.Native

@[expose] def lyFiveRegs : ℕ → Equiv.Perm (Fin lyN) := fiveSlpRun lyFiveProg (fiveInit lyA0 lyA1)

@[expose] def lyFiveA : Equiv.Perm (Fin lyN) := lyFiveRegs 1

@[expose] def lyFiveB : Equiv.Perm (Fin lyN) := lyFiveRegs 2

@[expose] def lyFiveM : Subgroup (Equiv.Perm (Fin lyN)) := Subgroup.closure {lyFiveA, lyFiveB}

@[expose] def lyFiveX : Equiv.Perm (Fin lyN) := lyFiveA ^ 5

@[expose] def lyFiveV (i : Fin 4) : Equiv.Perm (Fin lyN) :=
  fiveWord lyFiveA lyFiveB (lyFiveVWords i)

@[expose] def lyFiveQ : Subgroup (Equiv.Perm (Fin lyN)) := fiveQ lyFiveX lyFiveV

@[expose] def lyFiveU : Subgroup (Equiv.Perm (Fin lyN)) :=
  Subgroup.closure {lyFiveA, lyFiveB * lyFiveA * lyFiveB⁻¹, lyFiveB ^ 2 * lyFiveA * (lyFiveB ^ 2)⁻¹,
    lyFiveB ^ 3 * lyFiveA * (lyFiveB ^ 3)⁻¹, lyFiveB ^ 4}

theorem R3E_Ly_first_five_centralizer_certificate_data :
    lyFiveA = fiveSlpRun lyFiveProg (fiveInit lyA0 lyA1) 1 ∧
      lyFiveB = fiveSlpRun lyFiveProg (fiveInit lyA0 lyA1) 2 ∧
      lyFiveM = Subgroup.closure {lyFiveA, lyFiveB} ∧ lyFiveX = lyFiveA ^ 5 ∧
      (∀ i, lyFiveV i = fiveWord lyFiveA lyFiveB (lyFiveVWords i)) ∧
      lyFiveQ = Subgroup.closure (insert lyFiveX (Set.range lyFiveV)) ∧
      lyFiveU = Subgroup.closure {lyFiveA, lyFiveB * lyFiveA * lyFiveB⁻¹,
        lyFiveB ^ 2 * lyFiveA * (lyFiveB ^ 2)⁻¹, lyFiveB ^ 3 * lyFiveA * (lyFiveB ^ 3)⁻¹,
        lyFiveB ^ 4} ∧
      (∀ (c : ZMod 5) (e : Fin 4 → ZMod 5), fiveNF lyFiveX lyFiveV c e =
        lyFiveV 3 ^ (e 3).val * lyFiveV 2 ^ (e 2).val * lyFiveV 1 ^ (e 1).val *
          lyFiveV 0 ^ (e 0).val * lyFiveX ^ c.val) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, fun _ _ => rfl⟩

end CFSG.RankThree.Native
