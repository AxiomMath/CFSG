module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LieType.BorelTits

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16nt_orth_h1_plus_of_gen {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r : ℕ}
    (hr : 3 ≤ r) (hK : Nat.card K = 2) {S : Set (Fin r ⊕ Fin r → K)}
    (hS : ∀ v ∈ S, StatedQuadPlus r K v = 1) (hgen : S16ntNormOneGen (StatedQuadPlus r K) S) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (orthGroup (StatedQuadPlus r K)))) + 2 * r ≤ S.ncard := by
  have h3 : 3 ≤ Fintype.card (Fin r ⊕ Fin r) := by
    simp [Fintype.card_sum]; omega
  have hS' : ∀ v ∈ S, (quadPlusForm r K).Q v = 1 := fun v hv => hS v hv
  have hgen' : S16ntNormOneGen (quadPlusForm r K).Q S := hgen
  have h := w183_orth_natural_h1_bound (K := K) hK h3 (quadPlusForm r K) hS' hgen'
  have hc : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
    simp [Fintype.card_sum]; omega
  rw [hc] at h
  exact h

theorem s16nt_orth_h1_minus_of_gen {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r : ℕ}
    (hr : 3 ≤ r) (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {S : Set (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K)}
    (hS : ∀ v ∈ S, StatedQuadMinus r K b c v = 1)
    (hgen : S16ntNormOneGen (StatedQuadMinus r K b c) S) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (orthGroup (StatedQuadMinus r K b c)))) + 2 * r ≤ S.ncard := by
  have h3 : 3 ≤ Fintype.card (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := by
    simp [Fintype.card_sum]; omega
  have hS' : ∀ v ∈ S, (quadMinusForm r K b c hirr).Q v = 1 := fun v hv => hS v hv
  have hgen' : S16ntNormOneGen (quadMinusForm r K b c hirr).Q S := hgen
  have h := w183_orth_natural_h1_bound (K := K) hK h3 (quadMinusForm r K b c hirr) hS' hgen'
  have hc : Fintype.card (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) = 2 * r := by
    simp [Fintype.card_sum]; omega
  rw [hc] at h
  exact h

theorem s16nt_orth_h1_plus_two {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r : ℕ}
    (hr : 3 ≤ r) (hK : Nat.card K = 2) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (orthGroup (StatedQuadPlus r K)))) ≤ 1 := by
  obtain ⟨S, hcard, hS, hgen⟩ := s16nt_gen_plus hr hK
  have h := s16nt_orth_h1_plus_of_gen hr hK hS hgen
  omega

theorem s16nt_orth_h1_minus_two {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r : ℕ}
    (hr : 3 ≤ r) (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (orthGroup (StatedQuadMinus r K b c)))) = 0 := by
  obtain ⟨S, hcard, hS, hgen⟩ := s16nt_gen_minus (r := r) (by omega) hK hirr
  have h := s16nt_orth_h1_minus_of_gen hr hK hirr hS hgen
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
