module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

theorem sl2_three_conj_subfield {F : Type} [Field F] [Finite F] [CharP F 2] (k : Subfield F)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∃ y : Matrix.SpecialLinearGroup (Fin 2) k,
      g * x * g⁻¹ = Matrix.SpecialLinearGroup.map k.subtype y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) ≠ 0 := by
    intro h
    exact one_ne_zero (α := F) (by linear_combination h - h2)
  obtain ⟨hB3, hB1⟩ := KS11Lie4Proof.sl2Three_pow_three F
  obtain ⟨A, hA⟩ := Item1118Res3Proof.exists_conj_of_pow_three h3 hx3 hx1 hB3 hB1
  refine ⟨A, KS11Lie4Proof.sl2Three k, ?_⟩
  rw [hA]
  apply Subtype.ext
  show (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) =
    k.subtype.mapMatrix (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) k)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Plain

section Model


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem exists_conj_A0 (P : D4Par n X σ) {x : C0 σ} (hx : x ∈ Asub σ) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : ∃ g ∈ Asub σ, g * x * g⁻¹ ∈ A0sub σ := by
  haveI := P.charP
  rw [← iotaA_range P] at hx
  obtain ⟨x', rfl⟩ := hx
  have hx'3 : x' ^ 3 = 1 := by
    apply iotaA_injective P
    rw [map_pow, map_one]
    exact hx3
  have hx'1 : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨g, y, hg⟩ := sl2_three_conj_subfield (fixSubfield σ) x' hx'3 hx'1
  refine ⟨iotaA P g, ?_, ?_⟩
  · rw [← iotaA_range P]
    exact ⟨g, rfl⟩
  · rw [← map_mul, ← map_inv, ← map_mul, hg]
    exact (mem_A0sub_iff P).mpr ⟨y, rfl⟩

theorem exists_conj_Asub (P : D4Par n X σ) {x y : C0 σ} (hx : x ∈ Asub σ) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy : y ∈ Asub σ) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ g ∈ Asub σ, g * x * g⁻¹ = y := by
  haveI := P.charP
  have h2 : (2 : X) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : X) ≠ 0 := by
    intro h
    exact one_ne_zero (α := X) (by linear_combination h - h2)
  rw [← iotaA_range P] at hx hy
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  have hx'3 : x' ^ 3 = 1 := by
    apply iotaA_injective P
    rw [map_pow, map_one]
    exact hx3
  have hy'3 : y' ^ 3 = 1 := by
    apply iotaA_injective P
    rw [map_pow, map_one]
    exact hy3
  have hx'1 : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy'1 : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
  obtain ⟨g, hg⟩ := Item1118Res3Proof.exists_conj_of_pow_three h3 hx'3 hx'1 hy'3 hy'1
  refine ⟨iotaA P g, ?_, ?_⟩
  · rw [← iotaA_range P]
    exact ⟨g, rfl⟩
  · rw [← map_mul, ← map_inv, ← map_mul, hg]

end Model

end CFSG.RankThree.PartTwo.Sec19
