module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NineA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_exists_elem_nine_of_Z3_six_two_nine {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hLA : L ≤ A) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    (hm : E3.mParam A ≤ 2)
    {t : MulAut W} (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) {Q : Subgroup (MulAut W)} (hQA : Q ≤ A)
    (hQ : IsElemAbelian 3 Q)
    (hQ9 : 9 * Nat.card ↥(Q ⊓ centSub (commSub (⊤ : Subgroup W) L)) ≤ Nat.card ↥Q) :
    ∃ P : Subgroup (MulAut W), P ≤ A ⊓ centSub (commSub (⊤ : Subgroup W) L) ∧
      IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  classical
  obtain ⟨P, hPK, hPe, hP9⟩ :=
    s16h_e3_z3_blocks_elem_nine_centU2 hW hB hLA hL hrk hfix hO2 hm htA ht2 htr htL hQA hQ hQ9
  refine ⟨P.map (MulAut.conj x).toMonoidHom, ?_, hPe.map (MulAut.conj x).toMonoidHom, ?_⟩
  · rintro g ⟨p, hp, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · change x * p * x⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hB.mem (hPK hp).1) (A.inv_mem hB.mem)
    · rw [mem_centSub]
      intro u hu
      have hxu : x⁻¹ u ∈ commSub (⊤ : Subgroup W) L₂ :=
        (hB.swap' (x⁻¹ u)).mpr (by simpa using hu)
      calc (x * p * x⁻¹) u = x (p (x⁻¹ u)) := by simp only [MulAut.mul_apply]
        _ = x (x⁻¹ u) := by rw [mem_centSub.mp (hPK hp).2 (x⁻¹ u) hxu]
        _ = u := by simp
  · have hcard : Nat.card ↥(P.map (MulAut.conj x).toMonoidHom) = Nat.card ↥P :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    rw [hcard]
    exact hP9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
