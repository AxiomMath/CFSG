module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.SixPivot
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Nine.Setup
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveChartModel

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix
open CFSG.OddTranspositions.PartFour.TableE1Five

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_fiveChart_of_mulEquiv (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {k : ℕ}
    {ε π : Bool} (θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π)
    (hθ : ∀ x, x ∈ DstarH hC ↔ (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    ∃ c : FiveChart hC (k + 1), c.b = fiveBilin k ε π ∧
      ∀ y (hy : y ∈ commSet D hC.d) (x : Fin (k + 1) → ZMod 5),
        ((θ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
          x - (2 * fiveBilin k ε π x (c.vec y)) • c.vec y := by
  classical
  let vec : G → (Fin (k + 1) → ZMod 5) := fun y =>
    if hy : y ∈ commSet D hC.d then
      Classical.choose (FiveChartModel.mem_fiveReflections_iff.mp
        ((hθ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩).mp
          (mem_DstarH_of_mem_commSet hC hα hy)))
    else 0
  have hvec : ∀ y (hy : y ∈ commSet D hC.d),
      fiveBilin k ε π (vec y) (vec y) = 1 ∧
      refl (fiveBilin k ε π) (vec y) =
        (θ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ : GL (Fin (k + 1)) (ZMod 5)) := by
    intro y hy
    have h := Classical.choose_spec (FiveChartModel.mem_fiveReflections_iff.mp
      ((hθ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩).mp
        (mem_DstarH_of_mem_commSet hC hα hy)))
    simpa only [vec, dif_pos hy] using h
  have heq_vec : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
      vec z' = vec z ∨ vec z' = -vec z → z' = z := by
    intro z hz z' hz' h
    have hθeq : (θ ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : GL (Fin (k + 1)) (ZMod 5)) =
        (θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : GL (Fin (k + 1)) (ZMod 5)) := by
      rw [← (hvec z' hz').2, ← (hvec z hz).2]
      rcases h with h | h
      · rw [h]
      · rw [h]; exact refl_neg (vec z)
    exact congrArg Subtype.val (θ.injective (Subtype.ext hθeq))
  have hne_of : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      vec z' ≠ vec z ∧ vec z' ≠ -vec z := fun z hz z' hz' hne =>
    ⟨fun h => hne (heq_vec z hz z' hz' (Or.inl h)).symm,
      fun h => hne (heq_vec z hz z' hz' (Or.inr h)).symm⟩
  have hcomm : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      (Commute z z' ↔ fiveBilin k ε π (vec z) (vec z') = 0) := by
    intro z hz z' hz' hne
    obtain ⟨hne1, hne2⟩ := hne_of z hz z' hz' hne
    have hnormz := (hvec z hz).1
    have hnormz' := (hvec z' hz').1
    constructor
    · intro h
      have hH : Commute (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha)
          ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ :=
        (FiveChartModel.commute_subtype_iff (H := Halpha D hC.alpha)).mp h
      have hθc : Commute (θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩)
          (θ ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) := hH.map θ
      have hGL : Commute
          ((θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : GL (Fin (k + 1)) (ZMod 5)))
          ((θ ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : GL (Fin (k + 1)) (ZMod 5))) :=
        (FiveChartModel.commute_subtype_iff (H := fiveReflectionGroup k ε π)).mpr hθc
      rw [← (hvec z hz).2, ← (hvec z' hz').2] at hGL
      exact (FiveChartModel.refl_commute_iff_of_ne (fiveBilin_comm k ε π) hnormz hnormz'
        hne1 hne2).mp hGL
    · intro h
      have hGL : Commute (refl (fiveBilin k ε π) (vec z)) (refl (fiveBilin k ε π) (vec z')) :=
        (FiveChartModel.refl_commute_iff_of_ne (fiveBilin_comm k ε π) hnormz hnormz'
          hne1 hne2).mpr h
      rw [(hvec z hz).2, (hvec z' hz').2] at hGL
      have hθc : Commute (θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩)
          (θ ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) :=
        (FiveChartModel.commute_subtype_iff (H := fiveReflectionGroup k ε π)).mp hGL
      have hH : Commute (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha)
          ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ := by
        simpa using hθc.map θ.symm
      exact (FiveChartModel.commute_subtype_iff (H := Halpha D hC.alpha)).mpr hH
  have hord : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      fiveBilin k ε π (vec z) (vec z') ≠ 0 →
      orderOf (z * z') = if fiveBilin k ε π (vec z) (vec z') ^ 2 = 1 then 5 else 3 := by
    intro z hz z' hz' hne h0
    obtain ⟨hne1, hne2⟩ := hne_of z hz z' hz' hne
    have hnormz := (hvec z hz).1
    have hnormz' := (hvec z' hz').1
    have h1 : orderOf (z * z') = orderOf
        (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
          ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : Halpha D hC.alpha) := by
      rw [← Subgroup.orderOf_coe (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
        ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : Halpha D hC.alpha), Subgroup.coe_mul]
    rw [h1, ← θ.orderOf_eq (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
        ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : Halpha D hC.alpha), map_mul]
    rw [← Subgroup.orderOf_coe (θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
        θ ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : fiveReflectionGroup k ε π), Subgroup.coe_mul]
    rw [← (hvec z hz).2, ← (hvec z' hz').2]
    exact FiveChartModel.refl_mul_refl_order (fiveBilin_comm k ε π) hnormz hnormz' hne1 hne2 h0
  have hconj : ∀ x ∈ commSet D hC.d, ∀ y ∈ commSet D hC.d,
      vec (x * y * x⁻¹) = vec y - (2 * fiveBilin k ε π (vec y) (vec x)) • vec x ∨
        vec (x * y * x⁻¹) = -(vec y - (2 * fiveBilin k ε π (vec y) (vec x)) • vec x) := by
    intro x hx y hy
    have hmem : x * y * x⁻¹ ∈ commSet D hC.d := by
      refine ⟨hC.setup.conj_mem x hy.1, ?_, ?_⟩
      · have h1 : Commute (x * y * x⁻¹) (x * hC.d * x⁻¹) :=
          hy.2.1.map (MulAut.conj x).toMonoidHom
        rwa [hx.2.1.eq, mul_inv_cancel_right] at h1
      · intro he
        apply hy.2.2
        have h1 : y = x⁻¹ * hC.d * x := by rw [← he]; group
        have h2 : x⁻¹ * hC.d * x = hC.d := by
          calc x⁻¹ * hC.d * x = x⁻¹ * (hC.d * x) := by rw [mul_assoc]
            _ = x⁻¹ * (x * hC.d) := by rw [← hx.2.1.eq]
            _ = hC.d := by group
        rw [h1, h2]
    have hθconj : (θ ⟨x * y * x⁻¹, mem_Halpha_of_mem_commSet hC hα hmem⟩ :
          GL (Fin (k + 1)) (ZMod 5)) =
        refl (fiveBilin k ε π) (vec x) * refl (fiveBilin k ε π) (vec y) *
          (refl (fiveBilin k ε π) (vec x))⁻¹ := by
      rw [show (⟨x * y * x⁻¹, mem_Halpha_of_mem_commSet hC hα hmem⟩ : Halpha D hC.alpha) =
          ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩ * ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ *
            ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← (hvec x hx).2, ← (hvec y hy).2]
    have hrefl : refl (fiveBilin k ε π) (vec (x * y * x⁻¹)) =
        refl (fiveBilin k ε π) (act (refl (fiveBilin k ε π) (vec x)) (vec y)) := by
      rw [(hvec _ hmem).2, hθconj,
        conj_refl (refl_mem_isomGroup (fiveBilin_comm k ε π) (vec x)) (vec y)]
    have hnorm : fiveBilin k ε π (act (refl (fiveBilin k ε π) (vec x)) (vec y))
        (act (refl (fiveBilin k ε π) (vec x)) (vec y)) = 1 := by
      rw [isom_norm (refl_mem_isomGroup (fiveBilin_comm k ε π) (vec x)) (vec y), (hvec y hy).1]
    have hact : act (refl (fiveBilin k ε π) (vec x)) (vec y) =
        vec y - (2 * fiveBilin k ε π (vec y) (vec x)) • vec x := by
      rw [act_refl (hvec x hx).1]
      module
    rcases (refl_eq_refl_iff (hvec _ hmem).1 hnorm).mp hrefl with h | h
    · exact Or.inl (h.symm.trans hact)
    · have hp : vec (x * y * x⁻¹) = -act (refl (fiveBilin k ε π) (vec x)) (vec y) := by
        rw [h]
        exact (neg_neg (vec (x * y * x⁻¹))).symm
      exact Or.inr (by rw [hp, hact])
  refine ⟨{ b := fiveBilin k ε π
            hsym := fiveBilin_comm k ε π
            hnd := fiveBilin_nondegenerate k ε π
            vec := vec
            norm_vec := fun z hz => (hvec z hz).1
            exists_vec := ?_
            eq_of_vec := fun z hz z' hz' => heq_vec z hz z' hz'
            commute_iff := fun z hz z' hz' => hcomm z hz z' hz'
            orderOf_mul := fun z hz z' hz' => hord z hz z' hz'
            vec_conj := hconj }, rfl, ?_⟩
  · intro v hv
    have hrefl : refl (fiveBilin k ε π) v ∈ fiveReflections k ε π :=
      FiveChartModel.refl_mem_fiveReflections hv
    have hgrp : refl (fiveBilin k ε π) v ∈ fiveReflectionGroup k ε π :=
      Subgroup.subset_closure hrefl
    let x : Halpha D hC.alpha := θ.symm ⟨refl (fiveBilin k ε π) v, hgrp⟩
    have hxθ : (θ x : GL (Fin (k + 1)) (ZMod 5)) = refl (fiveBilin k ε π) v := by
      simp [x]
    have hxmem : x ∈ DstarH hC := (hθ x).mpr (by rw [hxθ]; exact hrefl)
    have hz : (x : G) ∈ commSet D hC.d := by
      rw [← CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC hα]
      exact (mem_DstarH_iff hC).mp hxmem
    refine ⟨(x : G), hz, ?_⟩
    have hspec : refl (fiveBilin k ε π) (vec (x : G)) =
        (θ ⟨(x : G), mem_Halpha_of_mem_commSet hC hα hz⟩ : GL (Fin (k + 1)) (ZMod 5)) :=
      (hvec (x : G) hz).2
    have hxθ' : (θ ⟨(x : G), mem_Halpha_of_mem_commSet hC hα hz⟩ :
        GL (Fin (k + 1)) (ZMod 5)) = refl (fiveBilin k ε π) v := by
      have hsub : (⟨(x : G), mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) = x :=
        Subtype.ext rfl
      rw [hsub, hxθ]
    have hnorm : fiveBilin k ε π (vec (x : G)) (vec (x : G)) = 1 := (hvec (x : G) hz).1
    have heq : refl (fiveBilin k ε π) (vec (x : G)) = refl (fiveBilin k ε π) v := by
      rw [hspec, hxθ']
    rcases (refl_eq_refl_iff hnorm hv).mp heq with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h]; exact (neg_neg (vec (x : G))).symm)
  · intro y hy x
    have hv := (hvec y hy).1
    have hrefl := (hvec y hy).2
    rw [← hrefl]
    change act (refl (fiveBilin k ε π) (vec y)) x =
      x - (2 * fiveBilin k ε π x (vec y)) • vec y
    rw [act_refl hv]
    module

end CFSG.OddTranspositions.PartThree
