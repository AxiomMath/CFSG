module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerCommA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfInnerCommB_commute_slOn_of_disjoint
    {N : ℕ} {S T : Set (Fin N)} (hd : Disjoint S T) :
    ∀ {x y : SpecialLinearGroup (Fin N) F2}, x ∈ slOn N S → y ∈ slOn N T → Commute x y := by
  intro x y hx hy
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, b, hab, c, ha, hb, rfl⟩
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
          rcases hy with ⟨e, f, hef, d, he, hf, rfl⟩
          exact commute_transvection_of_ne hab hef
            (fun hbe => (Set.disjoint_left.mp hd) hb (by rw [hbe]; exact he))
            (fun haf => (Set.disjoint_left.mp hd) ha (by rw [haf]; exact hf))
            c d
      | one => exact Commute.one_right _
      | mul y z _ _ hyz hyw => exact hyz.mul_right hyw
      | inv y _ hy => exact hy.inv_right
  | one => exact Commute.one_left y
  | mul x z _ _ hx hz => exact hx.mul_left hz
  | inv x _ hx => exact hx.inv_left

private theorem ggHalfInnerCommB_slOn_two_le_eq_sup (m : ℕ) (hm : 3 ≤ m) :
    slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} ⊔
        slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val = m ∨ i.val = m + 1} ⊔
          slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | m + 1 ≤ i.val} := by
  have h1 : ({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} ∩
      {i : Fin (m + 1 + 1 + 1) | i.val = m ∨ i.val = m + 1}).Nonempty := by
    refine ⟨⟨m, by omega⟩, ?_, ?_⟩
    · show 2 ≤ m ∧ m ≤ m
      omega
    · left; rfl
  have h2 : (({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} ∪
      {i : Fin (m + 1 + 1 + 1) | i.val = m ∨ i.val = m + 1}) ∩
      {i : Fin (m + 1 + 1 + 1) | m + 1 ≤ i.val}).Nonempty := by
    refine ⟨⟨m + 1, by omega⟩, ?_, ?_⟩
    · show (2 ≤ m + 1 ∧ m + 1 ≤ m) ∨ (m + 1 = m ∨ m + 1 = m + 1)
      omega
    · show m + 1 ≤ m + 1
      exact le_rfl
  rw [slOn_sup_of_inter h1, slOn_sup_of_inter h2]
  congr 1
  ext i
  simp only [Set.mem_union, Set.mem_setOf_eq]
  omega

private theorem ggHalfInnerCommB_tauPermInv_image_subset (m : ℕ) :
    ((tauPerm m)⁻¹ : Equiv.Perm (Fin (m + 1 + 1 + 1))) '' {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} ⊆
      {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
  rintro i ⟨j, hj, rfl⟩
  simp only [Set.mem_setOf_eq] at hj ⊢
  have hτ : tauPerm m ((tauPerm m)⁻¹ j) = j := Equiv.apply_symm_apply _ _
  have hne0 : (tauPerm m)⁻¹ j ≠ (0 : Fin (m + 1 + 1 + 1)) := by
    intro h
    have hj' : j = (Fin.last (m + 1)).castSucc := by rw [← hτ, h, tauPerm_apply_zero]
    have hval := congrArg Fin.val hj'
    simp only [Fin.val_last, Fin.val_castSucc] at hval
    omega
  have hne1 : (tauPerm m)⁻¹ j ≠ (1 : Fin (m + 1 + 1 + 1)) := by
    intro h
    have hj' : j = Fin.last (m + 1 + 1) := by rw [← hτ, h, tauPerm_apply_one]
    have hval := congrArg Fin.val hj'
    simp only [Fin.val_last] at hval
    omega
  have hv0 : ((tauPerm m)⁻¹ j).val ≠ 0 := by
    intro hv
    exact hne0 (Fin.ext (by rw [hv, Fin.val_zero]))
  have hv1 : ((tauPerm m)⁻¹ j).val ≠ 1 := by
    intro hv
    exact hne1 (Fin.ext (by rw [hv, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (show (1 : ℕ) < m + 1 + 1 + 1 by omega)]))
  have hlt := ((tauPerm m)⁻¹ j).isLt
  omega

theorem conj_slOn_lt_four_comm_J {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hK1 : GGHalfNormSL014 φ₁ φ₂) :
    ∀ b ∈ slOn (m + 1 + 1 + 1) {i | i.val < 4}, ∀ j ∈ J,
      (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹) * j = j * (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹) := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hcomm : ∀ b ∈ slOn (m + 1 + 1 + 1) {i | i.val < 4},
      ∀ u ∈ slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val},
        φ₁ b * φ₂ u = φ₂ u * φ₁ b := by
    intro b hb u hu
    have hle : slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} ≤
        (Subgroup.centralizer ((slOn (m + 1 + 1 + 1)
          {i : Fin (m + 1 + 1 + 1) | i.val < 4}).map φ₁ : Set G)).comap φ₂ := by
      rw [ggHalfInnerCommB_slOn_two_le_eq_sup m hm]
      refine sup_le (sup_le ?_ ?_) ?_
      ·
        intro u hu
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hw
        have hSlow_eq : slOn (m + 1 + 1 + 1)
            {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} =
            (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val ∧ j.val ≤ m}).map
              (slUpper2Hom m) := by
          rw [slUpper2Hom_map_slOn]
          congr 1
          ext i
          simp only [Set.mem_image, Set.mem_setOf_eq]
          constructor
          · rintro ⟨hi2, him⟩
            exact ⟨⟨i.val, by have := i.isLt; omega⟩, ⟨by simpa using hi2, by simpa using him⟩,
              Fin.ext (by simp only [Fin.val_castSucc])⟩
          · rintro ⟨j, ⟨hj2, hjm⟩, rfl⟩
            simpa only [Fin.val_castSucc] using ⟨hj2, hjm⟩
        have hu' : u ∈ (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val ∧ j.val ≤ m}).map
            (slUpper2Hom m) := by
          rw [← hSlow_eq]
          exact hu
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu'
        have hagree : φ₁ (slLower2Hom m y) = φ₂ (slUpper2Hom m y) :=
          DFunLike.congr_fun h.coords.agree y
        have hlow : slLower2Hom m y ∈
            slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 4 ≤ i.val} := by
          have h1 : slLower2Hom m y ∈
              (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val ∧ j.val ≤ m}).map
                (slLower2Hom m) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
          rw [slLower2Hom_map_slOn] at h1
          refine slOn_mono ?_ h1
          rintro i ⟨j, ⟨hj2, hjm⟩, rfl⟩
          simp only [Set.mem_setOf_eq] at hj2 hjm ⊢
          simp only [Fin.val_succ]
          omega
        have hdisj : Disjoint ({i : Fin (m + 1 + 1 + 1) | 4 ≤ i.val} :
            Set (Fin (m + 1 + 1 + 1))) {i : Fin (m + 1 + 1 + 1) | i.val < 4} := by
          rw [Set.disjoint_left]
          intro i hi1 hi2
          simp only [Set.mem_setOf_eq] at hi1 hi2
          omega
        have hcommSL : slLower2Hom m y * b' = b' * slLower2Hom m y :=
          (ggHalfInnerCommB_commute_slOn_of_disjoint hdisj hlow hb').eq
        rw [← hagree, ← map_mul, ← map_mul, hcommSL]
      ·
        intro u hu
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hw
        exact (h.slOn_mid_pair_comm hK1 u hu b'
          (slOn_mono (by intro i hi; simp only [Set.mem_setOf_eq] at hi ⊢; omega) hb')).symm
      ·
        intro u hu
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hw
        exact (h.slOn_last_pair_comm u hu (φ₁ b')
          (by rw [← h.coords.range₁]; exact MonoidHom.mem_range.mpr ⟨b', rfl⟩)).symm
    have hC : φ₂ u ∈ Subgroup.centralizer ((slOn (m + 1 + 1 + 1)
        {i : Fin (m + 1 + 1 + 1) | i.val < 4}).map φ₁ : Set G) :=
      Subgroup.mem_comap.mp (hle hu)
    exact (Subgroup.mem_centralizer_iff.mp hC) (φ₁ b) (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
  intro b hb j hj
  have hJ : J = (slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}).map φ₂ := by
    rw [← h.coords.rangeJ, h.coords.agree, MonoidHom.range_comp, range_slUpper2Hom]
  rw [hJ] at hj
  obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj
  let u : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
    (MulAut.conj (slPerm gf2_two ((tauPerm m)⁻¹))).toMonoidHom y
  have hu : u ∈ slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
    have h1 : u ∈ (slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}).map
        (MulAut.conj (slPerm gf2_two ((tauPerm m)⁻¹))).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [slOn_map_conj_slPerm] at h1
    exact slOn_mono (ggHalfInnerCommB_tauPermInv_image_subset m) h1
  have huφ : φ₂ u = (hElt φ₂)⁻¹ * φ₂ y * hElt φ₂ := by
    show φ₂ ((MulAut.conj (slPerm gf2_two ((tauPerm m)⁻¹))).toMonoidHom y) = _
    have hphi_inv : φ₂ (slPerm gf2_two ((tauPerm m)⁻¹)) = (hElt φ₂)⁻¹ := by
      rw [hElt, map_inv (slPerm gf2_two) (tauPerm m), map_inv]
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
      map_inv φ₂ (slPerm gf2_two ((tauPerm m)⁻¹)), hphi_inv, inv_inv]
  have hcu := hcomm b hb u hu
  rw [huφ, hyj] at hcu
  calc (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹) * j
      = hElt φ₂ * (φ₁ b * ((hElt φ₂)⁻¹ * j * hElt φ₂)) * (hElt φ₂)⁻¹ := by group
    _ = hElt φ₂ * (((hElt φ₂)⁻¹ * j * hElt φ₂) * φ₁ b) * (hElt φ₂)⁻¹ := by rw [hcu]
    _ = j * (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹) := by group

end GGHalfCtx

end CFSG.StandardType

end
