module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentCardX
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiagA5
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentPsi

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem exists_outer_psi : ∃ s : G, (s = D.a * D.w ∨ s = D.a * D.w * D.v) ∧
    ∀ x x' : SL5, psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM → s⁻¹ * D.d x * s = D.d x' := by
  have hs0X : D.a * D.w ∈ D.X :=
    mul_mem ((inf_le_left : D.T ≤ D.X) D.a_mem_T) ((inf_le_left : D.T ≤ D.X) D.w_mem_T)
  have hnorm : D.a * D.w ∈ Subgroup.normalizer (D.A : Set G) :=
    D.second_centralizer_card_and_diagonal_normal.2.1 hs0X
  have hs0inv_norm : (D.a * D.w)⁻¹ ∈ Subgroup.normalizer (D.A : Set G) := inv_mem hnorm
  have hφA : ∀ x : SL5, (D.a * D.w)⁻¹ * D.d x * (D.a * D.w) ∈ D.A := by
    intro x
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hs0inv_norm (D.d x)).mp ⟨x, rfl⟩
  let φ : SL5 →* G := (MulAut.conj (D.a * D.w)⁻¹).toMonoidHom.comp D.d
  have hφ_apply : ∀ x : SL5, φ x = (D.a * D.w)⁻¹ * D.d x * (D.a * D.w) := by
    intro x
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hφA' : ∀ x : SL5, φ x ∈ D.A := by intro x; rw [hφ_apply]; exact hφA x
  have hφ_hM : φ hM = D.d hM := by
    rw [hφ_apply]
    have hav : Commute D.a D.v := mem_centralizer_singleton_iff.mp (mem_inf.mp D.a_mem_T).2
    have hwv : Commute D.w D.v := mem_centralizer_singleton_iff.mp (mem_inf.mp D.w_mem_T).2
    have hcomm : Commute (D.a * D.w) D.v := hav.mul_left hwv
    show (D.a * D.w)⁻¹ * D.d hM * (D.a * D.w) = D.d hM
    rw [show D.d hM = D.v from rfl, mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwaw : D.w * D.a * D.w = D.b⁻¹ := by
    rw [← D.conj_w_a_and_b.1, inv_eq_of_mul_eq_one_right D.w_mul_w]
  have hwaw' : D.w * D.a⁻¹ * D.w = D.b := by
    have h : (D.w * D.a⁻¹ * D.w)⁻¹ = D.b⁻¹ := by
      rw [show (D.w * D.a⁻¹ * D.w)⁻¹ = D.w⁻¹ * D.a * D.w⁻¹ by group,
        inv_eq_of_mul_eq_one_right D.w_mul_w]
      exact hwaw
    simpa [inv_inv] using congrArg Inv.inv h
  have hφ_cM : φ cM = D.d (hM * cM) := by
    rw [hφ_apply]
    show (D.a * D.w)⁻¹ * D.d cM * (D.a * D.w) = D.d (hM * cM)
    calc (D.a * D.w)⁻¹ * D.d cM * (D.a * D.w)
        = D.w * D.a⁻¹ * D.w * D.a * D.w := by
          rw [show D.d cM = D.w from rfl,
            show (D.a * D.w)⁻¹ = D.w * D.a⁻¹ by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right D.w_mul_w]]
          noncomm_ring
      _ = D.b * D.a * D.w := by rw [hwaw']
      _ = D.a * D.b * D.w := by rw [← D.commute_a_b.eq]
      _ = D.v * D.w := by rw [D.a_mul_b]
      _ = D.d (hM * cM) := by rw [map_mul]; rfl
  have hb_inv : D.b⁻¹ = D.b * D.u * D.v := by
    apply inv_eq_of_mul_eq_one_right
    calc D.b * (D.b * D.u * D.v) = D.b * D.b * D.u * D.v := by group
      _ = (D.u * D.v) * D.u * D.v := by rw [← pow_two, D.b_sq]
      _ = 1 := by
        rw [show (D.u * D.v) * D.u * D.v = D.u * (D.v * (D.u * D.v)) by group]
        simp only [D.v_mul_u_mul, D.u_mul_u_mul, D.v_mul_v]
  have hs0_sq : (D.a * D.w) ^ 2 = D.u := by
    rw [pow_two]
    calc (D.a * D.w) * (D.a * D.w) = D.a * (D.w * D.a * D.w) := by group
      _ = D.a * D.b⁻¹ := by rw [hwaw]
      _ = D.a * (D.b * D.u * D.v) := by rw [hb_inv]
      _ = D.u := by
        rw [show D.a * (D.b * D.u * D.v) = (D.a * D.b) * D.u * D.v by group]
        rw [D.a_mul_b]
        rw [show (D.v * D.u) * D.v = D.u by
          rw [← D.commute_u_v.eq, mul_assoc, D.v_mul_v, mul_one]]
  have hd_eq : ∀ x z : SL5, D.d x = D.d z ↔ x = z ∨ x = -z := by
    intro x z
    constructor
    · intro h
      have h1 : D.d (x * z⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
      have h2 : x * z⁻¹ ∈ D.d.ker := MonoidHom.mem_ker.mpr h1
      rw [D.toSwapData.ker_d, sl5_mem_center_iff] at h2
      rcases h2 with h2 | h2
      · left
        calc x = x * z⁻¹ * z := by group
          _ = 1 * z := by rw [h2]
          _ = z := one_mul z
      · right
        calc x = x * z⁻¹ * z := by group
          _ = (-1) * z := by rw [h2]
          _ = -z := neg_one_mul z
    · rintro (rfl | rfl)
      · rfl
      · rw [D.d_neg]
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (show φ (thetaM 1) ∈ D.d.range from hφA' (thetaM 1))
  have hy1 : (y * hM) ^ 2 = 1 ∨ (y * hM) ^ 2 = -1 := by
    have hker : (y * hM) ^ 2 ∈ D.d.ker := by
      rw [MonoidHom.mem_ker]
      calc D.d ((y * hM) ^ 2) = (D.d (y * hM)) ^ 2 := by rw [map_pow]
        _ = (D.d y * D.d hM) ^ 2 := by rw [map_mul]
        _ = (φ (thetaM 1) * φ hM) ^ 2 := by rw [hy, hφ_hM]
        _ = (φ (thetaM 1 * hM)) ^ 2 := by rw [map_mul]
        _ = φ ((thetaM 1 * hM) ^ 2) := by rw [map_pow]
        _ = φ (-1) := by rw [thetaM_one_mul_hM_sq]
        _ = 1 := by rw [hφ_apply, D.d_neg, map_one, mul_one, inv_mul_cancel]
    rwa [D.toSwapData.ker_d, sl5_mem_center_iff] at hker
  have hy2 : (hM * cM * y) ^ 3 = 1 ∨ (hM * cM * y) ^ 3 = -1 := by
    have hker : (hM * cM * y) ^ 3 ∈ D.d.ker := by
      rw [MonoidHom.mem_ker]
      calc D.d ((hM * cM * y) ^ 3) = (D.d (hM * cM * y)) ^ 3 := by rw [map_pow]
        _ = (D.d (hM * cM) * D.d y) ^ 3 := by rw [map_mul]
        _ = (φ cM * φ (thetaM 1)) ^ 3 := by rw [← hφ_cM, hy]
        _ = (φ (cM * thetaM 1)) ^ 3 := by rw [map_mul]
        _ = φ ((cM * thetaM 1) ^ 3) := by rw [map_pow]
        _ = φ 1 := by rw [cM_mul_thetaM_one_cubed]
        _ = 1 := by rw [map_one]
    rwa [D.toSwapData.ker_d, sl5_mem_center_iff] at hker
  have hy3 : y ≠ hM * cM := by
    intro h
    have hφeq : φ (thetaM 1) = φ cM := by rw [← hy, h, ← hφ_cM]
    have h' : D.d (thetaM 1) = D.d cM := by
      calc D.d (thetaM 1) = (D.a * D.w) * φ (thetaM 1) * (D.a * D.w)⁻¹ := by
            rw [hφ_apply]; group
        _ = (D.a * D.w) * φ cM * (D.a * D.w)⁻¹ := by rw [hφeq]
        _ = D.d cM := by rw [hφ_apply]; group
    rcases (hd_eq (thetaM 1) cM).mp h' with h'' | h''
    · exact thetaM_one_ne_cM h''
    · exact thetaM_one_ne_neg_cM h''
  have hy4 : y ≠ -(hM * cM) := by
    intro h
    have hφeq : φ (thetaM 1) = φ cM := by rw [← hy, h, D.d_neg, ← hφ_cM]
    have h' : D.d (thetaM 1) = D.d cM := by
      calc D.d (thetaM 1) = (D.a * D.w) * φ (thetaM 1) * (D.a * D.w)⁻¹ := by
            rw [hφ_apply]; group
        _ = (D.a * D.w) * φ cM * (D.a * D.w)⁻¹ := by rw [hφeq]
        _ = D.d cM := by rw [hφ_apply]; group
    rcases (hd_eq (thetaM 1) cM).mp h' with h'' | h''
    · exact thetaM_one_ne_cM h''
    · exact thetaM_one_ne_neg_cM h''
  have hbad : ∀ k : ℕ, (k = 2 ∨ k = 3) → D.d y = D.d (thetaM k) → False := by
    intro k hk hkdy
    have hx5 : (D.d (thetaM 1)) ^ 5 = 1 := by rw [← map_pow, thetaM_one_pow_five, map_one]
    have hφeq : φ (thetaM 1) = (D.d (thetaM 1)) ^ k := by
      rw [← hy, hkdy]
      rcases hk with rfl | rfl
      · change D.d (thetaM 2) = (D.d (thetaM 1)) ^ 2
        rw [← thetaM_one_sq, map_pow]
      · change D.d (thetaM 3) = (D.d (thetaM 1)) ^ 3
        rw [← thetaM_one_cubed, map_pow]
    have hconj : (D.a * D.w)⁻¹ * D.d (thetaM 1) * (D.a * D.w) = (D.d (thetaM 1)) ^ k := by
      rw [← hφ_apply]; exact hφeq
    have h2 : ((D.a * D.w) ^ 2)⁻¹ * D.d (thetaM 1) * (D.a * D.w) ^ 2 =
        (D.d (thetaM 1)) ^ (k * k) := by
      calc ((D.a * D.w) ^ 2)⁻¹ * D.d (thetaM 1) * (D.a * D.w) ^ 2
          = (D.a * D.w)⁻¹ * ((D.a * D.w)⁻¹ * D.d (thetaM 1) * (D.a * D.w)) *
              (D.a * D.w) := by
            rw [pow_two, mul_inv_rev]
            group
        _ = (D.a * D.w)⁻¹ * (D.d (thetaM 1)) ^ k * (D.a * D.w) := by rw [hconj]
        _ = ((D.a * D.w)⁻¹ * D.d (thetaM 1) * (D.a * D.w)) ^ k := by
            have h := map_pow (MulAut.conj (D.a * D.w)⁻¹).toMonoidHom (D.d (thetaM 1)) k
            simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc] using h
        _ = ((D.d (thetaM 1)) ^ k) ^ k := by rw [hconj]
        _ = (D.d (thetaM 1)) ^ (k * k) := by rw [pow_mul]
    have hL : ((D.a * D.w) ^ 2)⁻¹ * D.d (thetaM 1) * (D.a * D.w) ^ 2 = D.d (thetaM 1) := by
      have hcomm : Commute D.u (D.d (thetaM 1)) := (D.d_commute_u (thetaM 1)).symm
      rw [hs0_sq, D.u_inv]
      rw [hcomm.eq, mul_assoc, D.u_mul_u, mul_one]
    have hx4 : D.d (thetaM 1) = (D.d (thetaM 1)) ^ 4 := by
      have hkk : (D.d (thetaM 1)) ^ (k * k) = (D.d (thetaM 1)) ^ 4 := by
        rcases hk with rfl | rfl
        · norm_num
        · rw [show 3 * 3 = 4 + 5 by norm_num, pow_add, hx5, mul_one]
      calc D.d (thetaM 1) = ((D.a * D.w) ^ 2)⁻¹ * D.d (thetaM 1) * (D.a * D.w) ^ 2 := hL.symm
        _ = (D.d (thetaM 1)) ^ (k * k) := h2
        _ = (D.d (thetaM 1)) ^ 4 := hkk
    have hx3 : (D.d (thetaM 1)) ^ 3 = 1 := by
      have h' : D.d (thetaM 1) * 1 = D.d (thetaM 1) * (D.d (thetaM 1)) ^ 3 := by
        rw [mul_one]
        nth_rewrite 1 [hx4]
        group
      exact (mul_left_cancel h').symm
    have hd3 : D.d (thetaM 3) = 1 := by
      rw [← thetaM_one_cubed, map_pow]; exact hx3
    have hker : thetaM 3 ∈ D.d.ker := MonoidHom.mem_ker.mpr hd3
    rw [D.toSwapData.ker_d, sl5_mem_center_iff] at hker
    rcases hker with h | h
    · exact thetaM_three_ne_one h
    · exact thetaM_three_ne_neg_one h
  have hy8 := eight_solutions hy1 hy2 hy3 hy4
  rcases hy8 with hyc1 | hyc1' | hyc2 | hyc2' | hyth2 | hyth2' | hyth3 | hyth3'
  · have hφ_eq : φ = D.d.comp psiConj := by
      refine MonoidHom.eq_of_eqOn_dense closure_cM_thetaM_one ?_
      intro z hz
      rcases hz with rfl | rfl
      · show φ cM = (D.d.comp psiConj) cM
        rw [hφ_cM, MonoidHom.comp_apply, psiConj_cM, D.d_neg]
      · change φ (thetaM 1) = D.d (psiConj (thetaM 1))
        rw [psiConj_thetaM_one, ← hy, hyc1]
    refine ⟨D.a * D.w, Or.inl rfl, ?_⟩
    intro x x' hxx'
    have hx' : x' = psiConj x := eq_psiConj_of_psiM_mul hxx'
    rw [hx', ← hφ_apply x, hφ_eq]
    rfl
  · have hφ_eq : φ = D.d.comp psiConj := by
      refine MonoidHom.eq_of_eqOn_dense closure_cM_thetaM_one ?_
      intro z hz
      rcases hz with rfl | rfl
      · show φ cM = (D.d.comp psiConj) cM
        rw [hφ_cM, MonoidHom.comp_apply, psiConj_cM, D.d_neg]
      · change φ (thetaM 1) = D.d (psiConj (thetaM 1))
        rw [psiConj_thetaM_one, ← hy, hyc1', D.d_neg]
    refine ⟨D.a * D.w, Or.inl rfl, ?_⟩
    intro x x' hxx'
    have hx' : x' = psiConj x := eq_psiConj_of_psiM_mul hxx'
    rw [hx', ← hφ_apply x, hφ_eq]
    rfl
  · have hφ₂_apply : ∀ x : SL5,
        ((MulAut.conj D.v⁻¹).toMonoidHom.comp φ) x = D.v⁻¹ * φ x * D.v := by
      intro x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hφ₂_eq : (MulAut.conj D.v⁻¹).toMonoidHom.comp φ = D.d.comp psiConj := by
      refine MonoidHom.eq_of_eqOn_dense closure_cM_thetaM_one ?_
      intro z hz
      rcases hz with rfl | rfl
      · show D.v⁻¹ * φ cM * (D.v⁻¹)⁻¹ = D.d (psiConj cM)
        rw [inv_inv, hφ_cM, psiConj_cM, D.d_neg]
        rw [map_mul, show D.d hM = D.v from rfl, show D.d cM = D.w from rfl,
          inv_eq_of_mul_eq_one_right D.v_mul_v]
        rw [← mul_assoc, D.v_mul_v, one_mul]
        exact D.commute_v_w.eq.symm
      · show D.v⁻¹ * φ (thetaM 1) * (D.v⁻¹)⁻¹ = D.d (psiConj (thetaM 1))
        rw [inv_inv, psiConj_thetaM_one, ← hy, hyc2]
        rw [show D.v = D.d hM from rfl, ← map_inv, ← map_mul, ← map_mul,
          hM_inv_mul_c2M_mul_hM]
    refine ⟨D.a * D.w * D.v, Or.inr rfl, ?_⟩
    intro x x' hxx'
    have hx' : x' = psiConj x := eq_psiConj_of_psiM_mul hxx'
    rw [hx']
    rw [show (D.a * D.w * D.v)⁻¹ * D.d x * (D.a * D.w * D.v) =
        D.v⁻¹ * ((D.a * D.w)⁻¹ * D.d x * (D.a * D.w)) * D.v by group]
    rw [← hφ_apply x, ← hφ₂_apply x, hφ₂_eq]
    rfl
  · have hφ₂_apply : ∀ x : SL5,
        ((MulAut.conj D.v⁻¹).toMonoidHom.comp φ) x = D.v⁻¹ * φ x * D.v := by
      intro x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hφ₂_eq : (MulAut.conj D.v⁻¹).toMonoidHom.comp φ = D.d.comp psiConj := by
      refine MonoidHom.eq_of_eqOn_dense closure_cM_thetaM_one ?_
      intro z hz
      rcases hz with rfl | rfl
      · show D.v⁻¹ * φ cM * (D.v⁻¹)⁻¹ = D.d (psiConj cM)
        rw [inv_inv, hφ_cM, psiConj_cM, D.d_neg]
        rw [map_mul, show D.d hM = D.v from rfl, show D.d cM = D.w from rfl,
          inv_eq_of_mul_eq_one_right D.v_mul_v]
        rw [← mul_assoc, D.v_mul_v, one_mul]
        exact D.commute_v_w.eq.symm
      · show D.v⁻¹ * φ (thetaM 1) * (D.v⁻¹)⁻¹ = D.d (psiConj (thetaM 1))
        rw [inv_inv, psiConj_thetaM_one, ← hy, hyc2', D.d_neg]
        rw [show D.v = D.d hM from rfl, ← map_inv, ← map_mul, ← map_mul,
          hM_inv_mul_c2M_mul_hM]
    refine ⟨D.a * D.w * D.v, Or.inr rfl, ?_⟩
    intro x x' hxx'
    have hx' : x' = psiConj x := eq_psiConj_of_psiM_mul hxx'
    rw [hx']
    rw [show (D.a * D.w * D.v)⁻¹ * D.d x * (D.a * D.w * D.v) =
        D.v⁻¹ * ((D.a * D.w)⁻¹ * D.d x * (D.a * D.w)) * D.v by group]
    rw [← hφ_apply x, ← hφ₂_apply x, hφ₂_eq]
    rfl
  · exact (hbad 2 (Or.inl rfl) (by rw [hyth2]; rfl)).elim
  · exact (hbad 2 (Or.inl rfl) (by rw [hyth2', D.d_neg]; rfl)).elim
  · exact (hbad 3 (Or.inr rfl) (by rw [hyth3]; rfl)).elim
  · exact (hbad 3 (Or.inr rfl) (by rw [hyth3', D.d_neg]; rfl)).elim

end CFSG.OddTranspositions.PartThree.Wong.SplitData
