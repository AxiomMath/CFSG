module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpOdd
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

theorem isPGroup_two_center_fiveReflectionGroup {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    IsPGroup 2 (Subgroup.center (fiveReflectionGroup k ε π)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rcases (mem_center_fiveReflectionGroup_iff hk ε π
      (g : fiveReflectionGroup k ε π)).mp g.2 with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, neg_mul_neg, one_mul]
  simpa using h2

theorem orderOf_mk_fiveProjective_of_odd {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {g : fiveReflectionGroup k ε π} (hg : Odd (orderOf g)) :
    orderOf (QuotientGroup.mk g : fiveProjective k ε π) = orderOf g :=
  CFSG.EvenSporadicStandard.HNRecog.CSide.cSide_orderOf_mk_of_odd
    (isPGroup_two_center_fiveReflectionGroup hk ε π) hg

theorem fiveForm_sub_smul_left_eq_zero (n : ℕ) (ε : Bool) {a : Fin (n + 1) → ZMod 5}
    (ha : fiveForm n ε a a ≠ 0) (v : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (v - (fiveForm n ε v a * (fiveForm n ε a a)⁻¹) • a) a = 0 := by
  rw [fiveForm_sub_left, fiveForm_smul_left]
  rw [mul_assoc, inv_mul_cancel₀ ha, mul_one, sub_self]

private theorem zmod5_sq_mul (x y : ZMod 5) (h : IsSquare x ↔ IsSquare y) :
    IsSquare (x * y) := by
  revert x y
  decide

private theorem zmod5_sq_eq_neg (x y : ZMod 5) (hx : x ≠ 0) (hy : y ≠ 0)
    (hsx : IsSquare x) (hsy : IsSquare y) (hne : x ≠ y) : x = -y := by
  revert x y
  decide

private theorem zmod5_sq_two (q : ZMod 5) (hq : q ≠ 0) (π : Bool)
    (hπ : IsSquare q ↔ π = true) : IsSquare (2 * q) ↔ π = false := by
  revert q π
  decide

private theorem zmod5_proj_ne (qa qv b : ZMod 5) (hqa : qa ≠ 0)
    (hne : b ^ 2 ≠ qa * qv) : qv - b ^ 2 * qa⁻¹ ≠ 0 := by
  intro h
  apply hne
  have h1 : qv * qa = b ^ 2 := by
    rw [sub_eq_zero.mp h, mul_assoc, inv_mul_cancel₀ hqa, mul_one]
  rw [mul_comm] at h1
  exact h1.symm

private theorem zmod5_proj_eq_two (qa qv b : ZMod 5) (hqa : qa ≠ 0)
    (hb : b ^ 2 = -(qa * qv)) : qv - b ^ 2 * qa⁻¹ = 2 * qv := by
  rw [hb]
  field_simp [hqa]
  ring

theorem fiveForm_orthComp_clause (n : ℕ) (ε π : Bool) {a v w : Fin (n + 1) → ZMod 5}
    (ha : fiveForm n ε a a ≠ 0) (haπ : IsSquare (fiveForm n ε a a) ↔ π = true)
    (hv : fiveForm n ε v v ≠ 0) (hvπ : IsSquare (fiveForm n ε v v) ↔ π = true)
    (hav : fiveForm n ε a v ≠ 0) (hva : ∀ μ : ZMod 5, v ≠ μ • a)
    (hw : w = v - (fiveForm n ε v a * (fiveForm n ε a a)⁻¹) • a) :
    if orderOf (fiveReflOf n ε a * fiveReflOf n ε v) = 5 then fiveForm n ε w w = 0
    else fiveForm n ε w w ≠ 0 ∧ (IsSquare (fiveForm n ε w w) ↔ π = false) := by
  have hQw : fiveForm n ε w w =
      fiveForm n ε v v - (fiveForm n ε v a) ^ 2 * (fiveForm n ε a a)⁻¹ := by
    rw [hw]
    simp only [fiveForm_sub_left, fiveForm_sub_right, fiveForm_smul_left,
      fiveForm_smul_right]
    rw [fiveForm_comm n ε a v]
    field_simp [ha]
    ring
  have hβ : fiveForm n ε v a ≠ 0 := by
    rw [fiveForm_comm n ε v a]
    exact hav
  have hord := orderOf_fiveReflOf_mul n ε π ha haπ hv hvπ hva
  rw [if_neg hav] at hord
  by_cases hsq : fiveForm n ε a v ^ 2 = fiveForm n ε a a * fiveForm n ε v v
  · have hsq' : (fiveForm n ε v a) ^ 2 = fiveForm n ε a a * fiveForm n ε v v := by
      rw [fiveForm_comm n ε v a]
      exact hsq
    have ho5 : orderOf (fiveReflOf n ε a * fiveReflOf n ε v) = 5 := by
      rw [hord, if_pos hsq]
    rw [if_pos ho5, hQw, hsq']
    field_simp [ha]
    ring
  · have ho3 : orderOf (fiveReflOf n ε a * fiveReflOf n ε v) = 3 := by
      rw [hord, if_neg hsq]
    have hβ2 : (fiveForm n ε v a) ^ 2 ≠ fiveForm n ε a a * fiveForm n ε v v := by
      rw [fiveForm_comm n ε v a]
      exact hsq
    rw [if_neg (by rw [ho3]; norm_num), hQw]
    refine ⟨zmod5_proj_ne _ _ _ ha hβ2, ?_⟩
    have hsqb : IsSquare ((fiveForm n ε v a) ^ 2) := ⟨_, by ring⟩
    have hsqp : IsSquare (fiveForm n ε a a * fiveForm n ε v v) :=
      zmod5_sq_mul _ _ (haπ.trans hvπ.symm)
    have hβ2eq : (fiveForm n ε v a) ^ 2 = -(fiveForm n ε a a * fiveForm n ε v v) :=
      zmod5_sq_eq_neg _ _ (pow_ne_zero 2 hβ) (mul_ne_zero ha hv) hsqb hsqp hβ2
    rw [zmod5_proj_eq_two _ _ _ ha hβ2eq]
    exact zmod5_sq_two _ hv π hvπ

private theorem fiveForm_self_ne_zero_of_not_commute {k : ℕ} {ε π : Bool}
    {a : Fin (k + 1) → ZMod 5} {ra : fiveReflectionGroup k ε π}
    (hra : (ra : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a)
    {s : fiveProjective k ε π} (hsa : ¬ Commute s (QuotientGroup.mk ra)) :
    fiveForm k ε a a ≠ 0 := by
  intro ha0
  have hrefl1 : fiveReflOf k ε a = 1 := by
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [fiveReflOf_mulVec]
    simp only [ha0, _root_.inv_zero, mul_zero, zero_smul, sub_zero]
    funext j
    simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
  have hra1 : ra = 1 := by
    apply Subtype.ext
    rw [hra, hrefl1, Subgroup.coe_one]
  have hmk : (QuotientGroup.mk ra : fiveProjective k ε π) = 1 := by
    rw [hra1]
    rfl
  exact hsa (by rw [hmk]; exact Commute.one_right _)

private theorem exists_fiveForm_ne_zero_and_not_smul {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {a : Fin (k + 1) → ZMod 5} {ra : fiveReflectionGroup k ε π}
    (ha : fiveForm k ε a a ≠ 0) (haπ : IsSquare (fiveForm k ε a a) ↔ π = true)
    (hra : (ra : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a)
    {rv : fiveReflectionGroup k ε π} (hrv : (rv : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hcomm : ¬ Commute (QuotientGroup.mk rv : fiveProjective k ε π) (QuotientGroup.mk ra)) :
    ∃ v, fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ π = true) ∧
      (rv : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε v ∧
      fiveForm k ε a v ≠ 0 ∧ ∀ μ : ZMod 5, v ≠ μ • a := by
  obtain ⟨v, hv, hvπ, hrv_eq⟩ := exists_eq_fiveReflOf hrv
  have hra_mem : (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
    rw [hra]
    exact fiveReflOf_mem ha haπ
  have hcomm_R : ¬ Commute rv ra :=
    fun h => hcomm ((commute_mk_iff_commute hk ε π hra_mem).mpr h)
  have hcomm_GL : ¬ Commute (fiveReflOf k ε a) (fiveReflOf k ε v) := by
    intro h
    rw [← hra, ← hrv_eq] at h
    exact hcomm_R (Submonoid.commute_coe_coe.mp h).symm
  have hnot : ¬ (fiveForm k ε a v = 0 ∨ ∃ μ : ZMod 5, v = μ • a) :=
    fun h => hcomm_GL ((commute_fiveReflOf_iff k ε ha hv).mpr h)
  exact ⟨v, hv, hvπ, hrv_eq, fun h => hnot (Or.inl h), fun μ h => hnot (Or.inr ⟨μ, h⟩)⟩

private theorem exists_fiveForm_eq_zero_of_commute_mk_ra {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {a : Fin (k + 1) → ZMod 5} {ra : fiveReflectionGroup k ε π}
    (ha : fiveForm k ε a a ≠ 0)
    (hra : (ra : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a)
    (hra_mem : (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    {r : fiveReflectionGroup k ε π} (hr : (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hcomm : Commute (QuotientGroup.mk r : fiveProjective k ε π) (QuotientGroup.mk ra))
    (hne : (QuotientGroup.mk r : fiveProjective k ε π) ≠ QuotientGroup.mk ra) :
    ∃ u, fiveForm k ε u u ≠ 0 ∧ (r : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε u ∧
      fiveForm k ε u a = 0 := by
  obtain ⟨u, hu, -, hr_eq⟩ := exists_eq_fiveReflOf hr
  have hcomm_ra_R : Commute r ra :=
    (commute_mk_iff_commute hk ε π hra_mem).mp hcomm
  have hcomm_GL_ua : Commute (fiveReflOf k ε u) (fiveReflOf k ε a) := by
    simpa only [← hr_eq, ← hra] using
      (Submonoid.commute_coe_coe (s := fiveReflectionGroup k ε π) (x := r) (y := ra)).mpr
        hcomm_ra_R
  have hPQ : fiveForm k ε u a = 0 ∨ ∃ μ : ZMod 5, a = μ • u :=
    (commute_fiveReflOf_iff k ε hu ha).mp hcomm_GL_ua
  refine ⟨u, hu, hr_eq, ?_⟩
  rcases hPQ with h | ⟨μ, hμ⟩
  · exact h
  · exfalso
    have hμ0 : μ ≠ 0 := by
      intro hμzero
      apply ha
      rw [hμ, hμzero, zero_smul]
      simp [fiveForm]
    have hra_eq : fiveReflOf k ε a = fiveReflOf k ε u := by
      rw [hμ, fiveReflOf_smul k ε u hμ0]
    have hreq : r = ra := by
      apply Subtype.ext
      rw [hr_eq, hra, hra_eq]
    exact hne (by rw [hreq])

private theorem commute_mk_iff_mulVec_of_form_eq_zero {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {a v w : Fin (k + 1) → ZMod 5} {rv : fiveReflectionGroup k ε π}
    {r : fiveReflectionGroup k ε π} {u : Fin (k + 1) → ZMod 5}
    (hu : fiveForm k ε u u ≠ 0) (hv : fiveForm k ε v v ≠ 0)
    (hav : fiveForm k ε a v ≠ 0)
    (hrv_mem : (rv : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hrv_eq : (rv : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε v)
    (hr_eq : (r : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε u)
    (hua : fiveForm k ε u a = 0)
    (hw : w = v - (fiveForm k ε v a * (fiveForm k ε a a)⁻¹) • a) :
    Commute (QuotientGroup.mk r : fiveProjective k ε π) (QuotientGroup.mk rv) ↔
      ((r : GL (Fin (k + 1)) (ZMod 5)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w =
        w := by
  have hcomm_GL_uv : Commute r rv ↔ Commute (fiveReflOf k ε u) (fiveReflOf k ε v) :=
    (Submonoid.commute_coe_coe (s := fiveReflectionGroup k ε π) (x := r) (y := rv)).symm.trans
      (by rw [hr_eq, hrv_eq])
  have hnot_v : ¬ ∃ μ : ZMod 5, v = μ • u := by
    rintro ⟨μ, hμ⟩
    apply hav
    rw [hμ, fiveForm_smul_right, fiveForm_comm k ε a u, hua, mul_zero]
  have hcomm_iff_B : Commute (QuotientGroup.mk r : fiveProjective k ε π)
      (QuotientGroup.mk rv) ↔ fiveForm k ε u v = 0 := by
    rw [commute_mk_iff_commute hk ε π hrv_mem, hcomm_GL_uv,
      commute_fiveReflOf_iff k ε hu hv, or_iff_left hnot_v]
  have huw : fiveForm k ε u v = fiveForm k ε u w := by
    rw [hw, fiveForm_sub_right, fiveForm_smul_right, hua, mul_zero, sub_zero]
  have hfix : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w ↔
      fiveForm k ε u w = 0 := by
    rw [fiveReflOf_mulVec_eq_self_iff hu, fiveForm_comm k ε w u]
  rw [hcomm_iff_B, huw, hr_eq]
  exact hfix.symm

theorem exists_hyperplane_vector_proj {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {a : Fin (k + 1) → ZMod 5} (haπ : IsSquare (fiveForm k ε a a) ↔ π = true)
    {ra : fiveReflectionGroup k ε π} (hra : (ra : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a)
    {s : fiveProjective k ε π} (hs : s ∈ fiveProjClass k ε π)
    (hsa : ¬ Commute s (QuotientGroup.mk ra)) :
    ∃ w : Fin (k + 1) → ZMod 5, w ≠ 0 ∧ fiveForm k ε w a = 0 ∧
      (if orderOf ((QuotientGroup.mk ra : fiveProjective k ε π) * s) = 5 then fiveForm k ε w w = 0
        else fiveForm k ε w w ≠ 0 ∧ (IsSquare (fiveForm k ε w w) ↔ π = false)) ∧
      ∀ r : fiveReflectionGroup k ε π, (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π →
        Commute (QuotientGroup.mk r : fiveProjective k ε π) (QuotientGroup.mk ra) →
        (QuotientGroup.mk r : fiveProjective k ε π) ≠ QuotientGroup.mk ra →
        (Commute (QuotientGroup.mk r : fiveProjective k ε π) s ↔
          ((r : GL (Fin (k + 1)) (ZMod 5)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w =
            w) := by
  simp only [fiveProjClass, Set.mem_setOf_eq] at hs
  obtain ⟨rv, hrv, hsv⟩ := hs
  subst s
  have ha : fiveForm k ε a a ≠ 0 := fiveForm_self_ne_zero_of_not_commute hra hsa
  have hra_mem : (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
    rw [hra]
    exact fiveReflOf_mem ha haπ
  obtain ⟨v, hv, hvπ, hrv_eq, hav, hva⟩ :=
    exists_fiveForm_ne_zero_and_not_smul hk ha haπ hra hrv hsa
  let c : ZMod 5 := fiveForm k ε v a * (fiveForm k ε a a)⁻¹
  let w : Fin (k + 1) → ZMod 5 := v - c • a
  have hw0 : w ≠ 0 := by
    intro hwzero
    exact hva c (sub_eq_zero.mp (by simpa [w] using hwzero))
  have hwa : fiveForm k ε w a = 0 := by
    simpa [w, c] using fiveForm_sub_smul_left_eq_zero k ε ha v
  have hcoe_order : orderOf (ra * rv) = orderOf (fiveReflOf k ε a * fiveReflOf k ε v) := by
    rw [← Subgroup.orderOf_coe (ra * rv)]
    congr 1
    rw [Subgroup.coe_mul, hra, hrv_eq]
  have hodd_rv : Odd (orderOf (ra * rv)) := by
    have hord := orderOf_fiveReflOf_mul k ε π ha haπ hv hvπ hva
    rw [if_neg hav] at hord
    rw [hcoe_order, hord]
    split_ifs <;> decide
  have hordeq : orderOf ((QuotientGroup.mk ra : fiveProjective k ε π) * QuotientGroup.mk rv) =
      orderOf (fiveReflOf k ε a * fiveReflOf k ε v) := by
    rw [← QuotientGroup.mk_mul, orderOf_mk_fiveProjective_of_odd hk hodd_rv, hcoe_order]
  have hclause := fiveForm_orthComp_clause k ε π ha haπ hv hvπ hav hva (w := w) (hw := by rfl)
  refine ⟨w, hw0, hwa, ?_, ?_⟩
  · rw [hordeq]
    exact hclause
  · intro r hr hcomm hne
    obtain ⟨u, hu, hr_eq, hua⟩ :=
      exists_fiveForm_eq_zero_of_commute_mk_ra hk ha hra hra_mem hr hcomm hne
    exact commute_mk_iff_mulVec_of_form_eq_zero hk hu hv hav hrv hrv_eq hr_eq hua
      (w := w) (hw := by rfl)

end CFSG.OddTranspositions.PartThree

end
