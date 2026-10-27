module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Tri
public import CFSG.RankThree.PartOne.SEITZ2.OmegaCore

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Apply

theorem eichler_apply_perp {u m v : V} (hu : Q u = 0) (hm : polar Q u m = 0)
    (hv : polar Q v u = 0) : eichler Q u m v = v + polar Q v m • u := by
  rw [eichler_apply hu hm, hv, zero_smul, mul_zero, add_zero, add_zero, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

omit [CharP K 2] in
theorem polar_inv_apply {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x y : V) : polar Q (g⁻¹ x) y = polar Q x (g y) := by
  rw [← polar_map_of_mem hg, LinearEquiv.apply_inv_apply']

variable {F : OmegaFrame Q 1 1}

theorem rho_apply {m₀ m₁ v : V} (hm₀₀ : polar Q (F.e 0) m₀ = 0) (hm₀₁ : polar Q (F.e 1) m₀ = 0)
    (hm₁₁ : polar Q (F.e 1) m₁ = 0) (hv₀ : polar Q v (F.e 0) = 0) (hv₁ : polar Q v (F.e 1) = 0) :
    (eichler Q (F.e 0) m₀ * eichler Q (F.e 1) m₁) v =
      v + polar Q v m₀ • F.e 0 + polar Q v m₁ • F.e 1 := by
  have h1 : polar Q (v + polar Q v m₁ • F.e 1) (F.e 0) = 0 := by
    rw [polar_add_left, polar_smul_left_eq, hv₀, polar_comm Q (F.e 1) (F.e 0), F.polar_ee]
    simp
  rw [LinearEquiv.mul_apply, eichler_apply_perp (F.Q_e 1) hm₁₁ hv₁,
    eichler_apply_perp (F.Q_e 0) hm₀₀ h1, polar_add_left, polar_smul_left_eq, hm₀₁]
  simp only [mul_zero, add_zero]
  module

end Apply

section MVec

variable (F : OmegaFrame Q 1 1)

@[expose] def OmegaFrame.mVec (a b c d : K) : V :=
  a • F.e 2 + b • F.f 2 + c • F.t 0 + d • F.t 1

variable {F}

omit [CharP K 2] in
theorem OmegaFrame.polar_e2_mVec (a b c d : K) : polar Q (F.e 2) (F.mVec a b c d) = b := by
  simp [OmegaFrame.mVec, polar_add_right, F.polar_ee, F.polar_ef, F.polar_et]

omit [CharP K 2] in
theorem OmegaFrame.polar_f2_mVec (a b c d : K) : polar Q (F.f 2) (F.mVec a b c d) = a := by
  simp [OmegaFrame.mVec, polar_add_right, F.polar_ff, F.polar_fe, F.polar_ft]

theorem OmegaFrame.polar_t0_mVec (a b c d : K) : polar Q (F.t 0) (F.mVec a b c d) = d := by
  simp [OmegaFrame.mVec, polar_add_right, F.polar_te, F.polar_tf, F.polar_t, F.polar_t_self]

theorem OmegaFrame.polar_t1_mVec (a b c d : K) : polar Q (F.t 1) (F.mVec a b c d) = c := by
  have h : polar Q (F.t 1) (F.t 0) = 1 := by rw [polar_comm, F.polar_t]
  simp [OmegaFrame.mVec, polar_add_right, F.polar_te, F.polar_tf, h, F.polar_t_self]

omit [CharP K 2] in
theorem OmegaFrame.polar_e_mVec (i : Fin 3) (hi : i ≠ 2) (a b c d : K) :
    polar Q (F.e i) (F.mVec a b c d) = 0 := by
  have hi' : ¬ (i = 2) := hi
  simp [OmegaFrame.mVec, polar_add_right, F.polar_ee, F.polar_ef, F.polar_et, hi']

theorem OmegaFrame.mVec_isRat {k : Subfield K} {a b c d : K} (ha : a ∈ k) (hb : b ∈ k)
    (hc : c ∈ k) (hd : d ∈ k) : F.IsRat k (F.mVec a b c d) :=
  ((((F.isRat_e 2).smul ha).add ((F.isRat_f 2).smul hb)).add ((F.isRat_t 0).smul hc)).add
    ((F.isRat_t 1).smul hd)

end MVec

section Rho

variable {F : OmegaFrame Q 1 1} {k : Subfield K} {Rat M : Subgroup (V ≃ₗ[K] V)}

theorem exists_rho (R : RatGroupData F k Rat) {u w : V}
    (h₁ : F.BadAt k u w (F.e 2)) (h₂ : F.BadAt k u w (F.f 2)) (h₃ : F.BadAt k u w (F.t 0))
    (h₄ : F.BadAt k u w (F.t 1)) :
    ∃ ρ ∈ Rat, ρ (F.e 0) = F.e 0 ∧ ρ (F.e 1) = F.e 1 ∧
      ∀ v, (v = F.e 2 ∨ v = F.f 2 ∨ v = F.t 0 ∨ v = F.t 1) →
        polar Q u (ρ v) = 0 ∧ polar Q w (ρ v) = 0 := by
  obtain ⟨a₁, b₁, ha₁, hb₁, h₁u, h₁w⟩ := h₁
  obtain ⟨a₂, b₂, ha₂, hb₂, h₂u, h₂w⟩ := h₂
  obtain ⟨a₃, b₃, ha₃, hb₃, h₃u, h₃w⟩ := h₃
  obtain ⟨a₄, b₄, ha₄, hb₄, h₄u, h₄w⟩ := h₄
  have hm₀e : ∀ i : Fin 3, i ≠ 2 → polar Q (F.e i) (F.mVec a₂ a₁ a₄ a₃) = 0 :=
    fun i hi => F.polar_e_mVec i hi _ _ _ _
  have hm₁e : ∀ i : Fin 3, i ≠ 2 → polar Q (F.e i) (F.mVec b₂ b₁ b₄ b₃) = 0 :=
    fun i hi => F.polar_e_mVec i hi _ _ _ _
  have hrho : ∀ v, polar Q v (F.e 0) = 0 → polar Q v (F.e 1) = 0 →
      (eichler Q (F.e 0) (F.mVec a₂ a₁ a₄ a₃) * eichler Q (F.e 1) (F.mVec b₂ b₁ b₄ b₃)) v =
        v + polar Q v (F.mVec a₂ a₁ a₄ a₃) • F.e 0 + polar Q v (F.mVec b₂ b₁ b₄ b₃) • F.e 1 :=
    fun v hv₀ hv₁ =>
      rho_apply (hm₀e 0 (by decide)) (hm₀e 1 (by decide)) (hm₁e 1 (by decide)) hv₀ hv₁
  refine ⟨eichler Q (F.e 0) (F.mVec a₂ a₁ a₄ a₃) * eichler Q (F.e 1) (F.mVec b₂ b₁ b₄ b₃),
    Rat.mul_mem
      (R.eichler_mem _ _ (F.isRat_e 0) (F.mVec_isRat ha₂ ha₁ ha₄ ha₃) (F.Q_e 0)
        (hm₀e 0 (by decide)))
      (R.eichler_mem _ _ (F.isRat_e 1) (F.mVec_isRat hb₂ hb₁ hb₄ hb₃) (F.Q_e 1)
        (hm₁e 1 (by decide))), ?_, ?_, ?_⟩
  · rw [hrho _ (F.polar_ee 0 0) (F.polar_ee 0 1), hm₀e 0 (by decide)]
    have : polar Q (F.e 0) (F.mVec b₂ b₁ b₄ b₃) = 0 := hm₁e 0 (by decide)
    rw [this]
    simp
  · rw [hrho _ (F.polar_ee 1 0) (F.polar_ee 1 1), hm₀e 1 (by decide)]
    have : polar Q (F.e 1) (F.mVec b₂ b₁ b₄ b₃) = 0 := hm₁e 1 (by decide)
    rw [this]
    simp
  · rintro v (rfl | rfl | rfl | rfl)
    · obtain ⟨p0, p1, -, -⟩ := F.perpH_e2
      rw [hrho _ p0 p1, F.polar_e2_mVec, F.polar_e2_mVec, polar_comm Q u, polar_comm Q w]
      exact ⟨h₁u, h₁w⟩
    · obtain ⟨p0, p1, -, -⟩ := F.perpH_f2
      rw [hrho _ p0 p1, F.polar_f2_mVec, F.polar_f2_mVec, polar_comm Q u, polar_comm Q w]
      exact ⟨h₂u, h₂w⟩
    · obtain ⟨p0, p1, -, -⟩ := F.perpH_t 0
      rw [hrho _ p0 p1, F.polar_t0_mVec, F.polar_t0_mVec, polar_comm Q u, polar_comm Q w]
      exact ⟨h₃u, h₃w⟩
    · obtain ⟨p0, p1, -, -⟩ := F.perpH_t 1
      rw [hrho _ p0 p1, F.polar_t1_mVec, F.polar_t1_mVec, polar_comm Q u, polar_comm Q w]
      exact ⟨h₄u, h₄w⟩

theorem exists_normalized (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {u w : V} (hQu : Q u = 0)
    (hQw : Q w = 0) (huw : polar Q u w = 0) (hM : eichler Q u w ∈ M)
    (h₁ : F.BadAt k u w (F.e 2)) (h₂ : F.BadAt k u w (F.f 2)) (h₃ : F.BadAt k u w (F.t 0))
    (h₄ : F.BadAt k u w (F.t 1)) :
    ∃ u' w' : V, Q u' = 0 ∧ Q w' = 0 ∧ polar Q u' w' = 0 ∧ eichler Q u' w' ∈ M ∧
      Phi Q u' w' (F.e 0) (F.e 1) = Phi Q u w (F.e 0) (F.e 1) ∧
      ∀ v, (v = F.e 2 ∨ v = F.f 2 ∨ v = F.t 0 ∨ v = F.t 1) →
        polar Q u' v = 0 ∧ polar Q w' v = 0 := by
  obtain ⟨ρ, hρ, hρ0, hρ1, hperp⟩ := exists_rho R h₁ h₂ h₃ h₄
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hρ)
  have hρiO : ρ⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hρO
  have hfix : ∀ y x : V, ρ y = y → polar Q y (ρ⁻¹ x) = polar Q y x := fun y x hy => by
    rw [polar_comm Q y (ρ⁻¹ x), polar_inv_apply hρO, hy, polar_comm]
  refine ⟨ρ⁻¹ u, ρ⁻¹ w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_of_mem hρiO, hQu]
  · rw [map_of_mem hρiO, hQw]
  · rw [polar_map_of_mem hρiO, huw]
  · rw [← eichler_conj hρiO u w]
    exact M.mul_mem (M.mul_mem (M.inv_mem (hRM hρ)) hM) (by simpa using hRM hρ)
  · unfold Phi
    rw [hfix _ _ hρ0, hfix _ _ hρ0, hfix _ _ hρ1, hfix _ _ hρ1]
  · intro v hv
    rw [polar_inv_apply hρO, polar_inv_apply hρO]
    exact hperp v hv

end Rho

end CFSG.RankThree.PartOne.SEITZ2
