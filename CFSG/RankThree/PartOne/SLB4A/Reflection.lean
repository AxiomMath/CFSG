module

public import CFSG.LieType.BorelTits.OrthogonalEichler

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix
open scoped commutatorElement

section Refl

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_conj (Φ : QuadForm K (ι → K)) {g g' : (ι → K) →ₗ[K] (ι → K)}
    (hgg' : ∀ v, g (g' v) = v) (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (w v : ι → K) :
    g (Φ.reflect w (g' v)) = Φ.reflect (g w) v := by
  have hβ : Φ.polar.β w (g' v) = Φ.polar.β (g w) v := by
    rw [← Φ.polar_map_of_Q hg w (g' v), hgg']
  rw [Φ.reflect_apply, Φ.reflect_apply, map_sub, map_smul, hgg', hβ, hg]

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_neg (Φ : QuadForm K (ι → K)) (w : ι → K) : Φ.reflect (-w) = Φ.reflect w := by
  refine LinearMap.ext fun v => ?_
  have h1 : Φ.Q (-w) = Φ.Q w := by
    have := Φ.Q_smul (-1 : K) w
    rw [neg_one_smul, neg_one_sq, one_mul] at this
    exact this
  have h2 : Φ.polar.β (-w) v = -Φ.polar.β w v := by
    have := Φ.polar_smul_left (-1 : K) w v
    rwa [neg_one_smul, neg_one_mul] at this
  rw [Φ.reflect_apply, Φ.reflect_apply, h1, h2]
  simp [neg_div]

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_comm_of_orth (Φ : QuadForm K (ι → K)) {w w' : ι → K}
    (h : Φ.polar.β w w' = 0) (v : ι → K) :
    Φ.reflect w (Φ.reflect w' v) = Φ.reflect w' (Φ.reflect w v) := by
  have h' : Φ.polar.β w' w = 0 := by rw [Φ.polar_symm, h]
  rw [Φ.reflect_apply w (Φ.reflect w' v), Φ.reflect_apply w' (Φ.reflect w v),
    Φ.reflect_apply w' v, Φ.reflect_apply w v]
  simp only [Φ.polar.β_sub_right, Φ.polar.smul_right, h, h', mul_zero, sub_zero]
  module

variable (Φ : QuadForm K (ι → K))

@[expose] noncomputable def Rmat (w : ι → K) : Matrix ι ι K := LinearMap.toMatrix' (Φ.reflect w)

theorem Rmat_mulVec (w v : ι → K) : Rmat Φ w *ᵥ v = Φ.reflect w v :=
  LinearMap.toMatrix'_mulVec _ _

theorem Rmat_mul_self {w : ι → K} (hw : Φ.Q w ≠ 0) : Rmat Φ w * Rmat Φ w = 1 := by
  rw [Rmat, ← LinearMap.toMatrix'_comp, show Φ.reflect w ∘ₗ Φ.reflect w = LinearMap.id from
    LinearMap.ext (Φ.reflect_reflect hw), LinearMap.toMatrix'_id]

theorem Rmat_comm {w w' : ι → K} (h : Φ.polar.β w w' = 0) : Rmat Φ w * Rmat Φ w' = Rmat Φ w' * Rmat Φ w := by
  rw [Rmat, Rmat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 1
  exact LinearMap.ext (reflect_comm_of_orth Φ h)

@[expose] noncomputable def RGL {w : ι → K} (hw : Φ.Q w ≠ 0) : GL ι K :=
  ⟨Rmat Φ w, Rmat Φ w, Rmat_mul_self Φ hw, Rmat_mul_self Φ hw⟩

theorem RGL_mul_self {w : ι → K} (hw : Φ.Q w ≠ 0) : RGL Φ hw * RGL Φ hw = 1 :=
  Units.ext (Rmat_mul_self Φ hw)

theorem RGL_inv {w : ι → K} (hw : Φ.Q w ≠ 0) : (RGL Φ hw)⁻¹ = RGL Φ hw :=
  inv_eq_of_mul_eq_one_right (RGL_mul_self Φ hw)

theorem RGL_mem_orthGroup {w : ι → K} (hw : Φ.Q w ≠ 0) : RGL Φ hw ∈ orthGroup Φ.Q :=
  Subgroup.subset_closure fun v => by
    show Φ.Q (Rmat Φ w *ᵥ v) = Φ.Q v
    rw [Rmat_mulVec, Φ.Q_reflect]

theorem RGL_comm {w w' : ι → K} (hw : Φ.Q w ≠ 0) (hw' : Φ.Q w' ≠ 0) (h : Φ.polar.β w w' = 0) :
    RGL Φ hw * RGL Φ hw' = RGL Φ hw' * RGL Φ hw :=
  Units.ext (Rmat_comm Φ h)

theorem Rmat_conj {c w : ι → K} (hc : Φ.Q c ≠ 0) :
    Rmat Φ c * Rmat Φ w * Rmat Φ c = Rmat Φ (Φ.reflect c w) := by
  rw [Rmat, Rmat, Rmat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  exact reflect_conj Φ (g := Φ.reflect c) (g' := Φ.reflect c) (Φ.reflect_reflect hc) (Φ.Q_reflect c)
    w v

omit [Fintype ι] [DecidableEq ι] in
theorem Q_sub (Φ : QuadForm K (ι → K)) (w w' : ι → K) :
    Φ.Q (w - w') = Φ.Q w + Φ.Q w' - Φ.polar.β w w' := by
  rw [sub_eq_add_neg, Φ.Q_add, show -w' = (-1 : K) • w' by simp, Φ.Q_smul, Φ.polar.smul_right]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem Q_sub_add_Q_add (Φ : QuadForm K (ι → K)) (w w' : ι → K) :
    Φ.Q (w - w') + Φ.Q (w + w') = 2 * (Φ.Q w + Φ.Q w') := by
  rw [Q_sub, Φ.Q_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_sub_self (Φ : QuadForm K (ι → K)) {w w' : ι → K} (hQ : Φ.Q w' = Φ.Q w)
    (hc : Φ.Q (w - w') ≠ 0) : Φ.reflect (w - w') w = w' := by
  have hb : Φ.polar.β (w - w') w = Φ.Q (w - w') := by
    rw [Φ.polar.β_sub_left, Φ.polar_self, Φ.polar_symm w' w, Q_sub, hQ]
    ring
  rw [Φ.reflect_apply, hb, div_self hc, one_smul]
  abel

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_add_self (Φ : QuadForm K (ι → K)) {w w' : ι → K} (hQ : Φ.Q w' = Φ.Q w)
    (hc : Φ.Q (w + w') ≠ 0) : Φ.reflect (w + w') w = -w' := by
  have hb : Φ.polar.β (w + w') w = Φ.Q (w + w') := by
    rw [Φ.polar.add_left, Φ.polar_self, Φ.polar_symm w' w, Φ.Q_add, hQ]
    ring
  rw [Φ.reflect_apply, hb, div_self hc, one_smul]
  abel

theorem RGL_mul_RGL_mem_statedOmega (h2 : (2 : K) ≠ 0) {w w' : ι → K} (hw : Φ.Q w ≠ 0)
    (hw' : Φ.Q w' ≠ 0) (hQ : Φ.Q w' = Φ.Q w) : RGL Φ hw * RGL Φ hw' ∈ StatedOmega Φ.Q := by
  have key : ∀ (c : ι → K) (hc : Φ.Q c ≠ 0), Rmat Φ c * Rmat Φ w * Rmat Φ c = Rmat Φ w' →
      RGL Φ hw * RGL Φ hw' ∈ StatedOmega Φ.Q := by
    intro c hc hconj
    have h1 : RGL Φ hc * RGL Φ hw * (RGL Φ hc)⁻¹ = RGL Φ hw' := by
      rw [RGL_inv]
      exact Units.ext hconj
    have h2' : ⁅RGL Φ hc, RGL Φ hw⁆ = RGL Φ hw' * RGL Φ hw := by
      rw [commutatorElement_def, h1, RGL_inv Φ hw]
    have h3 : ⁅RGL Φ hc, RGL Φ hw⁆ ∈ StatedOmega Φ.Q :=
      Subgroup.commutator_mem_commutator (RGL_mem_orthGroup Φ hc) (RGL_mem_orthGroup Φ hw)
    rw [h2'] at h3
    have := inv_mem h3
    rwa [_root_.mul_inv_rev, RGL_inv, RGL_inv] at this
  have hsum := Q_sub_add_Q_add Φ w w'
  have h4 : (4 : K) * Φ.Q w ≠ 0 := mul_ne_zero (by
    intro h
    apply h2
    have : (2 : K) * 2 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).elim id id) hw
  by_cases hc : Φ.Q (w - w') = 0
  · have hc' : Φ.Q (w + w') ≠ 0 := by
      intro h
      rw [hc, h, zero_add, hQ] at hsum
      apply h4
      linear_combination -hsum
    refine key (w + w') hc' ?_
    rw [Rmat_conj Φ hc', reflect_add_self Φ hQ hc', Rmat, Rmat, reflect_neg]
  · refine key (w - w') hc ?_
    rw [Rmat_conj Φ hc, reflect_sub_self Φ hQ hc]

end Refl

end CFSG.RankThree.PartOne.SLB4A
