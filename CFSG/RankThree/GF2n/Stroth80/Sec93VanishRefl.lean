module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishRank
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

theorem exists_reflection_form {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (Q' : QuadraticForm K V) (F : V →ₗ[K] V)
    (hFQ : ∀ v, Q' (F v) = Q' v) (hFF : ∀ v, F (F v) = v) (hne : ∃ v, F v ≠ v)
    (hns : ∀ v, Q' (F v + v) = 0 → F v + v = 0) :
    ∃ c : V, Q' c ≠ 0 ∧ ∀ v, F v = v + (QuadraticMap.polar Q' v c / Q' c) • c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hVadd : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  have hVneg : ∀ v : V, -v = v := fun v => neg_eq_iff_add_eq_zero.mpr (hVadd v)
  have hle : Module.finrank K (LinearMap.range (F - LinearMap.id)) ≤ 1 :=
    rank_le_one_of_nonsingular_image (QuadraticMap.polarBilin Q') ⇑Q'
      (fun a v => by
        rw [QuadraticMap.map_smul, smul_eq_mul]
        ring)
      (fun v w => by
        rw [QuadraticMap.map_add (⇑Q') v w, QuadraticMap.polarBilin_apply_apply])
      (fun v => by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, CharTwo.two_nsmul])
      F hFQ hFF hns
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨c, hc⟩ : ∃ c : V, c = F v0 - v0 := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.mpr hv0
  have hFv0c : F v0 + v0 = c := by
    rw [hc, sub_eq_add_neg, hVneg v0]
  have hQc : Q' c ≠ 0 := by
    intro h
    have hFc : F v0 + v0 = 0 := hns v0 (by rw [hFv0c]; exact h)
    exact hc0 (hFv0c.symm.trans hFc)
  have hcmem : c ∈ LinearMap.range (F - LinearMap.id) :=
    LinearMap.mem_range.mpr ⟨v0, by rw [LinearMap.sub_apply, LinearMap.id_apply, hc]⟩
  have hsub : Submodule.span K {c} ≤ LinearMap.range (F - LinearMap.id) :=
    (Submodule.span_singleton_le_iff_mem c _).mpr hcmem
  have hrange_eq : Submodule.span K {c} = LinearMap.range (F - LinearMap.id) := by
    apply Submodule.eq_of_le_of_finrank_le hsub
    rw [finrank_span_singleton hc0]
    exact hle
  have hβ : ∀ v : V, ∃ b : K, b • c = F v - v := fun v => by
    have hmem : F v - v ∈ Submodule.span K {c} := by
      rw [hrange_eq]
      exact LinearMap.mem_range.mpr ⟨v, by rw [LinearMap.sub_apply, LinearMap.id_apply]⟩
    exact Submodule.mem_span_singleton.mp hmem
  choose β hβ using hβ
  have hFβ : ∀ v : V, F v = v + β v • c := fun v => by
    rw [hβ v]
    abel
  have hβadd : ∀ v w : V, β (v + w) = β v + β w := by
    intro v w
    have h1 : (β (v + w) - (β v + β w)) • c = 0 := by
      rw [sub_smul, add_smul, hβ (v + w), hβ v, hβ w, map_add]
      abel
    have h3 := (smul_eq_zero.mp h1).resolve_right hc0
    exact sub_eq_zero.mp h3
  have hkey : ∀ v : V, β v * (β v * Q' c + QuadraticMap.polar Q' v c) = 0 := by
    intro v
    have h1 : Q' (F v) = Q' (v + β v • c) := by rw [hFβ v]
    rw [QuadraticMap.map_add (⇑Q') v (β v • c), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, hFQ v] at h1
    simp only [smul_eq_mul] at h1
    linear_combination -h1
  have hdich : ∀ v : V, β v = 0 ∨ β v = QuadraticMap.polar Q' v c / Q' c := by
    intro v
    rcases mul_eq_zero.mp (hkey v) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [eq_div_iff hQc]
      linear_combination h - QuadraticMap.polar Q' v c * h2
  have hβv0 : β v0 ≠ 0 := by
    intro h
    apply hv0
    rw [hFβ v0, h, zero_smul, add_zero]
  have hβv0γ : β v0 = QuadraticMap.polar Q' v0 c / Q' c :=
    (hdich v0).resolve_left hβv0
  have hall : ∀ v : V, β v = QuadraticMap.polar Q' v c / Q' c := by
    intro v
    by_contra hv
    have hβ2 : β v = 0 := (hdich v).resolve_right hv
    have hsum : β (v0 + v) = β v0 := by rw [hβadd, hβ2, add_zero]
    have hsum_ne : β (v0 + v) ≠ 0 := by rw [hsum]; exact hβv0
    have hγsum : β (v0 + v) = QuadraticMap.polar Q' (v0 + v) c / Q' c :=
      (hdich (v0 + v)).resolve_left hsum_ne
    have hpolar : QuadraticMap.polar Q' (v0 + v) c / Q' c =
        QuadraticMap.polar Q' v0 c / Q' c + QuadraticMap.polar Q' v c / Q' c := by
      rw [QuadraticMap.polar_add_left, add_div]
    have hγv : QuadraticMap.polar Q' v c / Q' c = 0 := by
      linear_combination hsum - hγsum - hpolar + hβv0γ
    apply hv
    rw [hβ2, hγv]
  refine ⟨c, hQc, fun v => ?_⟩
  rw [hFβ v, hall v]

theorem polar_mulVec_mulVec_of_isometry
    {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q' : QuadraticForm K (ι → K)) (X : Subgroup (GL ι K))
    (hXiso : ∀ A ∈ X, ∀ v, Q' ((A : Matrix ι ι K) *ᵥ v) = Q' v)
    (A : GL ι K) (hA : A ∈ X) (v w : ι → K) :
    QuadraticMap.polar Q' ((A : Matrix ι ι K) *ᵥ v) ((A : Matrix ι ι K) *ᵥ w) =
      QuadraticMap.polar Q' v w := by
  unfold QuadraticMap.polar
  rw [← Matrix.mulVec_add, hXiso A hA, hXiso A hA, hXiso A hA]

theorem exists_mem_conj_reflection_apply
    {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q' : QuadraticForm K (ι → K)) (X : Subgroup (GL ι K))
    (hXiso : ∀ A ∈ X, ∀ v, Q' ((A : Matrix ι ι K) *ᵥ v) = Q' v)
    (hXtrans : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = Q' y →
      ∃ A ∈ X, (A : Matrix ι ι K) *ᵥ x = y)
    (c u a : ι → K) (hc : Q' c ≠ 0) (hu : Q' u = 0) (ha : Q' a = 0)
    (hua : QuadraticMap.polar Q' u a ≠ 0) :
    ∃ A ∈ X, ∃ μ : K, μ ≠ 0 ∧
      (A : Matrix ι ι K) *ᵥ ((fun v => v + (QuadraticMap.polar Q' v c / Q' c) • c)
        (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u)) = μ • a := by
  have hpau : QuadraticMap.polar Q' a u = QuadraticMap.polar Q' u a :=
    QuadraticMap.polar_comm Q' a u
  have hpau' : QuadraticMap.polar Q' a u ≠ 0 := by
    rw [hpau]
    exact hua
  obtain ⟨lam, hlam⟩ : ∃ lam : K, lam * QuadraticMap.polar Q' a u = Q' c :=
    ⟨Q' c / QuadraticMap.polar Q' a u, div_mul_cancel₀ (Q' c) hpau'⟩
  have hQc' : Q' (a + lam • u) = Q' c := by
    rw [QuadraticMap.map_add Q' a (lam • u), QuadraticMap.map_smul, hu, ha,
      QuadraticMap.polar_smul_right]
    simp only [smul_zero, mul_zero, zero_add, add_zero, smul_eq_mul]
    exact hlam
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero Q')
  have hc'0 : a + lam • u ≠ 0 := fun h => hc (by rw [← hQc', h, map_zero])
  obtain ⟨A, hA, hAc⟩ := hXtrans c (a + lam • u) hc0 hc'0 hQc'.symm
  have hAw : (A : Matrix ι ι K) *ᵥ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hpolw : QuadraticMap.polar Q' (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) c =
      QuadraticMap.polar Q' u a := by
    rw [← polar_mulVec_mulVec_of_isometry Q' X hXiso A hA
      (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) c, hAw, hAc, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hu]
    simp only [smul_zero, nsmul_zero, add_zero]
  have hcoef : QuadraticMap.polar Q' u a / Q' c * lam = 1 := by
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq hc, mul_comm, ← hpau]
    exact hlam
  have hu2 : u + u = 0 := by
    rw [← two_smul K u, (CharTwo.two_eq_zero : (2 : K) = 0), zero_smul]
  have hgen : ∀ x : ι → K, u + (x + u) = x := by
    intro x
    calc u + (x + u) = x + (u + u) := by abel
      _ = x := by rw [hu2, add_zero]
  refine ⟨A, hA, QuadraticMap.polar Q' u a / Q' c, div_ne_zero hua hc, ?_⟩
  dsimp only
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAw, hpolw, hAc, smul_add, smul_smul, hcoef,
    one_smul]
  exact hgen _

end CFSG.RankThree.GF2n.Stroth80
