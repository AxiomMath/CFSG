module

public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.RankThree.PartOne

namespace TerminalDet

open Module

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

theorem det_involution (s : M ≃ₗ[K] M) (hss : s * s = 1) (h2 : (2 : K) ≠ 0) :
    LinearMap.det (s : M →ₗ[K] M) =
      (-1 : K) ^ finrank K (LinearMap.ker ((s : M →ₗ[K] M) + LinearMap.id)) := by
  have hss' : ∀ x, s (s x) = x := fun x => by
    simpa using congrArg (fun t : M ≃ₗ[K] M => t x) hss
  set P := LinearMap.ker ((s : M →ₗ[K] M) - LinearMap.id) with hP
  set Q := LinearMap.ker ((s : M →ₗ[K] M) + LinearMap.id) with hQ
  have hPmem : ∀ x, x ∈ P ↔ s x = x := fun x => by
    simp [hP, sub_eq_zero]
  have hQmem : ∀ x, x ∈ Q ↔ s x = -x := fun x => by
    simp [hQ, add_eq_zero_iff_eq_neg]
  have hcompl : IsCompl P Q := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hxP hxQ
      rw [hPmem] at hxP
      rw [hQmem] at hxQ
      have : (2 : K) • x = 0 := by
        rw [two_smul]
        calc x + x = s x + x := by rw [hxP]
          _ = -x + x := by rw [hxQ]
          _ = 0 := neg_add_cancel x
      exact (smul_eq_zero.mp this).resolve_left h2
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
      have hx : x = (2 : K)⁻¹ • (x + s x) + (2 : K)⁻¹ • (x - s x) := by
        rw [← smul_add]
        have : x + s x + (x - s x) = (2 : K) • x := by rw [two_smul]; abel
        rw [this, smul_smul, h2inv, one_smul]
      rw [hx]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [hPmem, map_smul, map_add, hss', add_comm]
      · rw [hQmem, map_smul, map_sub, hss', ← smul_neg, neg_sub]
  let e : (P × Q) ≃ₗ[K] M := Submodule.prodEquivOfIsCompl P Q hcompl
  let f : (P × Q) →ₗ[K] (P × Q) :=
    LinearMap.prodMap (LinearMap.id : P →ₗ[K] P) (-LinearMap.id : Q →ₗ[K] Q)
  have hconj : (e : (P × Q) →ₗ[K] M) ∘ₗ f ∘ₗ (e.symm : M →ₗ[K] (P × Q)) = (s : M →ₗ[K] M) := by
    ext x
    obtain ⟨⟨p, q⟩, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hp : s p = p := (hPmem p).mp p.2
    have hq : s q = -q := (hQmem q).mp q.2
    have he : ∀ (a : P) (b : Q), e (a, b) = (a : M) + b := fun a b =>
      Submodule.coe_prodEquivOfIsCompl' P Q hcompl (a, b)
    show e (f (p, q)) = s (e (p, q))
    have hf : f (p, q) = (p, -q) := by simp [f]
    rw [hf, he, he, map_add, hp, hq]
    simp
  have h1 := LinearMap.det_conj f e
  rw [hconj] at h1
  rw [h1]
  show LinearMap.det (LinearMap.prodMap (LinearMap.id : P →ₗ[K] P) (-LinearMap.id : Q →ₗ[K] Q)) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have : (-LinearMap.id : Q →ₗ[K] Q) = (-1 : K) • LinearMap.id := by
    ext x; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

omit [FiniteDimensional K M] in
theorem ker_add_id_eq_range_sub_id (s : M ≃ₗ[K] M) (hss : s * s = 1) (h2 : (2 : K) ≠ 0) :
    LinearMap.ker ((s : M →ₗ[K] M) + LinearMap.id) =
      LinearMap.range ((s : M →ₗ[K] M) - LinearMap.id) := by
  have hss' : ∀ x, s (s x) = x := fun x => by
    simpa using congrArg (fun t : M ≃ₗ[K] M => t x) hss
  ext x
  constructor
  · intro hx
    have hx' : s x = -x := by
      have := LinearMap.mem_ker.mp hx
      simpa [add_eq_zero_iff_eq_neg] using this
    refine ⟨(-(2 : K)⁻¹) • x, ?_⟩
    have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    show s ((-(2 : K)⁻¹) • x) - (-(2 : K)⁻¹) • x = x
    rw [map_smul, hx']
    simp only [smul_neg, neg_smul, neg_neg, sub_neg_eq_add]
    calc (2 : K)⁻¹ • x + (2 : K)⁻¹ • x = (2 : K)⁻¹ • ((2 : K) • x) := by
          rw [two_smul, smul_add]
      _ = x := by rw [smul_smul, h2inv, one_smul]
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      map_sub, hss']
    abel

theorem det_neg_one_of_rank_one (s : M ≃ₗ[K] M) (hss : s * s = 1) (h2 : (2 : K) ≠ 0)
    (hr : finrank K (LinearMap.range ((s : M →ₗ[K] M) - LinearMap.id)) = 1) :
    LinearEquiv.det s = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, det_involution s hss h2, ker_add_id_eq_range_sub_id s hss h2, hr,
    pow_one, Units.val_neg, Units.val_one]

omit [FiniteDimensional K M] in
theorem det_of_forall_smul (e : M ≃ₗ[K] M) (c : K) (h : ∀ x, e x = c • x) :
    ((LinearEquiv.det e : Kˣ) : K) = c ^ finrank K M := by
  have : (e : M →ₗ[K] M) = c • LinearMap.id := LinearMap.ext fun x => by simp [h]
  rw [LinearEquiv.coe_det, this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end TerminalDet

end CFSG.RankThree.PartOne
