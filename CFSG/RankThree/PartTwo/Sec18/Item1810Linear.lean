module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open Module CFSG.RankThree.Classical

section Field

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem apply_eq_of_mem_closure_pair {t₁ t₂ : V ≃ₗ[F] V} {v w : V} {f g φ : Dual F V}
    (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g) (hv : φ v = 0)
    (hw : φ w = 0) {κ : V ≃ₗ[F] V}
    (hκ : κ ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[F] V))) (y : V) : φ (κ y) = φ y := by
  revert y
  induction hκ using Subgroup.closure_induction with
  | mem x hx =>
    intro y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [h₁.2.2.2, map_add, map_smul, hv, smul_zero, add_zero]
    · rw [h₂.2.2.2, map_add, map_smul, hw, smul_zero, add_zero]
  | one => intro y; rfl
  | mul x z _ _ ihx ihz =>
    intro y
    rw [LinearEquiv.mul_apply, ihx, ihz]
  | inv x _ ih =>
    intro y
    have hxy : x (x⁻¹ y) = y := by
      change x (x.symm y) = y
      exact x.apply_symm_apply y
    have h := ih (x⁻¹ y)
    rw [hxy] at h
    exact h.symm

theorem exists_eq_sub_of_mem_span {t : V ≃ₗ[F] V} {v : V} {f : Dual F V}
    (h : IsTransvectionWith t v f) {u : V} (hu : u ∈ Submodule.span F {v}) :
    ∃ y : V, u = t y - y := by
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : V, f y₀ ≠ 0 := by
    by_contra! hall
    exact h.2.1 (LinearMap.ext hall)
  refine ⟨(α * (f y₀)⁻¹) • y₀, ?_⟩
  have hfy : f ((α * (f y₀)⁻¹) • y₀) = α := by
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hy₀, mul_one]
  rw [h.2.2.2, hfy]
  abel

end Field

section Three

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

private theorem linearEquiv_eq_of_eqOn_isCompl {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {x y : M ≃ₗ[R] M} {P L : Submodule R M} (hPL : IsCompl P L)
    (hP : ∀ p ∈ P, x p = y p) (hL : ∀ l ∈ L, x l = y l) : x = y := by
  refine LinearEquiv.ext fun z => ?_
  have hz : z ∈ P ⊔ L := by
    rw [hPL.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add, map_add, hP p hp, hL l hl]

theorem mul_comm_of_neg_pair {t₁ t₂ z : V ≃ₗ[ZMod 3] V} {v w : V} {f g : Dual (ZMod 3) V}
    (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g) (hfw : f w ≠ 0)
    (hgv : g v ≠ 0) (hzP : ∀ p ∈ Submodule.span (ZMod 3) {v, w}, z p = -p)
    (hzL : ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g, z l = l) :
    z * t₁ = t₁ * z := by
  have hPL := isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv
  have hvP : v ∈ Submodule.span (ZMod 3) {v, w} := Submodule.subset_span (by simp)
  refine linearEquiv_eq_of_eqOn_isCompl hPL (fun p hp => ?_) (fun l hl => ?_)
  · have hT : t₁ p ∈ Submodule.span (ZMod 3) {v, w} := by
      rw [h₁.2.2.2]
      exact Submodule.add_mem _ hp (Submodule.smul_mem _ _ hvP)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hzP _ hT, hzP p hp, map_neg]
  · have hfl : f l = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1
    have htl : t₁ l = l := by
      rw [h₁.2.2.2, hfl, zero_smul, add_zero]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htl, hzL l hl, htl]

theorem mem_span_of_eigen {t₁ t₂ z τ : V ≃ₗ[ZMod 3] V} {v w u : V} {f g : Dual (ZMod 3) V}
    (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g) (hfw : f w ≠ 0)
    (hgv : g v ≠ 0) (hzP : ∀ p ∈ Submodule.span (ZMod 3) {v, w}, z p = -p)
    (hzL : ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g, z l = l)
    (hτ : τ ∈ Subgroup.zpowers t₁) (hfu : f u = 0) (hgu : g u ≠ 0) {μ : ZMod 3}
    (hμ : (τ * z) u = μ • u) : u ∈ Submodule.span (ZMod 3) {v} := by
  have hfix : ∀ σ ∈ Subgroup.zpowers t₁, ∀ x : V, f x = 0 → σ x = x := by
    intro σ hσ
    rw [Subgroup.zpowers_eq_closure] at hσ
    induction hσ using Subgroup.closure_induction with
    | mem s hs =>
      intro x hx
      rw [Set.mem_singleton_iff.mp hs, h₁.2.2.2, hx, zero_smul, add_zero]
    | one => intro x _; rfl
    | mul a b _ _ iha ihb =>
      intro x hx
      rw [LinearEquiv.mul_apply, ihb x hx, iha x hx]
    | inv a _ iha =>
      intro x hx
      have h := a.symm_apply_apply x
      rw [iha x hx] at h
      change a.symm x = x
      exact h
  have hPL := isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv
  have hdisj : Disjoint (Submodule.span (ZMod 3) {v, w})
      (LinearMap.ker f ⊓ LinearMap.ker g) := hPL.disjoint
  have hsup : u ∈ Submodule.span (ZMod 3) {v, w} ⊔ (LinearMap.ker f ⊓ LinearMap.ker g) := by
    rw [hPL.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, l, hl, hpl⟩ := Submodule.mem_sup.mp hsup
  have hfl : f l = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1
  have hgl : g l = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).2
  have hfp : f p = 0 := by
    rw [← hpl, map_add, hfl, add_zero] at hfu
    exact hfu
  have hzu : z u = -p + l := by
    rw [← hpl, map_add, hzP p hp, hzL l hl]
  have hfzu : f (z u) = 0 := by
    rw [hzu, map_add, map_neg, hfp, hfl]
    decide
  have hτzu : τ (z u) = z u := hfix τ hτ (z u) hfzu
  have hμ' : z u = μ • u := by
    rw [← hμ, LinearEquiv.mul_apply, hτzu]
  rw [hzu, ← hpl, smul_add] at hμ'
  have hab : -p - μ • p = μ • l - l := by
    calc -p - μ • p = (-p + l) - (μ • p + μ • l) + (μ • l - l) := by module
      _ = (μ • p + μ • l) - (μ • p + μ • l) + (μ • l - l) := by rw [hμ']
      _ = μ • l - l := by rw [sub_self, zero_add]
  have hA : -p - μ • p = 0 := by
    refine Submodule.disjoint_def.mp hdisj _
      (Submodule.sub_mem _ (Submodule.neg_mem _ hp) (Submodule.smul_mem _ _ hp)) ?_
    rw [hab]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hl) hl
  have hB : μ • l - l = 0 := by
    refine Submodule.disjoint_def.mp hdisj _ ?_
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hl) hl)
    rw [← hab]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hp) (Submodule.smul_mem _ _ hp)
  have hl0 : l = 0 := by
    by_contra hl0
    have h1 : (μ - 1) • l = 0 := by
      rw [sub_smul, one_smul]
      exact hB
    have hμ1 : μ = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hl0)
    rw [hμ1, one_smul] at hA
    have h3 : (3 : ZMod 3) • p = 0 := by
      rw [show (3 : ZMod 3) = 0 by decide, zero_smul]
    have hp0 : p = 0 := by
      calc p = (3 : ZMod 3) • p + (-p - p) := by module
        _ = 0 := by rw [h3, hA, zero_add]
    apply hgu
    rw [← hpl, hp0, zero_add]
    exact hgl
  rw [hl0, add_zero] at hpl
  obtain ⟨a, b, hab'⟩ := Submodule.mem_span_pair.mp hp
  have hb : b = 0 := by
    have h := hfp
    rw [← hab', map_add, map_smul, map_smul, h₁.2.2.1, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right hfw
  rw [← hpl, ← hab', hb, zero_smul, add_zero]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v)

end Three

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
