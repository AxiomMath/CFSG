module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Span.Defs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma spUFix_pair_independent {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x y : V} (hx0 : x ≠ 0) (hy : ∀ c : F, y ≠ c • x) :
    ∀ s t : F, s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  intro s t hst
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at hst
    refine ⟨?_, ht⟩
    rcases smul_eq_zero.mp hst with h | h
    · exact h
    · exact absurd h hx0
  · have h1 : t • y = -(s • x) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hst
    have hty : y = (-(t⁻¹ * s)) • x := by
      calc y = t⁻¹ • (t • y) := (inv_smul_smul₀ ht y).symm
        _ = t⁻¹ • (-(s • x)) := by rw [h1]
        _ = -(t⁻¹ • (s • x)) := by rw [smul_neg]
        _ = -((t⁻¹ * s) • x) := by rw [smul_smul]
        _ = (-(t⁻¹ * s)) • x := by rw [neg_smul]
    exact absurd hty (hy _)

private lemma spUFix_scalar_eq_of_pair {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {ψ : V →+ V} {x y : V}
    (hxy : ∀ s t : F, s • x + t • y = 0 → s = 0 ∧ t = 0)
    {c₁ c₂ c₃ : F} (hx : ψ (ψ x) = c₁ • x) (hy : ψ (ψ y) = c₂ • y)
    (hxy3 : ψ (ψ (x + y)) = c₃ • (x + y)) : c₁ = c₃ ∧ c₂ = c₃ := by
  have h1 : ψ (ψ (x + y)) = c₁ • x + c₂ • y := by
    rw [map_add, map_add, hx, hy]
  have h2 : ψ (ψ (x + y)) = c₃ • x + c₃ • y := by
    rw [hxy3, smul_add]
  have heq : (c₁ - c₃) • x + (c₂ - c₃) • y = 0 := by
    have h : c₁ • x + c₂ • y = c₃ • x + c₃ • y := h1.symm.trans h2
    have key : (c₁ - c₃) • x + (c₂ - c₃) • y
        = (c₁ • x + c₂ • y) - (c₃ • x + c₃ • y) := by
      rw [sub_smul, sub_smul]
      abel
    rw [key, h, sub_self]
  obtain ⟨h1, h2⟩ := hxy _ _ heq
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

private lemma spUFix_eigen_const {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {ψ : V →+ V} (S : Submodule F V) (hψ2 : ∀ v ∈ S, ∃ c : F, ψ (ψ v) = c • v)
    {a u : V} (ha : a ∈ S) (hu : u ∈ S) (ha0 : a ≠ 0) (hau : ∀ c : F, u ≠ c • a)
    {lam : F} (hlam : ψ (ψ a) = lam • a) :
    ∀ v ∈ S, ψ (ψ v) = lam • v := by
  have hpair_au : ∀ s t : F, s • a + t • u = 0 → s = 0 ∧ t = 0 :=
    spUFix_pair_independent ha0 hau
  obtain ⟨cu, hcu⟩ := hψ2 u hu
  obtain ⟨cau, hcau⟩ := hψ2 (a + u) (S.add_mem ha hu)
  have hcomp := spUFix_scalar_eq_of_pair hpair_au hlam hcu hcau
  have hlam_cu : lam = cu := hcomp.1.trans hcomp.2.symm
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    simp
  · by_cases hmul : ∃ t : F, v = t • a
    · obtain ⟨t, ht⟩ := hmul
      have ht0 : t ≠ 0 := by
        intro h
        exact hv0 (ht.trans (by rw [h, zero_smul]))
      have hx0 : t • a ≠ 0 := by
        intro h
        rcases smul_eq_zero.mp h with h' | h'
        · exact ht0 h'
        · exact ha0 h'
      have hpair_tau : ∀ s r : F, s • (t • a) + r • u = 0 → s = 0 ∧ r = 0 :=
        spUFix_pair_independent hx0 (fun c hc => by
          rw [smul_smul] at hc
          exact hau (c * t) hc)
      obtain ⟨cv, hcv⟩ := hψ2 (t • a) (S.smul_mem t ha)
      obtain ⟨c3, hc3⟩ := hψ2 (t • a + u) (S.add_mem (S.smul_mem t ha) hu)
      have hcomp2 := spUFix_scalar_eq_of_pair hpair_tau hcv hcu hc3
      have hcv_cu : cv = cu := hcomp2.1.trans hcomp2.2.symm
      rw [ht, hcv, hcv_cu, hlam_cu]
    · have hv_not : ∀ c : F, v ≠ c • a := fun c hc => hmul ⟨c, hc⟩
      have hpair_av : ∀ s t : F, s • a + t • v = 0 → s = 0 ∧ t = 0 :=
        spUFix_pair_independent ha0 hv_not
      obtain ⟨cv, hcv⟩ := hψ2 v hv
      obtain ⟨c3, hc3⟩ := hψ2 (a + v) (S.add_mem ha hv)
      have hcomp3 := spUFix_scalar_eq_of_pair hpair_av hlam hcv hc3
      have hcv_lam : cv = lam := hcomp3.2.trans hcomp3.1.symm
      rw [hcv, hcv_lam]

private lemma spUFix_apply_apply_sq_eq_one {F : Type*} [Field F] (σ : F ≃+* F)
    (hσ2 : σ ^ 2 = 1) (x : F) : σ (σ x) = x := by
  have := congrArg (fun f : F ≃+* F => f x) hσ2
  simpa [pow_two] using this

private lemma spUFix_exists_apply_ne_of_ne_one {F : Type*} [Field F] (σ : F ≃+* F) (hσ1 : σ ≠ 1) :
    ∃ x : F, σ x ≠ x := by
  by_contra h
  push Not at h
  exact hσ1 (RingEquiv.ext fun x => h x)

private lemma spUFix_hilbert90 {F : Type*} [Field F] (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) {ν : F} (hν0 : ν ≠ 0) (hν : ν * σ ν = 1) :
    ∃ l : F, l ≠ 0 ∧ σ l = ν * l := by
  have hσσ := spUFix_apply_apply_sq_eq_one σ hσ2
  have hσν : σ ν = ν⁻¹ := eq_inv_of_mul_eq_one_right hν
  have key : ∀ c : F, σ (c + ν⁻¹ * σ c) = ν * (c + ν⁻¹ * σ c) := by
    intro c
    rw [map_add, map_mul, map_inv₀, hσσ, hσν, inv_inv]
    field_simp
    ring
  by_cases h1 : (1 : F) + ν⁻¹ * σ 1 = 0
  · obtain ⟨e, he⟩ := spUFix_exists_apply_ne_of_ne_one σ hσ1
    have hν1 : ν⁻¹ = -1 := by
      rw [map_one, mul_one] at h1
      exact eq_neg_of_add_eq_zero_right h1
    refine ⟨e + ν⁻¹ * σ e, ?_, key e⟩
    rw [hν1]
    intro h
    apply he
    linear_combination -h
  · exact ⟨_, h1, key 1⟩

private lemma spUFix_norm_onto {F : Type*} [Field F] [Finite F] (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) {d : F} (hd0 : d ≠ 0) (hd : σ d = d) :
    ∃ ρ : F, ρ ≠ 0 ∧ ρ * σ ρ = d := by
  have hσσ := spUFix_apply_apply_sq_eq_one σ hσ2
  let σu : Fˣ →* Fˣ := Units.map σ.toRingHom.toMonoidHom
  let ψ : Fˣ →* Fˣ := MonoidHom.mk' (fun x => x * σu x) (fun a b => by
    simp only [map_mul]
    exact mul_mul_mul_comm _ _ _ _)
  let φ : Fˣ →* Fˣ := MonoidHom.mk' (fun x => σu x * x⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hψ : ∀ x : Fˣ, ((ψ x : Fˣ) : F) = (x : F) * σ (x : F) := fun x => rfl
  have hφ : ∀ x : Fˣ, ((φ x : Fˣ) : F) = σ (x : F) * (x : F)⁻¹ := fun x => by
    show ((σu x * x⁻¹ : Fˣ) : F) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hker : ∀ x : Fˣ, x ∈ φ.ker ↔ σ (x : F) = x := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun u : Fˣ => (u : F)) h
      simp only [hφ, Units.val_one] at this
      field_simp at this
      exact this
    · intro h
      apply Units.ext
      rw [hφ, h, Units.val_one]
      exact mul_inv_cancel₀ x.ne_zero
  have hkerψ : ∀ x : Fˣ, x ∈ ψ.ker ↔ (x : F) * σ (x : F) = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa [hψ] using this
    · intro h
      exact Units.ext (by rw [hψ, h, Units.val_one])
  have h1 : φ.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hkerψ, hφ]
    rw [map_mul, map_inv₀, hσσ]
    field_simp
  have h2 : ψ.ker ≤ φ.range := by
    intro x hx
    rw [hkerψ] at hx
    obtain ⟨l, hl0, hl⟩ := spUFix_hilbert90 σ hσ1 hσ2 x.ne_zero hx
    refine ⟨Units.mk0 l hl0, ?_⟩
    apply Units.ext
    rw [hφ]
    simp only [Units.val_mk0]
    rw [hl]
    field_simp
  have h3 : ψ.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hker, hψ, map_mul, hσσ]
    exact mul_comm _ _
  have hc1 := Subgroup.card_ker_mul_card_range φ
  have hc2 := Subgroup.card_ker_mul_card_range ψ
  have heq : φ.range = ψ.ker := le_antisymm h1 h2
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hcard : Nat.card φ.ker = Nat.card ψ.range := by
    rw [heq] at hc1
    have : Nat.card ψ.ker * Nat.card φ.ker = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [mul_comm (Nat.card ψ.ker), hc1, hc2]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hrange : ψ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge h3 hcard.le
  have hdmem : Units.mk0 d hd0 ∈ φ.ker := (hker _).mpr (by simpa using hd)
  rw [← hrange] at hdmem
  obtain ⟨x, hx⟩ := hdmem
  refine ⟨x, x.ne_zero, ?_⟩
  have := congrArg (fun u : Fˣ => (u : F)) hx
  simpa [hψ] using this

theorem spUFix_exists_fixed_span {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] {σ : F ≃+* F} (hσ : σ ≠ 1) (ψ : V →+ V)
    (hψ : ∀ (c : F) (v : V), ψ (c • v) = σ c • ψ v) (hψinj : Function.Injective ψ)
    (S : Submodule F V) (hψS : ∀ v ∈ S, ψ v ∈ S) (hψ2 : ∀ v ∈ S, ∃ c : F, ψ (ψ v) = c • v)
    {a u : V} (ha : a ∈ S) (hu : u ∈ S) (ha0 : a ≠ 0) (hau : ∀ c : F, u ≠ c • a) :
    ∃ d : F, d ≠ 0 ∧ S ≤ Submodule.span F {x | x ∈ S ∧ d • ψ x = x} := by
  obtain ⟨lam, hlam⟩ := hψ2 a ha
  have hψa_ne : ψ a ≠ 0 := by
    intro h
    exact ha0 (hψinj (by rw [h, map_zero]))
  have hlam0 : lam ≠ 0 := by
    intro h
    exact hψa_ne (hψinj (by rw [hlam, h, zero_smul, map_zero]))
  have eigen : ∀ v ∈ S, ψ (ψ v) = lam • v :=
    spUFix_eigen_const S hψ2 ha hu ha0 hau hlam
  have hsigma : ∀ t : F, σ (σ t) = t := by
    intro t
    have h1 : ψ (ψ (t • a)) = (σ (σ t) * lam) • a := by
      rw [hψ t a, hψ (σ t) (ψ a), hlam, smul_smul]
    have h2 : ψ (ψ (t • a)) = (lam * t) • a := by
      rw [eigen (t • a) (S.smul_mem t ha), smul_smul]
    have he : (σ (σ t) * lam) • a = (lam * t) • a := h1.symm.trans h2
    have h3 : σ (σ t) * lam = lam * t := smul_left_injective F ha0 he
    rw [mul_comm lam t] at h3
    exact mul_right_cancel₀ hlam0 h3
  have hσ2 : σ ^ 2 = 1 := by
    apply RingEquiv.ext
    intro t
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply]
    exact hsigma t
  have hσlam : σ lam = lam := by
    have h1 : ψ (ψ (ψ a)) = lam • ψ a := eigen (ψ a) (hψS a ha)
    have h2 : ψ (ψ (ψ a)) = σ lam • ψ a := by
      rw [hlam, hψ lam a]
    have he : lam • ψ a = σ lam • ψ a := h1.symm.trans h2
    exact (smul_left_injective F hψa_ne he).symm
  let d0 : F := lam⁻¹
  have hd00 : d0 ≠ 0 := inv_ne_zero hlam0
  have hd0d : σ d0 = d0 := by
    dsimp only [d0]
    rw [map_inv₀, hσlam]
  obtain ⟨rho, hrho0, hrho⟩ := spUFix_norm_onto σ hσ hσ2 hd00 hd0d
  have hcoef : (rho * σ rho) * lam = 1 := by
    rw [hrho, inv_mul_cancel₀ hlam0]
  have hphi2 : ∀ x ∈ S, rho • ψ (rho • ψ x) = x := by
    intro x hx
    calc rho • ψ (rho • ψ x)
        = rho • (σ rho • ψ (ψ x)) := by rw [hψ rho (ψ x)]
      _ = rho • (σ rho • (lam • x)) := by rw [eigen x hx]
      _ = (rho * σ rho) • (lam • x) := by rw [smul_smul]
      _ = ((rho * σ rho) * lam) • x := by rw [smul_smul]
      _ = x := by rw [hcoef, one_smul]
  obtain ⟨theta, htheta⟩ := spUFix_exists_apply_ne_of_ne_one σ hσ
  refine ⟨rho, hrho0, fun v hv => ?_⟩
  have hx1 : v + rho • ψ v ∈ S := S.add_mem hv (S.smul_mem rho (hψS v hv))
  have hx1fix : rho • ψ (v + rho • ψ v) = v + rho • ψ v := by
    rw [map_add, smul_add, hphi2 v hv, add_comm]
  have hx2 : theta • v + rho • ψ (theta • v) ∈ S :=
    S.add_mem (S.smul_mem theta hv) (S.smul_mem rho (hψS (theta • v) (S.smul_mem theta hv)))
  have hx2fix : rho • ψ (theta • v + rho • ψ (theta • v))
      = theta • v + rho • ψ (theta • v) := by
    rw [map_add, smul_add, hphi2 (theta • v) (S.smul_mem theta hv), add_comm]
  have hrel : σ theta • (v + rho • ψ v) - (theta • v + rho • ψ (theta • v))
      = (σ theta - theta) • v := by
    rw [hψ theta v, smul_add, smul_smul, smul_smul, sub_smul, mul_comm (σ theta) rho]
    abel
  have hmem : σ theta • (v + rho • ψ v) - (theta • v + rho • ψ (theta • v))
      ∈ Submodule.span F {x | x ∈ S ∧ rho • ψ x = x} :=
    (Submodule.span F {x | x ∈ S ∧ rho • ψ x = x}).sub_mem
      ((Submodule.span F {x | x ∈ S ∧ rho • ψ x = x}).smul_mem (σ theta)
        (Submodule.subset_span ⟨hx1, hx1fix⟩))
      (Submodule.subset_span ⟨hx2, hx2fix⟩)
  rw [hrel] at hmem
  have hne : σ theta - theta ≠ 0 := by
    intro h
    exact htheta (sub_eq_zero.mp h)
  have := (Submodule.span F {x | x ∈ S ∧ rho • ψ x = x}).smul_mem
    (σ theta - theta)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  exact this

end CFSG.LocalAnalysis.WeakClosure81

end
