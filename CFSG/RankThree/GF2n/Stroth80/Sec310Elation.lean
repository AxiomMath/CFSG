module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

theorem elation_form_sp {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : LinearMap.BilinForm K (ι → K)) (hβ : ∀ u : ι → K, u ≠ 0 → ∃ x, β x u ≠ 0)
    (halt : ∀ x, β x x = 0) (A : Matrix ι ι K)
    (hA : ∀ x y, β (A *ᵥ x) (A *ᵥ y) = β x y)
    {u : ι → K} (hu : u ≠ 0) (hrank : ∀ x, ∃ c : K, A *ᵥ x - x = c • u) :
    ∃ c : K, ∀ x, A *ᵥ x - x = (c * β x u) • u := by
  choose f hf using hrank
  have hAx : ∀ x, A *ᵥ x = x + f x • u := fun x => sub_eq_iff_eq_add'.mp (hf x)
  have hskew : ∀ y, β u y = -β y u := by
    intro y
    have h1 : β (u + y) (u + y) = 0 := halt (u + y)
    simp only [map_add, LinearMap.add_apply, halt u, halt y, zero_add, add_zero] at h1
    linear_combination h1
  have key : ∀ x y, f y * β x u = f x * β y u := by
    intro x y
    have h := hA x y
    rw [hAx x, hAx y] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    linear_combination h - f x * hskew y - f x * f y * halt u
  obtain ⟨y0, hy0⟩ := hβ u hu
  refine ⟨f y0 / β y0 u, fun x => ?_⟩
  have hfx : f x = f y0 / β y0 u * β x u := by
    rw [div_mul_eq_mul_div, key x y0, mul_div_assoc, div_self hy0, mul_one]
  rw [hf x, hfx]

theorem elation_form_orth {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm K (ι → K))
    (hQ : ∀ u : ι → K, u ≠ 0 → ∃ x, QuadraticMap.polar Q x u ≠ 0)
    (A : Matrix ι ι K) (hA : ∀ x, Q (A *ᵥ x) = Q x)
    {u : ι → K} (hu : u ≠ 0) (hrank : ∀ x, ∃ c : K, A *ᵥ x - x = c • u) :
    ∃ c : K, ∀ x, A *ᵥ x - x = (c * QuadraticMap.polar Q x u) • u := by
  obtain ⟨f, hf⟩ : ∃ f : (ι → K) → K, ∀ x, A *ᵥ x - x = f x • u :=
    ⟨fun x => Classical.choose (hrank x), fun x => Classical.choose_spec (hrank x)⟩
  have hfA : ∀ x, A *ᵥ x = x + f x • u := fun x =>
    (sub_eq_iff_eq_add.mp (hf x)).trans (add_comm _ _)
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have e : A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y := Matrix.mulVec_add A x y
    rw [hfA (x + y), hfA x, hfA y] at e
    have e2 : f (x + y) • u = f x • u + f y • u := by
      have h3 : x + y + f (x + y) • u = x + y + (f x • u + f y • u) := by
        rw [e]
        abel
      exact add_left_cancel h3
    have h4 : (f (x + y) - (f x + f y)) • u = 0 := by
      rw [sub_smul, add_smul]
      exact sub_eq_zero.mpr e2
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hu
  obtain ⟨g, hg⟩ : ∃ g : (ι → K) → K, ∀ x, g x = f x * Q u + QuadraticMap.polar Q x u :=
    ⟨fun x => f x * Q u + QuadraticMap.polar Q x u, fun x => rfl⟩
  have hgadd : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    rw [hg (x + y), hg x, hg y, hadd, QuadraticMap.polar_add_left]
    ring
  have hkey : ∀ x, f x * g x = 0 := by
    intro x
    have h1 := hA x
    rw [hfA x, QuadraticMap.map_add (⇑Q) x (f x • u), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right] at h1
    simp only [smul_eq_mul] at h1
    rw [hg x]
    linear_combination h1
  have hclaim : (∀ x, f x = 0) ∨ (∀ x, g x = 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ := hcon
    have h1 : g x1 = 0 := by
      rcases mul_eq_zero.mp (hkey x1) with h | h
      · exact absurd h hx1
      · exact h
    have h2 : f x2 = 0 := by
      rcases mul_eq_zero.mp (hkey x2) with h | h
      · exact h
      · exact absurd h hx2
    have h4 : f x1 * g x2 = 0 := by
      have h3 := hkey (x1 + x2)
      rw [hadd, hgadd, h1, h2] at h3
      linear_combination h3
    exact mul_ne_zero hx1 hx2 h4
  rcases hclaim with hf0 | hg0
  · refine ⟨0, fun x => ?_⟩
    rw [hf x, hf0 x]
    simp
  · have hQu : Q u ≠ 0 := by
      intro hQu0
      obtain ⟨x, hx⟩ := hQ u hu
      apply hx
      have h := hg0 x
      rw [hg x, hQu0, mul_zero, zero_add] at h
      exact h
    refine ⟨-(Q u)⁻¹, fun x => ?_⟩
    have hfx : f x = -(Q u)⁻¹ * QuadraticMap.polar Q x u := by
      have h := hg0 x
      rw [hg x] at h
      have hinv : Q u * (Q u)⁻¹ = 1 := mul_inv_cancel₀ hQu
      linear_combination (Q u)⁻¹ * h - f x * hinv
    rw [hf x, hfx]

theorem ela_core {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : LinearMap.BilinForm K (ι → K)) (h4 : 4 ≤ Fintype.card ι)
    (D : AddSubgroup (ι → K)) (hD : Nat.card D ≤ Nat.card K)
    (Γ : Set (Matrix ι ι K))
    (hΓD : ∀ A ∈ Γ, ∀ x, A *ᵥ x - x ∈ D)
    (hform : ∀ A ∈ Γ, ∀ u : ι → K, u ≠ 0 → (∀ x, ∃ c : K, A *ᵥ x - x = c • u) →
        ∃ c : K, ∀ x, A *ᵥ x - x = (c * β x u) • u)
    (hfix : ∀ x, (∀ A ∈ Γ, A *ᵥ x = x) → x ∈ D) : False := by
  by_cases hall : ∀ A ∈ Γ, ∀ x, A *ᵥ x = x
  · have htop : D = ⊤ := by
      apply eq_top_iff.mpr
      intro x _
      exact hfix x (fun A hA => hall A hA x)
    rw [htop] at hD
    have h1 : Nat.card (⊤ : AddSubgroup (ι → K)) = Nat.card (ι → K) :=
      Nat.card_congr AddSubgroup.topEquiv.toEquiv
    rw [h1, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)] at hD
    have hK : 1 < Nat.card K := Finite.one_lt_card
    have hlt : Nat.card K ^ 1 < Nat.card K ^ Fintype.card ι :=
      Nat.pow_lt_pow_right hK (by omega)
    rw [pow_one] at hlt
    exact lt_irrefl _ (lt_of_lt_of_le hlt hD)
  · have hex : ∃ A ∈ Γ, ∃ x, A *ᵥ x ≠ x := by
      by_contra hcon
      exact hall fun A hA x => Classical.byContradiction fun hx => hcon ⟨A, hA, x, hx⟩
    obtain ⟨A₀, hA₀, x₀, hx₀⟩ := hex
    obtain ⟨u, hu_def⟩ : ∃ u : ι → K, A₀ *ᵥ x₀ - x₀ = u := ⟨_, rfl⟩
    have hu : u ≠ 0 := by
      rw [← hu_def]
      exact sub_ne_zero.mpr hx₀
    have hcu : ∀ c : K, c • u ∈ D := by
      intro c
      have h := hΓD A₀ hA₀ (c • x₀)
      have e : A₀ *ᵥ (c • x₀) - c • x₀ = c • u := by
        rw [Matrix.mulVec_smul, ← smul_sub, hu_def]
      rw [e] at h
      exact h
    have hinj : Function.Injective (fun c : K => (⟨c • u, hcu c⟩ : ↥D)) := by
      intro c c' h
      have h' : c • u = c' • u := congrArg Subtype.val h
      have h0 : (c - c') • u = 0 := by
        rw [sub_smul, h', sub_self]
      rcases smul_eq_zero.mp h0 with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hu
    have hbij : Function.Bijective (fun c : K => (⟨c • u, hcu c⟩ : ↥D)) :=
      Function.Injective.bijective_of_nat_card_le hinj hD
    have hDmul : ∀ d ∈ D, ∃ c : K, d = c • u := by
      intro d hd
      obtain ⟨c, hc⟩ := hbij.2 ⟨d, hd⟩
      have h2 : c • u = d := congrArg Subtype.val hc
      exact ⟨c, h2.symm⟩
    have hker : ∀ x : ι → K, β x u = 0 → ∃ c : K, x = c • u := by
      intro x hx
      have hxD : x ∈ D := by
        apply hfix x
        intro A hA
        obtain ⟨c', hc'⟩ := hform A hA u hu (fun y => hDmul _ (hΓD A hA y))
        have h1 := hc' x
        rw [hx, mul_zero, zero_smul, sub_eq_zero] at h1
        exact h1
      exact hDmul x hxD
    have hle : LinearMap.ker (LinearMap.flip β u) ≤ Submodule.span K {u} := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.flip_apply] at hx
      obtain ⟨c, hc⟩ := hker x hx
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    have hfin := LinearMap.finrank_range_add_finrank_ker (LinearMap.flip β u)
    rw [Module.finrank_fintype_fun_eq_card] at hfin
    have hrange : Module.finrank K (LinearMap.range (LinearMap.flip β u)) ≤ 1 := by
      have h := Submodule.finrank_le (LinearMap.range (LinearMap.flip β u))
      rw [Module.finrank_self] at h
      exact h
    have hker_le : Module.finrank K (LinearMap.ker (LinearMap.flip β u)) ≤ 1 := by
      have h := Submodule.finrank_mono hle
      rw [finrank_span_singleton hu] at h
      exact h
    omega

end CFSG.RankThree.GF2n.Stroth80
