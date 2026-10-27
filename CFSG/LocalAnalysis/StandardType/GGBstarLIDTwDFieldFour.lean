module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldSemi

public section

namespace CFSG.StandardType

namespace LIDTwDF

open Module QuadraticMap OrthBstarOdd OrthRestOdd
open scoped Polynomial

variable {K : Type} [Field K]

theorem polar_zero_of_sing {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {Y : Submodule K V} (hY : ∀ y ∈ Y, Q y = 0) : ∀ y ∈ Y, ∀ y' ∈ Y, polar Q y y' = 0 :=
  fun y hy y' hy' => by
    have h := hY (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.map_add (⇑Q), hY y hy, hY y' hy', zero_add, zero_add] at h
    exact h

section Alpha

variable [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem alpha_eq_one {p : ℕ} (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {s : V ≃ₗ[K] V}
    (hsp : s ^ p = 1) {Y : Submodule K V} (hY2 : finrank K Y = 2) (hYs : ∀ v ∈ Y, s v ∈ Y)
    {y : V} (hyY : y ∈ Y) (hind : ∀ a b : K, a • y + b • s y = 0 → a = 0 ∧ b = 0) {α β : K}
    (h2 : s (s y) = α • y + β • s y) : α = 1 := by
  classical
  let f : Y →ₗ[K] Y := (s : V →ₗ[K] V).restrict hYs
  have hfk : ∀ (k : ℕ) (v : Y), ((f ^ k) v : V) = (s ^ k) (v : V) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
      rfl
  have hfp : f ^ p = 1 := LinearMap.ext fun v => Subtype.ext (by rw [hfk, hsp]; rfl)
  have hdet : (LinearMap.det f) ^ p = 1 := by rw [← map_pow, hfp, map_one]
  have hdet1 : LinearMap.det f = 1 := hK1 _ hdet
  set y₀ : Y := ⟨y, hyY⟩ with hy₀
  set y₁ : Y := ⟨s y, hYs y hyY⟩ with hy₁
  have hli : LinearIndependent K ![y₀, y₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    apply hind a b
    have := congrArg Subtype.val hab
    simpa [y₀, y₁] using this
  let bY : Module.Basis (Fin 2) K Y :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hY2])
  have hbY0 : bY 0 = y₀ := by simp [bY]
  have hbY1 : bY 1 = y₁ := by simp [bY]
  have hfy₀ : f y₀ = y₁ := Subtype.ext rfl
  have hfy₁ : f y₁ = α • y₀ + β • y₁ := by
    apply Subtype.ext
    show s (s y) = α • y + β • s y
    exact h2
  have e00 : LinearMap.toMatrix bY bY f 0 0 = 0 := by
    rw [LinearMap.toMatrix_apply, hbY0, hfy₀, ← hbY1, Module.Basis.repr_self]
    simp
  have e10 : LinearMap.toMatrix bY bY f 1 0 = 1 := by
    rw [LinearMap.toMatrix_apply, hbY0, hfy₀, ← hbY1, Module.Basis.repr_self]
    simp
  have e01 : LinearMap.toMatrix bY bY f 0 1 = α := by
    rw [LinearMap.toMatrix_apply, hbY1, hfy₁, ← hbY0, ← hbY1, map_add, map_smul, map_smul,
      Module.Basis.repr_self, Module.Basis.repr_self]
    simp
  have e11 : LinearMap.toMatrix bY bY f 1 1 = β := by
    rw [LinearMap.toMatrix_apply, hbY1, hfy₁, ← hbY0, ← hbY1, map_add, map_smul, map_smul,
      Module.Basis.repr_self, Module.Basis.repr_self]
    simp
  have hdetM := LinearMap.det_toMatrix bY f
  rw [Matrix.det_fin_two, e00, e11, e01, e10, hdet1] at hdetM
  have h3 : -α = 1 := by linear_combination hdetM
  rw [← CharTwo.neg_eq α]
  exact h3

end Alpha

section Four

variable [Finite K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  {Q : QuadraticForm K X}

theorem exists_inv_singular_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    {σ : K ≃+* K} (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) (hX : finrank K X = 4)
    (hQ : (polarBilin Q).Nondegenerate) {E : Subgroup (X ≃ₗ[K] X)} {s : X ≃ₗ[K] X} (hsE : s ∈ E)
    (hEs : ∀ g ∈ E, ∃ k : ℕ, s ^ k = g) (hpow : ∀ g ∈ E, g ^ p = 1)
    (hQE : ∀ g ∈ E, ∀ v, Q (g v) = Q v) (hfpf : ∀ v : X, v ≠ 0 → s v ≠ v)
    (S : SemiSim Q p σ) (hSs : ∀ v, S.G (s v) = s (S.G v)) {Y : Submodule K X} (hY0 : Y ≠ ⊥)
    (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) (hYsing : ∀ y ∈ Y, Q y = 0) :
    ∃ Y' : Submodule K X, Y' ≠ ⊥ ∧ (∀ g ∈ E, ∀ y ∈ Y', g y ∈ Y') ∧
      (∀ y ∈ Y', S.G y ∈ Y') ∧ ∀ y ∈ Y', Q y = 0 := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have hsp : s ^ p = 1 := hpow s hsE
  have hsQ : ∀ v, Q (s v) = Q v := hQE s hsE
  have hc2 : ∀ w : X, w + w = 0 := fun w => by
    rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  have hYp := polar_zero_of_sing hYsing
  have hYle : Y ≤ perp Q Y := fun y hy => subset_perp hYp hy
  have hperp : finrank K (perp Q Y) = 4 - finrank K Y := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hX]
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hsy : s y ≠ y := hfpf y hy0
  have hY1 : finrank K Y ≠ 1 := fun h1 =>
    hsy (fix_of_finrank_eq_one hpow hK1 h1 hYinv hyY hy0 s hsE)
  have hYpos : 1 ≤ finrank K Y := Submodule.one_le_finrank_iff.mpr hY0
  have hYle2 : finrank K Y ≤ finrank K (perp Q Y) := Submodule.finrank_mono hYle
  have hY2 : finrank K Y = 2 := by omega
  have hYeq : perp Q Y = Y := (Submodule.eq_of_le_of_finrank_eq hYle (by omega)).symm
  have hind : ∀ a b : K, a • y + b • s y = 0 → a = 0 ∧ b = 0 := indep_of_ne hsp hK1 hsy
  have hYs : ∀ v ∈ Y, s v ∈ Y := hYinv s hsE
  have hspan := mem_span_of_finrank_two hY2 hyY (hYs y hyY) hind
  obtain ⟨α, β, h2⟩ := hspan (s (s y)) (hYs _ (hYs y hyY))
  have hα : α = 1 := alpha_eq_one hK1 hsp hY2 hYs hyY hind h2
  have h2' : s (s y) = y + β • s y := by rw [h2, hα, one_smul]
  have hsqY : ∀ v ∈ Y, s (s v) = β • s v + v := by
    intro v hv
    obtain ⟨a, b, rfl⟩ := hspan v hv
    have h3 := congrArg s h2'
    rw [map_add, map_smul] at h3
    simp only [map_add, map_smul]
    rw [h3, h2']
    module
  have hkey : ∀ v ∈ Y, s (s v) + β • s v + v = 0 := by
    intro v hv
    rw [hsqY v hv]
    calc β • s v + v + β • s v + v = (β • s v + β • s v) + (v + v) := by abel
      _ = 0 := by rw [hc2, hc2, add_zero]
  have hNY : ∀ x : X, s (s x) + β • s x + x ∈ Y := by
    intro x
    rw [← hYeq, mem_perp]
    intro y₁ hy₁
    have hsinv : ∀ v, s (s⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply s s⁻¹, mul_inv_cancel, leq_one_apply]
    obtain ⟨z₁, hz₁, rfl⟩ : ∃ z₁ ∈ Y, s z₁ = y₁ :=
      ⟨s⁻¹ y₁, hYinv s⁻¹ (E.inv_mem hsE) y₁ hy₁, hsinv y₁⟩
    obtain ⟨z₂, hz₂, rfl⟩ : ∃ z₂ ∈ Y, s z₂ = z₁ :=
      ⟨s⁻¹ z₁, hYinv s⁻¹ (E.inv_mem hsE) z₁ hz₁, hsinv z₁⟩
    have p1 : polar Q (s (s z₂)) (s (s x)) = polar Q z₂ x := by
      rw [polar_map hsQ (s z₂) (s x), polar_map hsQ z₂ x]
    have p2 : polar Q (s (s z₂)) (s x) = polar Q (s z₂) x := polar_map hsQ (s z₂) x
    have h0 := congrArg (fun w => polar Q w x) (hkey z₂ hz₂)
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left] at h0
    rw [polar_add_right, polar_add_right, polar_smul_right, p1, p2, smul_eq_mul]
    linear_combination h0
  set sl : Module.End K X := (s : X →ₗ[K] X) with hsl
  have hsl_p : sl ^ p = 1 := by
    rw [hsl, ← CFSG.RankThree.PartOne.KCOrthogonal.toLinearMap_pow, hsp]
    rfl
  have hsemi : sl.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (Polynomial.X ^ p - Polynomial.C 1 : K[X])) ?_ ?_
    · exact (Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree
    · simp [hsl_p]
  set Nend : Module.End K X := sl ^ 2 + β • sl + 1 with hNend
  have hNapp : ∀ x, Nend x = s (s x) + β • s x + x := by
    intro x
    simp [hNend, hsl, pow_two, Module.End.mul_apply]
  have hNsemi : Nend.IsSemisimple := by
    have := hsemi.aeval (Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + 1)
    convert this using 1
    simp [hNend, Algebra.smul_def]
  have hNnil : IsNilpotent Nend := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    rw [pow_two, Module.End.mul_apply, hNapp x, hNapp]
    exact hkey _ (hNY x)
  have hN0 : Nend = 0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hNnil hNsemi
  have hsqX : ∀ v : X, s (s v) = β • s v + v := fun v => by
    have h1 := congrArg (fun F => F v) hN0
    simp only [hNapp, LinearMap.zero_apply] at h1
    rw [add_assoc] at h1
    rw [eq_neg_of_add_eq_zero_left h1]
    exact neg_eq_of_add_eq_zero_right (hc2 _)
  have hβ : β ≠ 0 := by
    intro hβ0
    have hs2 : ∀ v : X, s (s v) = v := fun v => by
      rw [hsqX v, hβ0, zero_smul, zero_add]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hpow2 : ∀ j : ℕ, ∀ v : X, (s ^ (2 * j)) v = v := by
      intro j
      induction j with
      | zero => intro v; simp
      | succ j ih =>
        intro v
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, LinearEquiv.mul_apply, _root_.sq,
          LinearEquiv.mul_apply, hs2 v, ih v]
    have h1 : (s ^ p) y = s y := by
      rw [hk, pow_succ, LinearEquiv.mul_apply, hpow2 k (s y)]
    rw [hsp] at h1
    exact hsy h1.symm
  obtain ⟨v, hv0, hvQ, c, hc0, hGv⟩ := exists_fixed_singular hp hf hf1 hσp hσ1 hQ S (by omega)
  have hsqv : s (s v) = β • s v + v := hsqX v
  set Yv : Submodule K X := Submodule.span K {v, s v} with hYv
  have hvYv : v ∈ Yv := Submodule.subset_span (Set.mem_insert _ _)
  have hsvYv : s v ∈ Yv := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hsYv : ∀ w ∈ Yv, s w ∈ Yv := by
    intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [map_add, map_smul, map_smul, hsqv]
    exact Submodule.mem_span_pair.mpr ⟨b, a + b * β, by module⟩
  have hsYvk : ∀ k : ℕ, ∀ w ∈ Yv, (s ^ k) w ∈ Yv := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hsYv w hw)
  refine ⟨Yv, fun h => hv0 ((Submodule.mem_bot K).mp (h ▸ hvYv)), ?_, ?_, ?_⟩
  · intro g hg w hw
    obtain ⟨k, rfl⟩ := hEs g hg
    exact hsYvk k w hw
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [map_add, S.smul, S.smul, hSs, hGv, map_smul]
    exact Submodule.mem_span_pair.mpr ⟨σ a * c, σ b * c, by module⟩
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [map_add_smul_of_sq hsQ hβ hsqv a b, hvQ, mul_zero]

end Four

end LIDTwDF

end CFSG.StandardType
