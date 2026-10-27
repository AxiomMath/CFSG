module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

theorem w183_eq_of_singular {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P P' : HypPair Q) (h : P.Orth P') {a c : V → K}
    (ha : ∀ u v, u ∈ P.perp → v ∈ P.perp → a (u + v) = a u + a v)
    (ha' : ∀ (t : K) (u : V), u ∈ P.perp → a (t • u) = t * a u)
    (hc : ∀ u v, u ∈ P.perp → v ∈ P.perp → c (u + v) = c u + c v)
    (hc' : ∀ (t : K) (u : V), u ∈ P.perp → c (t • u) = t * c u)
    (hsing : ∀ u ∈ P.perp, Q u = 0 → a u = c u) : ∀ w ∈ P.perp, a w = c w := by
  have he' : P'.e ∈ P.perp := HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩
  have hf' : P'.f ∈ P.perp := HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩
  have hlin : ∀ g : V → K, (∀ u v, u ∈ P.perp → v ∈ P.perp → g (u + v) = g u + g v) →
      (∀ (t : K) (u : V), u ∈ P.perp → g (t • u) = t * g u) →
      ∀ (s : V) (t₁ t₂ : K), s ∈ P.perp →
        g (s + t₁ • P'.e + t₂ • P'.f) = g s + t₁ * g P'.e + t₂ * g P'.f := by
    intro g hg hg' s t₁ t₂ hs
    have h1 : t₁ • P'.e ∈ P.perp := P.perp.smul_mem t₁ he'
    have h2 : t₂ • P'.f ∈ P.perp := P.perp.smul_mem t₂ hf'
    rw [hg _ _ (P.perp.add_mem hs h1) h2, hg _ _ hs h1, hg' t₁ _ he', hg' t₂ _ hf']
  intro w hw
  set w₀ := P'.proj w with hw₀
  have hw₀P' : w₀ ∈ P'.perp := P'.proj_mem_perp w
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hw₀P'
  have hw₀P : w₀ ∈ P.perp := by
    rw [hw₀, HypPair.proj]
    exact P.perp.sub_mem (P.perp.sub_mem hw (P.perp.smul_mem _ he')) (P.perp.smul_mem _ hf')
  have hsP : w₀ + P'.e + (-Q w₀) • P'.f ∈ P.perp :=
    P.perp.add_mem (P.perp.add_mem hw₀P he') (P.perp.smul_mem _ hf')
  have hs : Q (w₀ + P'.e + (-Q w₀) • P'.f) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, P'.Q_e, P'.Q_f]
    simp only [polar_add_left, polar_smul_right_eq]
    rw [polar_comm Q w₀ P'.e, polar_comm Q w₀ P'.f, h1, h2, P'.polar_ef]
    ring
  have hdec : w = (w₀ + P'.e + (-Q w₀) • P'.f) + (polar Q w P'.f - 1) • P'.e +
      (polar Q w P'.e + Q w₀) • P'.f := by
    conv_lhs => rw [P'.eq_add_proj w]
    rw [← hw₀]
    module
  rw [hdec, hlin a ha ha' _ _ _ hsP, hlin c hc hc' _ _ _ hsP, hsing _ hsP hs,
    hsing _ he' P'.Q_e, hsing _ hf' P'.Q_f]

theorem w183_dual_vector {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) {a : V → K}
    (ha : ∀ u v, u ∈ P.perp → v ∈ P.perp → a (u + v) = a u + a v)
    (ha' : ∀ (t : K) (u : V), u ∈ P.perp → a (t • u) = t * a u) :
    ∃ v ∈ P.perp, ∀ u ∈ P.perp, polar Q u v = a u := by
  have hadd : ∀ x y : V, P.proj (x + y) = P.proj x + P.proj y := fun x y => by
    simp only [HypPair.proj, polar_add_left]
    module
  have hsmul : ∀ (t : K) (x : V), P.proj (t • x) = t • P.proj x := fun t x => by
    simp only [HypPair.proj, polar_smul_left_eq, smul_eq_mul]
    module
  have hfix : ∀ u ∈ P.perp, P.proj u = u := fun u hu => by
    obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hu
    rw [HypPair.proj, polar_comm Q u P.f, polar_comm Q u P.e, h1, h2]
    simp
  let A : V →ₗ[K] K :=
    { toFun := fun z => a (P.proj z)
      map_add' := fun x y => by
        rw [hadd]
        exact ha _ _ (P.proj_mem_perp x) (P.proj_mem_perp y)
      map_smul' := fun t x => by
        rw [hsmul, smul_eq_mul, RingHom.id_apply]
        exact ha' t _ (P.proj_mem_perp x) }
  obtain ⟨v₀, hv₀⟩ := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).surjective A
  refine ⟨P.proj v₀, P.proj_mem_perp v₀, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hu
  have hz : ∀ z, polar Q v₀ z = a (P.proj z) := fun z => by
    have := congrArg (fun φ => φ z) hv₀
    simpa [LinearMap.BilinForm.toDual_def, A] using this
  rw [HypPair.proj, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_comm Q u P.e, polar_comm Q u P.f, h1, h2, mul_zero, mul_zero, sub_zero, sub_zero,
    polar_comm Q u v₀, hz u, hfix u hu]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
