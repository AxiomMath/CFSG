module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

section Eval

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {E : Type*} [Field E]
  [Algebra K E] {U : Submodule K V} (φ : E →ₗ[K] U) {x : V ≃ₗ[K] V} {μ : E}

theorem pow_apply_phi (hx : ∀ z, x (φ z : V) = (φ (μ * z) : V)) (n : ℕ) (z : E) :
    (x.toLinearMap ^ n) (φ z : V) = (φ (μ ^ n * z) : V) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h1 : x.toLinearMap (φ z : V) = (φ (μ * z) : V) := hx z
    rw [h1, ih, pow_succ, mul_assoc]

theorem aeval_apply_phi (hx : ∀ z, x (φ z : V) = (φ (μ * z) : V)) (f : K[X]) (z : E) :
    aeval x.toLinearMap f (φ z : V) = (φ (aeval μ f * z) : V) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, map_add, add_mul, map_add, Submodule.coe_add]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, pow_apply_phi φ hx]
    show (algebraMap K (Module.End K V) a) _ = _
    rw [Module.algebraMap_end_apply, ← Submodule.coe_smul, ← map_smul, Algebra.smul_def,
      mul_assoc]

theorem sup_le_primaryComponent {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂) {μ₁ μ₂ : E}
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V)) (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V))
    {f : K[X]} (hf₁ : aeval μ₁ f = 0) (hf₂ : aeval μ₂ f = 0) :
    U₁ ⊔ U₂ ≤ primaryComponent x.toLinearMap f := by
  refine sup_le (fun v hv => ?_) (fun v hv => ?_)
  · obtain ⟨z, hz⟩ := hφ₁ ⟨v, hv⟩
    rw [mem_primaryComponent]
    have := aeval_apply_phi φ₁ hx₁ f z
    rw [hf₁, zero_mul, map_zero, Submodule.coe_zero, hz] at this
    exact this
  · obtain ⟨z, hz⟩ := hφ₂ ⟨v, hv⟩
    rw [mem_primaryComponent]
    have := aeval_apply_phi φ₂ hx₂ f z
    rw [hf₂, zero_mul, map_zero, Submodule.coe_zero, hz] at this
    exact this

end Eval

section Primary

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem mem_primaryFactors_of_primaryComponent_ne_bot {x : Module.End K V} {h : K[X]}
    (hirr : Irreducible h) (hmon : h.Monic) (hne : primaryComponent x h ≠ ⊥) :
    h ∈ primaryFactors x := by
  rw [mem_primaryFactors]
  refine ⟨hirr, hmon, ?_⟩
  by_contra hdvd
  have hcop : IsCoprime h (minpoly K x) := (Irreducible.coprime_iff_not_dvd hirr).mpr hdvd
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval x u * aeval x h = 1 := by
    have := congrArg (aeval x) huv
    simpa [minpoly.aeval] using this
  apply hne
  rw [eq_bot_iff]
  intro w hw
  rw [mem_primaryComponent] at hw
  rw [Submodule.mem_bot]
  have h2 : (aeval x u * aeval x h) w = w := by rw [h1]; rfl
  rw [Module.End.mul_apply, hw, map_zero] at h2
  exact h2.symm

theorem mem_of_isOrbitRepresentatives_of_selfdual {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hself : reciprocalPolynomial h = h) : h ∈ Rep := by
  obtain ⟨r, ⟨hrRep, hr⟩, -⟩ := hRep.2 h hh
  have hrf : r ∈ primaryFactors x.toLinearMap := hRep.1 hrRep
  rcases hr with hr | hr
  · rw [hr]
    exact hrRep
  · have hrr : reciprocalPolynomial (reciprocalPolynomial r) = r :=
      reciprocalPolynomial_reciprocalPolynomial (monic_of_mem_primaryFactors hrf)
        (hx.coeff_zero_ne hrf)
    have : r = h := by rw [← hrr, ← hr, hself]
    rw [← this]
    exact hrRep

theorem two_le_primaryMultiplicity {x : Module.End K V} {h : K[X]} [Fact (Irreducible h)]
    (hdeg : h.natDegree ≤ 2) {R : Submodule K V} (hR : R ≤ primaryComponent x h)
    (hR4 : finrank K R = 4) : 2 ≤ primaryMultiplicity x h := by
  have h1 := Submodule.finrank_mono hR
  rw [hR4, finrank_primaryComponent] at h1
  have h1' : 4 ≤ h.natDegree * primaryMultiplicity x h := h1
  by_contra hlt
  push Not at hlt
  have h2 : primaryMultiplicity x h ≤ 1 := by omega
  have h3 : h.natDegree * primaryMultiplicity x h ≤ 2 * 1 := Nat.mul_le_mul hdeg h2
  omega

end Primary

section Selfdual

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] [Module.Finite K E]

theorem reciprocalPolynomial_minpoly_eq (bar : E ≃ₐ[K] E) {μ : E} (hμ : μ ≠ 0)
    (hbar : bar μ = μ⁻¹) : reciprocalPolynomial (minpoly K μ) = minpoly K μ := by
  have hint : IsIntegral K μ := Algebra.IsIntegral.isIntegral μ
  have h0 : (minpoly K μ).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hμ
  have hroot : aeval μ (reciprocalPolynomial (minpoly K μ)) = 0 := by
    have h1 := aeval_reciprocalPolynomial_of_unit (A := E) (Units.mk0 μ hμ) (minpoly K μ)
    have h2 : aeval μ⁻¹ (minpoly K μ) = 0 := by
      rw [← hbar]
      have := Polynomial.aeval_algHom_apply (bar : E →ₐ[K] E) μ (minpoly K μ)
      rw [minpoly.aeval, map_zero] at this
      exact this
    simp only [Units.val_mk0, Units.val_inv_eq_inv_val] at h1
    rw [h1, h2, mul_zero, smul_zero]
  exact minpoly.eq_of_irreducible_of_monic (irreducible_reciprocalPolynomial
    (minpoly.irreducible hint) h0) hroot (monic_reciprocalPolynomial h0)

end Selfdual

section Special

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem map_eq_one_of_isPerfect {G M : Type*} [Group G] [CommMonoid M] (hG : Group.IsPerfect G)
    (f : G →* M) (g : G) : f g = 1 := by
  have h1 : g ∈ commutator G := Group.IsPerfect.mem_commutator
  have hle : commutator G ≤ (f.toHomUnits).ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have h2 := hle h1
  rw [MonoidHom.mem_ker] at h2
  have := congrArg Units.val h2
  simpa using this

theorem range_le_specialBlock {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    {R : Submodule K V} (hR : R ≤ primaryComponent x.toLinearMap h) {G : Type*} [Group G]
    (hG : Group.IsPerfect G) (ι : G →* (V ≃ₗ[K] V))
    (hιO : ∀ g, ι g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hιx : ∀ g, ι g * x = x * ι g)
    (hιfix : ∀ g, ∀ w ∈ (LinearMap.BilinForm.orthogonal (polarBilin Q) R), ι g w = w) :
    ι.range ≤ specialBlock Q x h := by
  have hothers : ∀ r ∈ othersSpace x.toLinearMap h,
      r ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) R := by
    intro r hr
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hu' : u ∈ orbitSpace x.toLinearMap h := Submodule.mem_sup_left (hR hu)
    rw [polarBilin_apply_apply]
    exact hx.polar_orbit_others hh hu' hr
  have hmem : ∀ g, ι g ∈ supportedBlock Q x h := by
    intro g
    refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨?_, fun v => ?_⟩,
      fun r hr => hιfix g r (hothers r hr)⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hιO g)
    · have := congrArg (fun m : V ≃ₗ[K] V => m v) (hιx g)
      exact this
  let ιS : G →* ↥(supportedBlock Q x h) := ι.codRestrict _ hmem
  have hdet : ∀ g, blockDet Q x h (ιS g) = 1 := fun g =>
    map_eq_one_of_isPerfect hG ((blockDet Q x h).comp ιS) g
  rintro _ ⟨g, rfl⟩
  exact mem_specialBlock.mpr ⟨hmem g, hdet g⟩

end Special

end CFSG.RankThree.PartOne.KCOrthogonal
