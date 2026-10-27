module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairOneAssembly
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Pointwise

theorem ggFrobT_surjective (f : ℕ) : Function.Surjective (ggFrobT f) := by
  intro y
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2 ^ f) y
    (pow_pos (by norm_num : (0 : ℕ) < 2) f)
  exact ⟨x, by rw [ggFrobT_apply, hx]⟩

theorem twE6_derived_ggFixGp_eq
    {f : ℕ} (hf : 1 ≤ f) :
    ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ =
      graphFixedRootGroup TwistTag.E6 GGL (ggFrobT f) := by
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.mp hf))]
    rw [← pow_mul, Nat.mul_comm]
  let σ : K →+* K := iterateFrobenius K 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  obtain ⟨-, -, hder, -, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ GGL (ggFrobT f) (ggFrobT_apply f)
  change ⁅twistedFixedGroup TwistTag.E6 GGL (ggFrobT f),
      twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)⁆ =
    graphFixedRootGroup TwistTag.E6 GGL (ggFrobT f)
  rw [hder]
  exact map_baseChangeGL_graphFixedRootGroup_eq TwistTag.E6 Nat.prime_two hf K hK σ
    hσ (algebraMap K GGL) (ggFrobT_apply f) (ggFrobT_surjective f)

theorem twE6_model_decomp
    {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hB : TwE6BaseCompat n f p ψ B) (hψr : ψ.range = G₀)
    (a : Fin Tag.E6.rank → ℤ) (ha : IsRoot Tag.E6 a) :
    ∀ h ∈ B.Δ.model, ∃ t ∈ B.Δ.model, ∃ γ ∈ B.Δ.Γ, h = t * γ ∧
      (excCurve a B.Δ.g0⁻¹).map (MulAut.conj t).toMonoidHom = excCurve a B.Δ.g0⁻¹ ∧
      (excCurve (-a) B.Δ.g0⁻¹).map (MulAut.conj t).toMonoidHom = excCurve (-a) B.Δ.g0⁻¹ := by
  classical
  intro h hh
  let g₀ : ModGL Tag.E6 (ExcOmega f) := B.Δ.g0
  let f' : ModGL Tag.E6 (ExcOmega f) →* ModGL Tag.E6 (ExcOmega f) :=
    (MulAut.conj g₀⁻¹).toMonoidHom
  let R : Subgroup (ModGL Tag.E6 (ExcOmega f)) := ggFixGp .twistedE6 f
  have hf' : ∀ y : ModGL Tag.E6 (ExcOmega f), f' y = g₀⁻¹ * y * g₀ := by
    intro y
    show (MulAut.conj g₀⁻¹) y = g₀⁻¹ * y * g₀
    simp [MulAut.conj_apply]
  have hσsurj : Function.Surjective (ggFrobT f) := ggFrobT_surjective f
  have hRR : ⁅R, R⁆ = graphFixedRootGroup TwistTag.E6 GGL (ggFrobT f) :=
    twE6_derived_ggFixGp_eq B.one_le_f
  have hmodel : B.Δ.model = R.map f' := by
    have h1 : B.Δ.model = (twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)).map
        (MulAut.conj B.Δ.g0⁻¹).toMonoidHom :=
      model_eq_map_twistedFixedGroup B.Δ hB.Φ_eq
    exact h1
  rw [hmodel] at hh
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh
  have hrT : r ∈ twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) := hr
  have hset := coe_twistedFixedGroup_eq_mul (t := TwistTag.E6) (K := GGL) (σ := ggFrobT f) hσsurj
  have hr' : r ∈ (graphFixedTorus TwistTag.E6 GGL (ggFrobT f) :
        Set (ModGL TwistTag.E6.tag GGL)) *
      (graphFixedRootGroup TwistTag.E6 GGL (ggFrobT f) :
        Set (ModGL TwistTag.E6.tag GGL)) := hset ▸ hrT
  obtain ⟨u, hu, v, hv, huv⟩ := hr'
  let u' : ModGL Tag.E6 (ExcOmega f) := u
  let v' : ModGL Tag.E6 (ExcOmega f) := v
  have hu' : u' ∈ graphFixedTorus TwistTag.E6 GGL (ggFrobT f) := hu
  have hv' : v' ∈ graphFixedRootGroup TwistTag.E6 GGL (ggFrobT f) := hv
  have huv' : u' * v' = r := huv
  have hru : r = u' * v' := huv'.symm
  subst hru
  have huR : u' ∈ R := graphFixedTorus_le TwistTag.E6 (ExcOmega f) (ggFrobT f) hu'
  have hnorm : ∀ {α : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 α →
      (excCurve α g₀⁻¹).map (MulAut.conj (f' u')).toMonoidHom = excCurve α g₀⁻¹ := by
    intro α hα
    have huT : u' ∈ torusGroup Tag.E6 (ExcOmega f) := hu'.1
    have hun : u' ∈ Subgroup.normalizer
        (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 (ExcOmega f) α :
          Set (ModGL Tag.E6 (ExcOmega f))) :=
      torusGroup_le_normalizer_rootSubgroup (R := ExcOmega f) hα huT
    have hfu : f' u' = g₀⁻¹ * u' * g₀ := hf' u'
    unfold excCurve
    rw [hfu]
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      have hzu : (MulAut.conj u') z ∈
          CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 (ExcOmega f) α := by
        simpa only [MulAut.conj_apply, inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hun z).mp hz
      have heq : (MulAut.conj (g₀⁻¹ * u' * g₀)).toMonoidHom
            ((MulAut.conj g₀⁻¹).toMonoidHom z) =
          (MulAut.conj g₀⁻¹).toMonoidHom ((MulAut.conj u').toMonoidHom z) := by
        change g₀⁻¹ * u' * g₀ * (g₀⁻¹ * z * g₀) * (g₀⁻¹ * u' * g₀)⁻¹ =
          g₀⁻¹ * (u' * z * u'⁻¹) * g₀
        group
      rw [heq]
      exact Subgroup.mem_map_of_mem _ hzu
    · rintro x ⟨z, hz, rfl⟩
      have hzu : (MulAut.conj u'⁻¹) z ∈
          CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 (ExcOmega f) α := by
        simpa only [MulAut.conj_apply, inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (inv_mem hun) z).mp hz
      refine Subgroup.mem_map.2
        ⟨(MulAut.conj g₀⁻¹).toMonoidHom ((MulAut.conj u'⁻¹).toMonoidHom z), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ hzu
      · change g₀⁻¹ * u' * g₀ *
            (g₀⁻¹ * (u'⁻¹ * z * u') * g₀) * (g₀⁻¹ * u' * g₀)⁻¹ = g₀⁻¹ * z * g₀
        group
  refine ⟨f' u', ?_, f' v', ?_, ?_, ?_, ?_⟩
  · rw [hmodel]
    exact Subgroup.mem_map_of_mem _ huR
  · have hΓ : B.Δ.Γ = (⁅R, R⁆).map f' := by
      change ⁅B.Δ.model, B.Δ.model⁆ = (⁅R, R⁆).map f'
      rw [hmodel]
      exact (Subgroup.map_commutator R R f').symm
    have hvRR : v' ∈ ⁅R, R⁆ := hRR.symm ▸ hv'
    rw [hΓ]
    exact Subgroup.mem_map_of_mem _ hvRR
  · rw [map_mul]
  · exact hnorm ha
  · exact hnorm (IsRoot.neg ha)

end CFSG.StandardType.LieKnownR2.ExcPos

end
