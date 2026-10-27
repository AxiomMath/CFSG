module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

namespace OrdPGraph

theorem exists_field_twisted
    (f : ℕ) (hf : 1 ≤ f) (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f))
    {γ : Fin (twistedE6Datum 2 f).rank → ℤ} (hγ : γ ∈ (twistedE6Datum 2 f).roots)
    {z : twistedE6Group 2 f} (hz : z ∈ (twistedE6Datum 2 f).rootGroup γ) :
    ∃ z₁ ∈ (twistedE6Datum 2 f).rootGroup γ,
      ((e6Isogeny (GaloisField 2 (2 * f)) (z₁ : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) =
      Units.map (entrywiseHom δ.toRingHom)
        ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) := by
  set K := GaloisField 2 (2 * f)
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  have hcomm : ∀ x, δ (frobQ 2 f x) = frobQ 2 f (δ x) := RootDetectTwE6.map_frobQ f δ
  have hγ' : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots (frobQ 2 f) hγ
  obtain ⟨hα, hpr⟩ := liftRoot_spec hγ'
  set α₀ := liftRoot γ with hα₀
  have hval : ∀ (β : Fin (Tag.rank .E6) → ℤ) (hβ : IsRoot .E6 β) (c : K),
      Units.map (entrywiseHom δ.toRingHom)
        ((e6Isogeny K (e6Data_valid.xm K β c) : adjointGroup .E6 K) : ModGL .E6 K) =
      ((e6Isogeny K (e6Data_valid.xm K β (δ c)) : adjointGroup .E6 K) : ModGL .E6 K) := by
    intro β hβ c
    rw [e6Isogeny_xm K hβ, e6Isogeny_xm K hβ, yPar, yPar, xPar_of_isRoot hβ, xPar_of_isRoot hβ,
      RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement,
      RootDetectExc.units_map_entrywiseHom_eltUnit, map_mul, map_intCast]
  by_cases hfix : rho α₀ = α₀
  · obtain ⟨c, hc, hzc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f) hα hpr hfix z).mp hz
    have hδc : frobQ 2 f (δ c) = δ c := by rw [← hcomm, hc]
    refine ⟨xFixed (frobQ 2 f) hα hfix (δ c) hδc,
      (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f) hα hpr hfix _).mpr ⟨δ c, hδc, rfl⟩, ?_⟩
    rw [xFixed_val, hzc, hval α₀ hα c]
  · obtain ⟨c, hzc⟩ := (mem_twistedRootGroup_iff_of_pair (frobQ 2 f) hα hpr hfix z).mp hz
    refine ⟨xPair (frobQ 2 f) hθ hα hfix (δ c),
      (mem_twistedRootGroup_iff_of_pair (frobQ 2 f) hα hpr hfix _).mpr ⟨δ c, rfl⟩, ?_⟩
    rw [xPair_val, hzc, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, map_mul,
      hval α₀ hα c, hval (rho α₀) (isRoot_rho hα), map_mul, map_intCast, hcomm]

end OrdPGraph

section Family

theorem ggOrdPGraphModelAt_twistedE6 : GGOrdPGraphModelAt .twistedE6 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  show ∃ (C : Type) (_ : Group C) (π : twistedE6Group 2 f →* C), Function.Surjective π ∧
    π.ker = Subgroup.center (twistedE6Group 2 f) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (StatedLieTag.twistedE6 = .POmegaPlus ∧ n = 4 ∧ p = 3) →
        ∀ β : MulAut C, β ^ p = 1 → OrdPGraph.ModelDiagField (twistedE6Datum 2 f) π β
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπval : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  refine ⟨twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f), inferInstance, π, hπ,
    le_antisymm (RootDetectTwE6.ker_le_center f π hπvalT)
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.center_le_ker_of_surjective hπ hZ),
    fun p _ _ _ β hβ => ?_⟩
  obtain ⟨g, d, σ', -, hdiag, hβg⟩ := RootDetectTwE6.hform_twisted f hf π hπval β hβ
  refine ⟨g, fun γ hγ z hz => ?_⟩
  obtain ⟨z₁, hz₁, hz₁e⟩ := OrdPGraph.exists_field_twisted f hf σ' hγ hz
  obtain ⟨h, hh, hhd⟩ := hdiag γ hγ
  refine ⟨h * z₁ * h⁻¹, (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_ggTorus hh hγ)
    z₁).mp hz₁, Subtype.ext ?_⟩
  have hz₁e' : ((π z₁ : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      Units.map (entrywiseHom σ'.toRingHom) ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    hz₁e
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hβg, hhd z₁ hz₁, hz₁e']
  group

theorem ggOrdPGraphAt_twistedE6 : GGOrdPGraphAt .twistedE6 :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_twistedE6

end Family

end CFSG.StandardType
