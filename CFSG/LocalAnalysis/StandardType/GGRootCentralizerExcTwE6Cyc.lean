module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmega
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSU
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUSpTag
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExc
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcE6
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Root
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RootCentExc

section Model

variable {U C G : Type*} [Group U] [Group C] [Group G]

theorem normalizerMonoidHom_mul_congr_mem_range {ψ : U →* G} {π : U →* C}
    (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) {X : Set U}
    (hX : Subgroup.closure X = ⊤) {y g : G} (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hg : g ∈ ψ.range) (α : MulAut C)
    (hact : ∀ z ∈ X, ∃ z' : U, (y * g)⁻¹ * ψ z * (y * g) = ψ z' ∧ π z' = α (π z)) :
    ψ.range.normalizerMonoidHom ⟨y, hyN⟩ * MulAut.congr (AutSt.modelEquiv ψ π hπ hker) α ∈
      (MulAut.conj : ψ.range →* MulAut ψ.range).range := by
  set Θ := AutSt.modelEquiv ψ π hπ hker
  have hΘ : ∀ v, ((Θ (π v) : ψ.range) : G) = ψ v := fun v =>
    AutSt.modelEquiv_apply ψ π hπ hker v
  have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer hg
  set κ := ψ.range.normalizerMonoidHom
  have happ : ∀ (m : Subgroup.normalizer (ψ.range : Set G)) (x : ψ.range),
      ((κ m x : ψ.range) : G) = (m : G) * x * (m : G)⁻¹ := fun _ _ => rfl
  set cN : Subgroup.normalizer (ψ.range : Set G) := ⟨y, hyN⟩ * ⟨g, hgN⟩ with hcN
  have hcN' : (cN : G) = y * g := rfl
  have hF : (κ cN⁻¹).toMonoidHom.comp (Θ.toMonoidHom.comp π) =
      (MulAut.congr Θ α).toMonoidHom.comp (Θ.toMonoidHom.comp π) := by
    refine MonoidHom.eq_of_eqOn_dense hX fun z hz => ?_
    obtain ⟨z', hz'1, hz'2⟩ := hact z hz
    apply Subtype.ext
    change ((κ cN⁻¹ (Θ (π z)) : ψ.range) : G) = ((Θ (α (Θ.symm (Θ (π z)))) : ψ.range) : G)
    rw [happ, hΘ, Subgroup.coe_inv, hcN', inv_inv, hz'1, MulEquiv.symm_apply_apply, ← hz'2, hΘ]
  have hσ : κ cN⁻¹ = MulAut.congr Θ α := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, hv⟩ := hπ (Θ.symm x)
    have hx : x = Θ (π v) := by rw [hv, MulEquiv.apply_symm_apply]
    rw [hx]
    exact DFunLike.congr_fun hF v
  have hκc : κ cN = (MulAut.congr Θ α)⁻¹ := by
    rw [← hσ, map_inv, inv_inv]
  have hginn : κ (⟨g, hgN⟩)⁻¹ = MulAut.conj (⟨g, hg⟩ : ψ.range)⁻¹ := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [happ, MulAut.conj_apply]
    rfl
  have hy' : (⟨y, hyN⟩ : Subgroup.normalizer (ψ.range : Set G)) = cN * (⟨g, hgN⟩)⁻¹ := by
    rw [hcN, mul_inv_cancel_right]
  rw [hy', map_mul, hginn, hκc]
  have hn := (normal_range_mulAutConj (M := ψ.range)).conj_mem _
    ⟨(⟨g, hg⟩ : ψ.range)⁻¹, rfl⟩ (MulAut.congr Θ α)⁻¹
  rwa [inv_inv] at hn

end Model

section Diag

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] noncomputable def compatParamAut :
    ↥(TableB.TwE6.compat σ) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  (graphFixedRootGroup TwistTag.E6 K σ).normalizerMonoidHom.comp
    (((rootDiagUnitHom TwistTag.E6.tag K).comp (TableB.TwE6.compat σ).subtype).codRestrict _
      fun b => rootDiagUnit_mem_normalizer_graphFixedRootGroup b.2)

theorem coe_compatParamAut_apply (b : ↥(TableB.TwE6.compat σ))
    (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    ((compatParamAut σ b g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (b : Fin 6 → Kˣ) * g *
        (rootDiagUnit TwistTag.E6.tag (b : Fin 6 → Kˣ))⁻¹ :=
  rfl

theorem compatParamAut_mem_range_of_mem_torus {t : ↥(TableB.TwE6.compat σ)}
    (ht : (t : Fin 6 → Kˣ) ∈ TableB.TwE6.torus₀ σ) :
    compatParamAut σ t ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range := by
  obtain ⟨s, hs, hst⟩ := ht
  have hmem : rootDiagUnit TwistTag.E6.tag (t : Fin 6 → Kˣ) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
    rw [← hst]
    exact TableB.TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  exact ⟨⟨_, hmem⟩, MulEquiv.ext fun g => Subtype.ext rfl⟩

end Diag

end RootCentExc

section TwE6

theorem ggTwE6InnerDiagCyclicInput_holds : GGTwE6InnerDiagCyclicInput := by
  intro G _ _ n f ψ hadm hker hC Y hYN hYd
  obtain ⟨-, hf, -⟩ := hadm
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
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
    rw [← hσθ]
    exact hder
  have hZ' : Subgroup.center
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) = ⊥ := by
    rw [← hσθ]
    exact hZ
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπvalT : ∀ z, ((π z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπker : π.ker = ψ.ker := by
    rw [AutSt.ker_eq_center hker hC]
    refine le_antisymm (RootDetectTwE6.ker_le_center f π hπvalT) fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc := RootCentExc.map_mem_center_of_surjective hπ hz
    rw [hZ', Subgroup.mem_bot] at hzc
    exact hzc
  set Θ := AutSt.modelEquiv ψ π hπ hπker
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega
  refine RootCentExc.exists_mem_zpowers_mul_of_param hC
    ((TableB.TwE6.torus₀ (frobQ 2 f)).subgroupOf (TableB.TwE6.compat (frobQ 2 f)))
    (fun a a' ha' => ?_)
    ((MulAut.congr Θ).toMonoidHom.comp (RootCentExc.compatParamAut (frobQ 2 f)))
    (fun t ht => ?_) hYN (fun y hy => ?_)
  ·
    obtain ⟨k, hk⟩ := TableB.TwE6.exists_mul_inv_pow_mem hq hK (frobQ_apply 2 f) a.2 a'.2 ha'
    exact ⟨k, hk⟩
  ·
    obtain ⟨c, hc⟩ := RootCentExc.compatParamAut_mem_range_of_mem_torus (frobQ 2 f) ht
    refine ⟨Θ c, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hc, AutSt.congr_conj]
  ·
    obtain ⟨g, hg, b, hb, hact⟩ := InnerDiagTwE6.twE6DiagInput_of_rankOne hf
      (InnerDiagTwE6.twE6RankOneInput_holds f hf) G ψ hker y (hYd y hy)
    refine ⟨(⟨b, hb⟩ : ↥(TableB.TwE6.compat (frobQ 2 f)))⁻¹, ?_⟩
    rw [map_inv, inv_inv]
    refine RootCentExc.normalizerMonoidHom_mul_congr_mem_range hπ hπker
      (InnerDiagTwE6.closure_fundamental_eq_top (frobQ 2 f) (frobQ_frobQ 2 f hf)) (hYN hy) hg _
      ?_
    rintro z ⟨j, γ, hγ, hz⟩
    obtain ⟨z', hz'1, hz'2⟩ := hact j γ hγ z hz
    exact ⟨z', hz'1, Subtype.ext hz'2⟩

theorem ggRootCentralizerCyclicTag_twistedE6 : GGRootCentralizerCyclicTag .twistedE6 :=
  ggRootCentralizerCyclicTag_twistedE6_of_cyclic ggTwE6InnerDiagCyclicInput_holds

theorem ggRootCentralizerCyclicInput_holds : GGRootCentralizerCyclicInput :=
  ggRootCentralizerCyclicInput_of_remaining ggRootCentralizerCyclicTag_PSU
      ggRootCentralizerCyclicTag_PSp ggRootCentralizerCyclicTag_POmegaPlus
      ggRootCentralizerCyclicTag_POmegaMinus ggRootCentralizerCyclicTag_F4
      ggRootCentralizerCyclicTag_E6 ggRootCentralizerCyclicTag_E7 ggRootCentralizerCyclicTag_E8
      (ggRootCentralizerCyclicTag_twistedE6_of_cyclic ggTwE6InnerDiagCyclicInput_holds)

end TwE6

end CFSG.StandardType
