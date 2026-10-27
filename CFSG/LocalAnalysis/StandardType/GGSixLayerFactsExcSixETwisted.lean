module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cyc
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace LayerSixE

section TwE6

@[expose] noncomputable def twInndiagAut (f : ℕ) :
    Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :=
  (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
    MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range ⊔
      (RootCentExc.compatParamAut (frobQ 2 f)).range

theorem exists_induces_twistedE6 {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →* ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))}
    (hπval : ∀ z, ((π z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {G : Type} [Group G] (ψ : twistedE6Group 2 f →* G)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f)) (hkπ : ψ.ker ≤ π.ker) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hc : GGPsiInnerDiag (twistedE6Datum 2 f) ψ c) :
    ∃ α ∈ twInndiagAut f, GGInduces π ψ c α := by
  obtain ⟨g, ⟨u, rfl⟩, b, hb, hact⟩ := InnerDiagTwE6.twE6DiagInput_of_rankOne hf
    (InnerDiagTwE6.twE6RankOneInput_holds f hf) G ψ hker c hc
  have hgN : ψ u ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer ⟨u, rfl⟩
  have hdN : (c * ψ u)⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    inv_mem (mul_mem hcN hgN)
  have hδ : GGInduces π ψ (c * ψ u)⁻¹
      (RootCentExc.compatParamAut (frobQ 2 f) (⟨b, hb⟩ : ↥(TableB.TwE6.compat (frobQ 2 f)))) := by
    refine GGInduces.of_generators hkπ
      (InnerDiagTwE6.closure_fundamental_eq_top (frobQ 2 f) (frobQ_frobQ 2 f hf)) hdN ?_
    rintro z ⟨j, γ, hγ, hz⟩
    obtain ⟨z', hz'1, hz'2⟩ := hact j γ hγ z hz
    refine ⟨z', by rw [inv_inv, hz'1], Subtype.ext ?_⟩
    rw [RootCentExc.coe_compatParamAut_apply, hπval, hπval]
    exact hz'2
  have hδ' := hδ.inv
  rw [inv_inv] at hδ'
  have hc' := hδ'.mul (Subgroup.le_normalizer ⟨u⁻¹, rfl⟩) (GGInduces.psi hkπ u⁻¹)
  have hce : c * ψ u * ψ u⁻¹ = c := by rw [map_inv, mul_inv_cancel_right]
  rw [hce] at hc'
  refine ⟨_, mul_mem (Subgroup.mem_sup_right (inv_mem ⟨_, rfl⟩))
    (Subgroup.mem_sup_left ⟨_, rfl⟩), hc'⟩

end TwE6

end LayerSixE

section Tags

theorem LayerSixE.exists_model_twistedE6 {f : ℕ} (hf : 1 ≤ f) :
    ∃ π : twistedE6Group 2 f →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Surjective π ∧ π.ker = Subgroup.center (twistedE6Group 2 f) ∧
        Odd (Nat.card π.ker) ∧
        ∀ z, ((π z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
          ((e6IsogenyT (GaloisField 2 (2 * f))
              (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
            adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
              ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
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
  refine ⟨π, hπ, le_antisymm (RootDetectTwE6.ker_le_center f π hπvalT) fun z hz => ?_,
    RootDetectTwE6.odd_card_ker f π hπvalT, hπvalT⟩
  rw [MonoidHom.mem_ker]
  have hzc := RootCentExc.map_mem_center_of_surjective hπ hz
  rw [hZ', Subgroup.mem_bot] at hzc
  exact hzc

@[expose] def GGTwE6InndiagCoreInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
        A ≤ LayerSixE.twInndiagAut f →
          ∃ (β : Type) (S : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))), LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggLayerTags_twistedE6_of_inndiagCore (h : GGTwE6InndiagCoreInput) :
    GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm hN hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm hN hdiag => ?_⟩ <;>
  · obtain ⟨⟨⟨-, hf, -⟩, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have : Finite (twistedE6Group 2 f) := by
      have : Finite (Module.End (GaloisField 2 (2 * f)) (Fin e6Data.d →₀ GaloisField 2 (2 * f))) :=
        Module.finite_of_finite (GaloisField 2 (2 * f))
      infer_instance
    obtain ⟨π, hπ, hπker, hodd, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
    have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
    have hl := LayerSixE.ggLayer_of_model hπ hπker.le hodd hkπ hE hcomm hN
      (fun e he => LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ (hN he) (hdiag e he))
      (fun A hA hAc hAD => h f hf p hp hp2 A hA hAc hAD)
    first
    | exact hl.1
    | exact hl.2

end Tags

end CFSG.StandardType
