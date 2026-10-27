module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  LayerSixE

section Tags

@[expose] def GGTwE6InndiagCompInput : Prop :=
  ∀ f : ℕ, 2 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ α ∈ LayerSixE.twInndiagAut f, α ^ p = 1 →
    ∀ X : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → GGNotExcThreeOrder (ggCQ X)

theorem ggLayerNotExcThreeTag_twistedE6_of_inputs (hcore : GGTwE6InndiagCoreInput)
    (hcomp : GGTwE6InndiagCompInput) : GGLayerNotExcThreeTag .twistedE6 := by
  intro G _ _ n f ψ G₀ hpres hf2 p hp hp2 y hy hyN hdiag C hC
  obtain ⟨⟨⟨-, hf, -⟩, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have : Finite (twistedE6Group 2 f) := by
    have : Finite (Module.End (GaloisField 2 (2 * f)) (Fin e6Data.d →₀ GaloisField 2 (2 * f))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    infer_instance
  obtain ⟨π, hπ, hπker, hodd, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hyN hdiag
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hyN p
    rw [hy] at h1
    exact GGInduces.unique hπ (Subgroup.one_mem _) h1 (GGInduces.one hkπ)
  obtain ⟨hAp, hAc⟩ := TagsExc.isPGroup_zpowers_of_pow_eq_one hαp
  obtain ⟨β, S, hS⟩ := hcore f hf p hp hp2 _ hAp hAc ((Subgroup.zpowers_le).mpr hαD)
  exact TagsExc.ggNotExcThree_of_isComponentOf_model hπ hπker.le hodd hkπ hyN hα hS
    (fun X hX => hcomp f hf2 p hp hp2 α hαD hαp X hX) hC

end Tags

end CFSG.StandardType
