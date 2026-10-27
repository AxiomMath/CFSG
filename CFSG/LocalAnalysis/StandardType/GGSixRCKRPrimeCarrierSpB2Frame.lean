module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4Frame
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB2Part2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart1

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.F4Pilot


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (ZMod 2) L]
  [Algebra.IsAlgebraic (ZMod 2) L]

theorem exists_sp2Frame (v : WeylGroup Tag.F4) :
    ∃ ψ : ↥(StatedSp 2 L) →* ModGL Tag.F4 L, Function.Injective ψ ∧
      ψ.range = rootSpan Tag.F4 L ((fun α => v • α) '' b2LeviRoots) ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp 2 L)),
        frobGL σ (ψ X) = ψ (statedSpMap (σ : L →+* L) 2 X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp 2 L), ∀ X, t * ψ X * t⁻¹ = ψ (W * X * W⁻¹) := by
  let ι := CFSG.StandardType.F4ExplicitPos.RationalB2.iOmegaB2 L
  have hinj : Function.Injective ι :=
    CFSG.StandardType.F4ExplicitPos.RationalB2.iOmegaB2_injective (Ω := L)
  have hrange : MonoidHom.range ((adjointGroup Tag.F4 L).subtype.comp ι)
      = rootSpan Tag.F4 L b2LeviRoots := by
    rw [MonoidHom.range_comp]
    exact CFSG.StandardType.F4ExplicitPos.RationalB2.range_iOmegaB2 (Ω := L)
  have hnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp 2 L)),
      frobGL (τ := Tag.F4) σ (((adjointGroup Tag.F4 L).subtype.comp ι) X)
        = ((adjointGroup Tag.F4 L).subtype.comp ι) (statedSpMap (σ : L →+* L) 2 X) := by
    intro σ X
    change frobGL (τ := Tag.F4) σ
        (((ι X : ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L)) =
      (((ι (statedSpMap (σ : L →+* L) 2 X) : ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L))
    rw [CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := L) σ]
    exact congrArg (fun z : ↥(adjointGroup Tag.F4 L) => (z : ModGL Tag.F4 L))
      (DFunLike.congr_fun
        (CFSG.StandardType.F4ExplicitPos.RationalB2.iOmegaB2_natural (Ω := L)
          (σ : L →+* L)) X)
  have htor : ∀ t ∈ torusGroup Tag.F4 L, ∃ t₁ ∈ rootSpan Tag.F4 L b2LeviRoots,
      ∀ g ∈ rootSpan Tag.F4 L b2LeviRoots, t * g * t⁻¹ = t₁ * g * t₁⁻¹ :=
    fun t ht => exists_mem_rootSpan_conj_eq_b2Levi ht
  obtain ⟨ι₀, hinj₀, hrange₀, hnat₀, htor₀⟩ :=
    exists_spFrame_of_adjoint (L := L) ι hinj hrange hnat htor
  exact exists_spFrame_conj (L := L) v (fun α hα => hα.1) ι₀ hinj₀ hrange₀ hnat₀ htor₀

end CFSG.StandardType.RCKRP

end
