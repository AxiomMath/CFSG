module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LieType.Chevalley.GraphFixedRankOneScalar

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K]

theorem exists_mem_orbitRankOneGroup_conj_twE6SplitFrameHom (σ : K →+* K) {p : ℕ}
    [Fact p.Prime] {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) (a : Fin Tag.F4.rank) :
    ∃ x : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (x : ModGL TwistTag.E6.tag K) ∈ orbitRankOneGroup TwistTag.E6 K σ a ∧
      ∀ s : Fin Tag.F4.rank → ZMod p,
        x * ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * x⁻¹ =
          ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
            (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple Tag.F4 a) s)) := by
  let wsub : ↥(relWeylTwist TwistTag.E6) :=
    ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩
  have hn : canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1 ∈
      graphFixedRootMonomial TwistTag.E6 K σ :=
    canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 K σ wsub.2
  refine ⟨⟨_, graphFixedRootMonomial_le TwistTag.E6 K σ hn⟩, ?_, fun s => Subtype.ext ?_⟩
  · change canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1 ∈
      orbitRankOneGroup TwistTag.E6 K σ a
    rw [show wsub.1 = TwistTag.E6.orbitReflection a from rfl,
      canonicalRep_orbitReflection_eq_orbitN TwistTag.E6 σ a]
    exact orbitN_one_mem_orbitRankOneGroup (t := TwistTag.E6) a
  · change canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1 *
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ (ExcFrames.twE6SplitTheta p s) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1)⁻¹ =
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (ExcFrames.twE6SplitTheta p (TableBExc.torusAct .F4 p (simple Tag.F4 a) s))
    rw [ExcFrames.canonicalRep_conj_frameDiag ζ hζ wsub.1 (ExcFrames.twE6SplitTheta p s),
      ExcFrames.torusAct_twE6SplitTheta wsub s]
    rw [show wsub = ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ from rfl,
      foldedWeylEquiv_orbitReflection (t := TwistTag.E6) a]
    rfl

theorem iSup_orbitRankOneGroup_subgroupOf_twE6 [Finite K] (σ : K →+* K) :
    (⨆ a : Fin Tag.F4.rank, (orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) = ⊤ := by
  have hσ : Function.Surjective σ :=
    Finite.injective_iff_surjective.mp (RingHom.injective σ)
  have hC : graphFixedRootGroup TwistTag.E6 K σ =
      ⨆ a : Fin Tag.F4.rank, orbitRankOneGroup TwistTag.E6 K σ a :=
    graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6) hσ
  have hle : ∀ a : Fin Tag.F4.rank,
      orbitRankOneGroup TwistTag.E6 K σ a ≤ graphFixedRootGroup TwistTag.E6 K σ := by
    intro a
    rw [hC]
    exact le_iSup (fun a : Fin Tag.F4.rank => orbitRankOneGroup TwistTag.E6 K σ a) a
  refine (Subgroup.map_injective
    (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective).eq_iff.mp ?_
  rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
  exact (iSup_congr fun a => Subgroup.map_subgroupOf_eq_of_le (hle a)).trans hC.symm

end CFSG.StandardType.TwE6SplitRootGen

end
