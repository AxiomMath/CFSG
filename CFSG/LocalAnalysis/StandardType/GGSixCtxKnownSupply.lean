module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

private theorem largeEvenMarking_elim_of {X : Type*} [Group X] {P : LargeEvenMarkProp X} {Q : Prop}
    (h : LargeEvenMarking X P)
    (hQ : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → Q) : Q := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  exact hQ lab R I F θ hθ

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem ggSixCtx_normalizer_and_innerDiag_on_L (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    B ≤ Subgroup.normalizer (L : Set G) ∧
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
  ⟨largeEvenMarking_elim_of hctx.stdType.1 (fun _ _ _ _ _ _ h => h.2.1),
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2.2) hctx.stdType.1⟩

theorem ggSixCtx_bstar_selfCentralizing (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (H : Subgroup G) :
    ∀ y ∈ (Bs ⊔ H) ⊓ Subgroup.centralizer (Bs : Set G), orderOf y = p → y ∈ Bs :=
  fun y hy hyo => hctx.bstar.2.2.2 y hy.2 (hyo ▸ pow_orderOf_eq_one y)

theorem ggSixCtx_bstar_rank_facts (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    B ≤ Bs ∧ IsElemAbelian p Bs ∧
      Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧ (∀ a ∈ Bs, GGPsiInnerDiag Δ ψ a) ∧
      Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ ∧
      (∀ y ∈ (Bs ⊔ ggG0 p B x L D J) ⊓ Subgroup.centralizer (Bs : Set G), orderOf y = p →
        y ∈ Bs) ∧
      p ^ LargeEvenTwoLocalRank p ↥(Bs ⊔ ggG0 p B x L D J) ≤ Nat.card Bs := by
  refine ⟨hctx.bstar.1, hctx.bstar.2.1, hctx.2.2.2.2.2.2.1.1, hctx.2.2.2.2.2.2.1.2,
    bstar_inf_centralizer_ggG0_eq_bot hctx.config, ggSixCtx_bstar_selfCentralizing hctx _, ?_⟩
  have hp : p.Prime := hctx.prime
  calc p ^ LargeEvenTwoLocalRank p ↥(Bs ⊔ ggG0 p B x L D J)
      ≤ p ^ LargeEvenTwoLocalRank p G :=
        Nat.pow_le_pow_right hp.pos
          (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp _)
    _ = Nat.card B := hctx.sstar.1.2.1.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1

end CFSG.StandardType
