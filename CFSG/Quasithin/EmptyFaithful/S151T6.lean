module

public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.S151ZG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15122ThreeCZL2Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G),
    (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L → ZL2 S L

@[expose] def Input15122ThreeDZL2Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) → SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L → ZL2 S L

variable {G : Type} [Group G] [Finite G]

theorem s151t_S_le_normalizer {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) (hnot : ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)) :
    s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
      (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
  · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
  · exact absurd h2 hnot

theorem input15122ThreeCZL2_of_loc (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kN : RankTwoSimpleNotA38)
    (hl : Input15122ThreeCZL2Loc) : Input15122ThreeCZL2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3C
  exact hl G L (s1516 T Z₁) h3C.1 hc.h18.four.2.1
    (s151t_S_le_normalizer h37 h38 hc (kN G L h3C.1)) hc.h20.sylow

theorem input15122ThreeDZL2_of_loc (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kN : SporadicSixNotA38)
    (hl : Input15122ThreeDZL2Loc) : Input15122ThreeDZL2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D hsix
  exact hl G L (s1516 T Z₁) hcomp.2.2 (hc.h20.three hcomp).1 hsix hc.h18.four.2.1
    (s151t_S_le_normalizer h37 h38 hc (kN G L hsix)) hc.h20.sylow

end CFSG.Quasithin
