module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BlockNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

theorem S_eq_sup_inf_centralizer (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {S : Subgroup G} (hLS : D.T ⊓ c.L ≤ S) (hST : S ≤ D.T) :
    S = (D.T ⊓ c.L) ⊔ (S ⊓ Subgroup.centralizer (c.V : Set G)) := by
  refine le_antisymm ?_ (sup_le hLS inf_le_left)
  intro s hs
  obtain ⟨l, hl, hc⟩ :=
    exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c (hST hs)
  have hcS : s * l⁻¹ ∈ S := S.mul_mem hs (S.inv_mem (hLS hl))
  have hs' : s = (s * l⁻¹) * l := by group
  rw [hs', sup_comm]
  exact Subgroup.mul_mem_sup ⟨hcS, hc⟩ ⟨hl.1, hl.2⟩

theorem T_eq_sup_inf_centralizer (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    D.T = (D.T ⊓ c.L) ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) :=
  S_eq_sup_inf_centralizer D Ch h4 h23 h1930 c inf_le_left le_rfl

theorem isPGroup_inf_centralizer_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    IsPGroup 2 ↥(c.L ⊓ Subgroup.centralizer (c.V : Set G)) :=
  (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le
    (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c)

theorem pCoreOf_L_eq (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V)
    (hLV : c.L ≤ Subgroup.normalizer (c.V : Set G))
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)) :
    CFSG.Open.pCoreOf 2 c.L = c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
  have h := κ.blockQ_eq (isPGroup_inf_centralizer_L D Ch h4 h23 h1930 c)
  rwa [CFSG.AGLEmbedding.NoXBlock.blockQ_eq_map] at h

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
