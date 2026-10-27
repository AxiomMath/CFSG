module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43m
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43d
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43h

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

@[expose] def S43_CommThetaAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → CommTheta b b₁ b₂

theorem S43_Tstar_of_commTheta
    (h23 : FF84_2_3)
    (hct : S43_CommThetaAll) (hR : S43_TstarCen₁) : S43_Tstar := by
  intro G _ _ b L B K b₁ b₂ h V hV hVne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := a8Model_of_hyp h.hyp
  have hC := hct G b L B K b₁ b₂ h
  haveI := isElemAb_E h
  have hET : Subgroup.closure ({b, b₁} : Set G) ≤ Nor (Op 2 (Nor V)) := fun e he =>
    FF79.L41.mem_nor_of_forall (fun z hz => Tstar_B_inv hA h hV z hz e (E_le_B h he))
  have hgen := B_gen_centralizers (E := Subgroup.closure ({b, b₁} : Set G)) (X := Op 2 (Nor V))
    (card_E_ge h) (FF79.L41.Op_isPGroup _) hET
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  rcases E_four h ha ha1 with h1 | h1 | h1 | h1
  · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (tstar_cen_b hA h hV)
  · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
      (hR G b L B K b₁ b₂ h V hV hVne)
  · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (tstar_cen_bb₁ h23 hA h hC hV)
  · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans (tstar_cen_bb₁sq h23 hA h hC hV)

theorem S43_odd_of_commTheta
    (h23 : FF84_2_3)
    (hct : S43_CommThetaAll) (hR : S43_TstarCen₁) : S43_odd :=
  S43_odd_of_rest fun G _ _ b L B K b₁ b₂ h =>
    ⟨hct G b L B K b₁ b₂ h,
      S43_tail_of_Tstar (S43_Tstar_of_commTheta h23 hct hR) G b L B K b₁ b₂ h⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
