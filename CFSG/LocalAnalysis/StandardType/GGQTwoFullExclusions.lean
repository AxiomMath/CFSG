module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem index_le_three_pow_five_of_E6_marking {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index ≤ 3 ^ 5 := by
  classical
  obtain ⟨-, labM, hlabM, hrawM⟩ := hmark
  obtain ⟨-, -, -, -, -, -, -, hlabEq, -, -⟩ := largeEvenRawDatum_exists hrawM
  have hn1 : labM.n = 1 := by
    have hlt : labM.n < 2 := by rw [hlabEq]; exact hq2
    have hn : 1 ≤ labM.n := hlabM.1
    omega
  have htagM : labM.tag = .E6 := by rw [hlabEq]; exact htag
  rw [LargeEvenRawDatumLegacy, htagM] at hrawM
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hrawM
  letI := hfield
  letI := hfinite
  have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
  obtain ⟨-, -, θ, -, hN, -⟩ := hQ
  let θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E6 K := θ
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hL : commutator L = ⊤ := hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.2.1
  have hE : IsElemAbelian 3 (ggBeta L θ' hN).range :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.property)) (ggBeta L θ' hN)
  have hbound := TableBExc.E6Three.card_le_of_isElemAbelian_aut_E6_two hK2 hE
  rwa [beta_card hL θ' hN] at hbound

theorem not_full_E6_of_marking {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index ≠ 3 ^ GGQ2LieRank lab := by
  intro hidx
  have hbound := index_le_three_pow_five_of_E6_marking hS hq2 htag hmark
  rw [hidx, GGQ2LieRank, htag] at hbound
  norm_num at hbound

end CFSG.StandardType.QTwoCav

end
