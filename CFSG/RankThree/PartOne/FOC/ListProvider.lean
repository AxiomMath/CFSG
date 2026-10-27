module

public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Assembly

theorem sectionProviderK_list (hSLB : N143.SectionListBound) :
    SectionProviderK (fun _ _ _ _ J => Census3.TheoremThreeList (↥J ⧸ Subgroup.center ↥J)) := by
  intro G _ _ hev hKP d hd I hIC Γ _ _ φ p hp hp5 hloc hq hcat
  set L : Subgroup G := Subgroup.centralizer ({d} : Set G) with hL
  have hK : CFSG.IsKGroup ↥L := hKP L hd
  have heL : evenRank ↥L ≤ 3 :=
    (PlaneAux.evenRank_le_of_injective L.subtype (Subgroup.subtype_injective L)).trans hev
  let e : ↥(I.subgroupOf L) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIC
  let π : ↥(I.subgroupOf L) →* ↥φ.range := φ.rangeRestrict.comp e.toMonoidHom
  have hπ : Function.Surjective π :=
    (MonoidHom.rangeRestrict_surjective φ).comp e.surjective
  exact (hSLB ↥L hK heL (I.subgroupOf L) ↥φ.range hq π hπ).1

theorem sectionProviderK_listNative (hSLB : N143.SectionListBound) :
    SectionProviderK ListSec := by
  intro G _ _ hev hKP d hd I hIC Γ _ _ φ p hp hp5 hloc hq hcat
  have h := sectionProviderK_list hSLB G hev hKP d hd I hIC Γ φ p hp hp5 hloc hq hcat
  have : IsSimpleGroup (↥φ.range ⧸ Subgroup.center ↥φ.range) := hq.2.1
  exact Census3.TheoremThreeList.native h

end CFSG.RankThree.PartOne.FOC
