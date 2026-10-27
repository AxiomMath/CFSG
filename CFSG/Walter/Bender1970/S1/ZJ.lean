module

public import CFSG.Walter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import CFSG.Walter.Bender1970.S1.QdNotInvolved
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3

public section

namespace CFSG.Walter

open Glauberman

private theorem zj_eq_self_of_isMulCommutative {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    [IsMulCommutative P] : ZJ P = P := by
  have hJ : thompsonSubgroup P = P :=
    le_antisymm (sSup_le fun _ hA => hA.1)
      (le_sSup ⟨le_rfl, inferInstance, fun _ hB _ => Subgroup.card_le_of_le hB⟩)
  change centerIn (thompsonSubgroup P) = P
  rw [hJ, centerIn]
  exact inf_eq_left.mpr (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)

private theorem zj_characteristic_of_two {G : Type*} [Group G] [Finite G]
    (hG : HasAbelianSylowTwo G) (P : Sylow 2 G)
    (hC : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    (ZJ (P : Subgroup G)).Characteristic := by
  have := hG P
  have hOP : pCore 2 G ≤ P := pCore_isPGroup.le_sylow_of_normal P
  have hPO : (P : Subgroup G) ≤ pCore 2 G :=
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr this).trans
      (Subgroup.centralizer_le hOP)).trans hC
  rw [zj_eq_self_of_isMulCommutative, le_antisymm hPO hOP]
  infer_instance

theorem bender1970_1_2_ZJ_characteristic
    {G : Type*} [Group G] [Finite G]
    (hG : HasAbelianSylowTwo G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hC : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G) :
    (Glauberman.ZJ (P : Subgroup G)).Characteristic := by
  by_cases hp2 : p = 2
  · subst hp2
    exact zj_characteristic_of_two hG P hC
  have hstab : pStable p ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G))) :=
    (lemma6_3 hp2).mp (qd_not_involved_of_hasAbelianSylowTwo hG hp2) ⊤ ⊥
  exact TheoremA.theoremA hp2 P
    ((pStable_iso (QuotientGroup.quotientBot.trans Subgroup.topEquiv)).mp hstab) hC

theorem bender1970_1_2_ZJ_normal
    {G : Type*} [Group G] [Finite G]
    (hG : HasAbelianSylowTwo G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hC : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G) :
    (Glauberman.ZJ (P : Subgroup G)).Normal :=
  have := bender1970_1_2_ZJ_characteristic hG P hC
  inferInstance

end CFSG.Walter
