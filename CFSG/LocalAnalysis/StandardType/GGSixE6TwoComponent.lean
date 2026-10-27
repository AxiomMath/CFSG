module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section Component

theorem eq_lE_of_isComponentOf {L' : Subgroup EC}
    (h : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({zE} : Set EC))) : L' = lE := by
  set Z : Subgroup EC := Subgroup.centralizer ({zE} : Set EC) with hZdef
  have hZ : Z = Subgroup.zpowers zE ⊔ lE := by rw [hZdef]; exact centralizer_zE.1
  have hlE_le_Z : lE ≤ Z := by rw [hZ]; exact le_sup_right
  have hzp_le_Z : Subgroup.zpowers zE ≤ Z := by rw [hZ]; exact le_sup_left
  have hZ_norm : Z ≤ Subgroup.normalizer (lE : Set EC) := by
    rw [hZ]
    exact sup_le
      (centralizer_zE.2.2.trans (Subgroup.centralizer_le_normalizer (lE : Set EC)))
      (Subgroup.le_normalizer (H := lE))
  have hNnormal : (lE.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hlE_le_Z).2 hZ_norm
  have hsup : (lE.subgroupOf Z) ⊔ (Subgroup.zpowers zE).subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hlE_le_Z hzp_le_Z, Subgroup.subgroupOf_eq_top]
    simpa [sup_comm] using (le_of_eq hZ)
  haveI : (lE.subgroupOf Z).Normal := hNnormal
  haveI : IsMulCommutative (Subgroup.zpowers zE) := Subgroup.zpowers_isMulCommutative zE
  have hHcomm : IsMulCommutative ((Subgroup.zpowers zE).subgroupOf Z) :=
    Subgroup.subgroupOf_isMulCommutative Z (Subgroup.zpowers zE)
  have hcommZ : _root_.commutator ↥Z ≤ lE.subgroupOf Z :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hHcomm
  have hcommZ' : ⁅Z, Z⁆ ≤ lE := by
    have hmap : (_root_.commutator ↥Z).map Z.subtype ≤ (lE.subgroupOf Z).map Z.subtype :=
      Subgroup.map_mono (f := Z.subtype) hcommZ
    rw [Subgroup.map_subtype_commutator Z, Subgroup.map_subgroupOf_eq_of_le hlE_le_Z] at hmap
    exact hmap
  have hL'eq : L' = ⁅L', L'⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_le_self L')
    rw [← Subgroup.map_subtype_commutator L', h.2.2.1, Subgroup.map_top]
    exact le_of_eq (Subgroup.range_subtype L').symm
  have hL'_le_lE : L' ≤ lE :=
    hL'eq.le.trans ((Subgroup.commutator_mono h.1 h.1).trans hcommZ')
  have hsn : CFSG.Assembly.IsSubnormal L' Z := h.2.1
  have hsub : CFSG.Assembly.IsSubnormal L' lE := by
    have h' := hsn.inf_of_le hlE_le_Z
    rwa [inf_eq_left.2 hL'_le_lE] at h'
  have hne : L' ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥L' := by rw [hbot]; infer_instance
    haveI : IsSimpleGroup (↥L' ⧸ Subgroup.center ↥L') := h.2.2.2
    haveI : Nontrivial (↥L' ⧸ Subgroup.center ↥L') := inferInstance
    haveI : Subsingleton (↥L' ⧸ Subgroup.center ↥L') := inferInstance
    obtain ⟨a, b, hab⟩ :=
      (inferInstance : Nontrivial (↥L' ⧸ Subgroup.center ↥L')).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  rcases CFSG.Assembly.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub isSimpleGroup_lE with
    hb | he
  · exact absurd hb hne
  · exact he

end Component

end CFSG.StandardType.GGSixE6Two
