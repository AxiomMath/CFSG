module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Cop
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Lin
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125W

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification

theorem res3NoDatumL3Odd_holds : Res3NoDatumL3Odd := by
  intro J _ _ _ hq p e _ hp5 he hiso c g V U hd
  haveI : Group.IsPerfect J := hq.1
  let Φ : MulAut J →* MulAut (J ⧸ Subgroup.center J) :=
    PerfectAutomorphisms.centerQuotientHom J
  have hΦ : Function.Injective Φ := PerfectAutomorphisms.centerQuotientHom_injective J
  have hZ : Subgroup.center (J ⧸ Subgroup.center J) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot J
  have hα : Φ g ∈ Subgroup.normalizer ((V.map Φ : Subgroup (MulAut (J ⧸ Subgroup.center J))) :
      Set (MulAut (J ⧸ Subgroup.center J))) :=
    V.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ hd.g_mem)
  have hcop : Nat.Coprime (orderOf (Φ g)) 6 := by
    rw [orderOf_injective Φ hΦ g]
    exact hd.coprime_six
  have hcent := res3L125_centralizes_of_normalizes hZ
    (res3L125_odd_commutator_outer hp5 he hiso) (res3L125_abelian_index_le_two hp5 he hiso)
    (res3L125_card_elemAbelian_le_four hp5 he hiso)
    (fun R _ _ hR A hA hidx hE β hβ => res3L125_eq_one_of_coprime_six hR hA hidx hE hβ)
    (hd.V_isPGroup.map Φ) hα hcop
  have hgV : ∀ v ∈ V, g * v = v * g := fun v hv => hΦ (by
    rw [map_mul, map_mul]
    exact hcent (Φ v) (Subgroup.mem_map_of_mem Φ hv))
  apply hd.U_ne
  rw [← hd.U_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
    Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hgV u (hd.U_le hu)).symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
