module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Model
import CFSG.RankThree.PartTwo.Sec19.SimsC198U48
import CFSG.RankThree.PartTwo.Sec19.SimsC198AutCrit
import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

theorem noAutDatum_SU4 : NoAutDatum SU4 := by
  intro c L 𝒟 h
  haveI : IsSimpleGroup SU4 := isSimpleGroup_SU4
  have hL7560 : 7560 ≤ Nat.card L :=
    (IsType198.le_card h.quasisimple h.type).trans
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
  obtain ⟨h19, hθ, hD⟩ := u48_component h.orderOf_eq h.le_centralizer h.subnormal h.perfect
    h.mem h.toLocalDatum.exists_nonabelian hL7560
  have hfix : fixIn 𝒟 L = L := h.fixIn_eq hθ
  by_cases hinn : 𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner SU4
  · have hZ := h.center_eq_bot
    have h9 : Nat.card (𝒟.comap (MulAut.conj : SU4 →* MulAut SU4)) = 9 :=
      (card_comap_conj hZ hinn).trans h.card
    have hle := comap_conj_le_centralizer 𝒟 L
    rw [hfix] at hle
    have := hD _ hle (isElemAbelian_comap_conj hZ h.comm h.pow_three)
    omega
  · obtain ⟨φ, hφ, hout⟩ := SetLike.not_le_iff_exists.mp hinn
    refine u48_not_dvd_of_outer φ (h.pow_three φ hφ) hout L (fun l hl => ?_) h19
    rw [← hfix] at hl
    exact (mem_fixIn.mp hl).2 φ hφ

theorem noAutDatum_of_U48 {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 3) : NoAutDatum S :=
  NoAutDatum.of_mulEquiv (e.trans equivSU4) noAutDatum_SU4

end CFSG.RankThree.PartTwo.Sec19.SimsC198
