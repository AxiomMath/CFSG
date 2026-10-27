module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec119PSU8
import CFSG.RankThree.GF2n.Stroth80.Sec119Field
import CFSG.RankThree.GF2n.Stroth80.Sec119Filtration
import CFSG.RankThree.GF2n.Stroth80.Sec119OmegaCase
import CFSG.RankThree.GF2n.Stroth80.Sec119PslCase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

private theorem Ctx.false_of_cmOmegaFiltration {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hΩ : CMOmegaFiltration) (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hO : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)) : False := by
  have hx := hc.two_pow_eq_card_Z_of_omega hw ha2 hO
  obtain ⟨X₁, X₂, hZX₁, hX₁X₂, hX₂Q, hX₁c, rfl, hbr⟩ := hΩ G M Q Z B hc n m x hw hn ha2 hO hx
  have hX₁Z := hc.eq_Z_of_le_commXbarPre hZX₁ hX₁X₂ hX₁c
  rcases hbr with ⟨-, K, _, _, hK, X, hR, -⟩ |
    ⟨rfl, hU, ⟨K, _, _, hK, X, hR, -⟩ | ⟨K, _, _, hK, X, hR⟩⟩
  · rw [hX₁Z] at hR
    exact hc.false_of_omega_naturalRep hO hx hK hR
  · rw [hX₁Z] at hR
    exact hc.false_of_omega_naturalRep hO hx hK hR
  · exact hc.false_of_psu4_eight hw hn ha2 hx hU hZX₁ hX₁X₂ hX₂Q hX₁c rfl hK hR

theorem stroth119_of_cm
    (hΩ : CMOmegaFiltration) :
    Stroth119Statement := by
  intro G _ _ M Q Z B _ hc n hw hn ha2 hO
  obtain ⟨m, x, hP | hM | hL4 | hU⟩ := hO
  · exact (hc.false_of_cmOmegaFiltration hΩ hw hn ha2 (Or.inl hP)).elim
  · exact (hc.false_of_cmOmegaFiltration hΩ hw hn ha2 (Or.inr (Or.inl hM))).elim
  · exact hc.exists_psl4_of_lieModel hw ha2 hL4
  · exact (hc.false_of_cmOmegaFiltration hΩ hw hn ha2 (m := 3)
      (Or.inr (Or.inr ⟨rfl, hU⟩))).elim

end CFSG.RankThree.GF2n.Stroth80
