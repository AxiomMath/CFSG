module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExcAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeSplitOn_exc :
    GGNbrTableBWeylTypeSplitOn fun p lab => ¬ lab.tag = .A ∧ ¬ lab.tag = .B ∧ ¬ lab.tag = .C ∧
      ¬ lab.tag = .D ∧ ¬ (lab.tag = .E6 ∧ p = 3) := by
  rintro p hp hp2 ⟨tag, l, n⟩ hlab ⟨hA, hB, hC, hD, hE6⟩ - hsp
  have hpn : p ∣ 2 ^ n - 1 := hsp.2.2
  cases tag with
  | A => exact (hA rfl).elim
  | B => exact (hB rfl).elim
  | C => exact (hC rfl).elim
  | D => exact (hD rfl).elim
  | E6 =>
    refine ggWTSX_largeEvenLabelAll_weylTypeW_excSplit hp hp2 hlab ?_
    exact ⟨Or.inl ⟨rfl, fun h => hE6 ⟨rfl, h⟩⟩, hpn⟩
  | E7 =>
    refine ggWTSX_largeEvenLabelAll_weylTypeW_excSplit hp hp2 hlab ?_
    exact ⟨Or.inr (Or.inl rfl), hpn⟩
  | E8 =>
    refine ggWTSX_largeEvenLabelAll_weylTypeW_excSplit hp hp2 hlab ?_
    exact ⟨Or.inr (Or.inr rfl), hpn⟩
  | F4 => exact ggWTSX_largeEvenLabelAll_weylTypeW_F4 hp hp2 hlab ⟨rfl, hpn⟩
  | G2 => exact ggWTSX_largeEvenLabelAll_weylTypeW_G2 hp hp2 hlab rfl hsp
  | twA | twD | twE6 | triD4 | twB2 | twF4 | twF4der => exact False.elim hsp.1
  | B2der | G2der =>
    have h1 : n = 1 := by
      obtain ⟨-, -, h⟩ := hlab
      exact h
    have h2 : 2 ≤ n := hsp.2.1
    omega

end CFSG.StandardType

end
