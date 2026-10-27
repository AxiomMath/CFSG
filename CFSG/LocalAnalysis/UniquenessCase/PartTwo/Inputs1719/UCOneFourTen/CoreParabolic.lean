module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadicalSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.ParabolicDescent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.ParabolicRee
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSylowGrowth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreRadicalNormalizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenAbs
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem coreParabolicSlice_of_radicalSzComponent
    (hF3 : RadicalSzComponent) : CoreParabolicSlice := by
  intro X _ _ K L T Y n h hev hL2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm := h.lieModel_twistedF4 hF3 hev hL2
  have hK : CFSG.Blueprint.LieModel ↥K .twistedF4 0 2 n :=
    CFSG.Blueprint.LieModel.of_quotient_center
      (center_eq_bot_of_lieModel_twistedF4 h.quasisimple hm) hm
  obtain ⟨U, hU, hUK, -, hrad, hNLU, -, -, -, -, -, -⟩ := h.exists_radical_normalizer hL2
  have hU2 : IsPGroup 2 U := hrad ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hR : U.subgroupOf K ≠ ⊥ := by
    intro h0
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact hU (disjoint_self.mp (h0.mono_right hUK))
  have hR2 : IsPGroup 2 (U.subgroupOf K) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUK).symm
  have h5U := padicValNat_five_card_normalizer_le_of_twistedF4 hK hR hR2
  rw [card_normalizer_subgroupOf hUK] at h5U
  have h5LU : padicValNat 5 (Nat.card ↥(K ⊓ normalizer (L : Set X))) ≤
      padicValNat 5 (Nat.card ↥(K ⊓ normalizer (U : Set X))) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.padicValNat_le_of_dvd' (by norm_num)
      Nat.card_pos.ne' (Subgroup.card_dvd_of_le (inf_le_inf_left K hNLU))
  have hL5 := h.padicValNat_five_card_L
  have h1 := one_le_padicValNat_five_two_pow h.odd_three_le.1
  have hK5 : 2 * padicValNat 5 (2 ^ (2 * n) + 1) ≤ padicValNat 5 (Nat.card K) := by
    refine (padicValNat_dvd_iff_le Nat.card_pos.ne').mp ?_
    rw [pow_mul', pow_two]
    exact (mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd).trans
      ((pow_two (2 ^ (2 * n) + 1)) ▸ sq_dvd_card_of_lieModel_twistedF4 hK)
  have hgrow := h.lt_padicValNat_card_normalizer (r := 5) (by norm_num) (by norm_num)
    (dvd_of_one_le_padicValNat (hL5 ▸ h1)) (by omega)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
