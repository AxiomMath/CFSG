module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLow
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_sub_one_ne_two_five (m : ℕ) : 2 ^ m - 1 ≠ 2 ∧ 2 ^ m - 1 ≠ 5 := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;> norm_num
  · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    constructor <;> omega

theorem s23_8_SzLow_of_s21_15N_four {D : Data G} {Ch : Choice2011 G} (he : 3 < evenRank G)
    (hsig : D.sig.Nonempty) : S21_15N D Ch → S23_8_SzLow D Ch := by
  intro h15 h1930 c K hK a hSz hne ha hap r hr hrdvd _ _ _ _ _
  exfalso
  obtain ⟨p, hp⟩ := hsig
  have ha25 := two_pow_sub_one_ne_two_five (CFSG.Open.pRank 2 D.Z)
  have haodd : Odd a := hap.eq_two_or_odd'.resolve_left fun h2 => ha25.1 (ha.symm.trans h2)
  obtain ⟨A, hA, hAK⟩ := uc22ine229_exists_sub (Or.inr hSz) (dvd_refl a) hr hrdvd
  obtain ⟨-, -, hcase⟩ := h15 h1930 c.toCtx23.toCtx21 K hK a (Or.inr hSz) hne a haodd
    (dvd_refl a) r hr hrdvd p hp A hA hAK
  rcases hcase with ⟨he3, -⟩ | ⟨hL8, -⟩ | ⟨hSz5, -⟩
  · omega
  · exact P2214S.false_of_isSz_of_isL2 hSz hL8
  · have h5 := CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_twistedB2 hSz5
    have hfa := CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_twistedB2 hSz
    exact ha25.2 (ha.symm.trans (by omega))

theorem s23_8_SzLow_of_s21_15N_setup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {Ch : Choice2011 G} :
    S21_15N (UC6.dataOfSetup4 hS hU S) Ch → S23_8_SzLow (UC6.dataOfSetup4 hS hU S) Ch :=
  s23_8_SzLow_of_s21_15N_four (by have := hS.rank; omega)
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S).nonempty

end CFSG.LocalAnalysis.UniquenessCase.UC22
