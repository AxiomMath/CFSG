module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue6
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open CFSG.LocalAnalysis.UniquenessCase

theorem r890_normalizer_le_of_le_sz {G : Type} [Group G] [Finite G] {D : Data G}
    (h847 : UC22.R847ThinNe3 D) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3) {J K : Subgroup G}
    (hJ : J ∈ calC D.M) {n m : ℕ} (hSzJ : IsSz (Bar2 J) n) (hKJ : K ≤ J) (hSzK : IsSz (Bar2 K) m) :
    normalizer (K : Set G) ≤ D.M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hthin : F08.Thin8 J := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.thin8_of_isSz hSzJ
  have hr : CFSG.Open.pRank 5 K ≤ 1 :=
    (CFSG.LocalAnalysis.GLTheoremA.H248.pRank_mono (by norm_num) hKJ).trans
      (hthin 5 (by norm_num) (by norm_num))
  have h5K : 5 ∣ Nat.card K :=
    (five_dvd_card_of_isSz hSzK).trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  set A : Subgroup G := Subgroup.zpowers (x : G) with hAdef
  have hAcard : Nat.card A = 5 := by
    rw [hAdef, Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hAK : A ≤ K := by
    rw [hAdef]
    exact Subgroup.zpowers_le.mpr x.2
  have hNA : normalizer (A : Set G) ≤ D.M :=
    UC22.normalizer_le_of_isSz_of_r847ThinNe3 h847 hp hp3 hJ hSzJ (hAK.trans hKJ)
      (by rw [hAcard]; norm_num)
      (by rw [hAcard]; norm_num)
  intro g hg
  have hgK : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hBK : A.map (MulAut.conj g).toMonoidHom ≤ K := by
    rw [← hgK]
    exact Subgroup.map_mono hAK
  obtain ⟨l, hlK, hl⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime (p := 5) hr hAK hBK
      hAcard (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard])
  have hgm : l⁻¹ * g ∈ normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show A.map (MulAut.conj (l⁻¹ * g)).toMonoidHom = A
    rw [← CFSG.RankThreeCoreUniqueness.Helpers.conjugate_map_mul A l⁻¹ g, ← hl,
      CFSG.RankThreeCoreUniqueness.Helpers.conjugate_map_mul A l⁻¹ l, inv_mul_cancel]
    ext y
    simp
  have hM1 : l⁻¹ * g ∈ D.M := hNA hgm
  have hM2 : l ∈ D.M := hJ.1.le (hKJ hlK)
  have hgmem : l * (l⁻¹ * g) ∈ D.M := D.M.mul_mem hM2 hM1
  rwa [mul_inv_cancel_left l g] at hgmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
