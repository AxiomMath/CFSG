module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallF4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallF4Disp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Quasithin.Background.SmithB42Disp
import CFSG.Quasithin.Background.HFF
import CFSG.Quasithin.H13.ExcludedOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Blueprint (LieModel)

theorem k14_5SmallFor_2f4 :
    K14_5SmallFor fun L _ e => LieModel L .twistedF4 0 2 e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  exfalso
  have hV : ∀ w : I, w * w = 1 := fun w => by rw [← pow_two]; exact hI w
  have hne : n = e := nParam_eq_of_twistedF4_parabolic hq hS hPL hpar hinf hN
  obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel hS (by decide)
  obtain ⟨a, K, _, _, _, ha, hea, hK, ⟨ε⟩⟩ := exists_mulEquiv_largeRee_model hR
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hea]
  have hevL : Even (Nat.card ↥L) := by
    obtain ⟨k, -, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel hR
    rw [hcard, ordTwistedF4]
    exact even_iff_two_dvd.2 (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _) _) _)
  have hev : Even (Nat.card ↥X) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hevL).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have htc : ∃ x ∈ L, t * x ≠ x * t := by
    by_contra hcon
    push Not at hcon
    exact ht1 (eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact htt) hcon)
  have hsimpL : IsSimpleGroup ↥L := uc22p22r_lieModel_isSimple_twistedF4 hS
  have hLodd : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N = ⊥ :=
    fun N hN hodd => eq_bot_of_odd_of_isSimpleGroup hevL N hN hodd
  obtain ⟨l, -, k, hyL, hy1, hy2⟩ := exists_involution_pow_mul_conj hLodd (hXN htX) htt htc
  have h4 := two_pow_le_index_pow_four_of_twistedF4 hV ha hK' ε hyL hy2 hy1
  have hyt : (fixV (zpowers ((t * (l⁻¹ * t * l)) ^ k))).index ≤
      (fixV (zpowers t)).index ^ 2 :=
    calc (fixV (zpowers ((t * (l⁻¹ * t * l)) ^ k))).index ≤
        (fixV (zpowers (t * (l⁻¹ * t * l)))).index :=
          CFSG.QuasithinUnique.Setup.X5.index_fixV_antitone
            ((zpowers_le).2 (pow_mem (mem_zpowers _) k))
      _ ≤ (fixV (zpowers t)).index ^ 2 := by
          simpa using B42Disp.index_fixV_prod_conj_le t [1, l⁻¹]
  have hIp : IsPGroup 2 I := fun w => ⟨1, by rw [pow_one]; exact hI w⟩
  have htidx : (fixV (zpowers t)).index = 2 ^ E3.mParam X := by
    rw [H.index_eq_two_pow_rkIdx hIp, htm]
  have hle : 2 ^ (12 * (2 * a + 1)) ≤ 2 ^ (8 * (n + 1)) :=
    calc 2 ^ (12 * (2 * a + 1)) ≤ (fixV (zpowers ((t * (l⁻¹ * t * l)) ^ k))).index ^ 4 := h4
      _ ≤ ((fixV (zpowers t)).index ^ 2) ^ 4 := Nat.pow_le_pow_left hyt 4
      _ = 2 ^ (8 * E3.mParam X) := by
          rw [htidx, ← pow_mul, ← pow_mul]
          ring_nf
      _ ≤ 2 ^ (8 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
