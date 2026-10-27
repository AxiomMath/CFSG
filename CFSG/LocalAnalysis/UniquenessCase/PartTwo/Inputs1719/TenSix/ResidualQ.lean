module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.ParThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QForms
import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsReeOver17)

private theorem aParam_eq_one_of_aSet_two_eq_empty {W : Type} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} (h2 : E3.aSet 2 Y = ∅) (hinv : ∃ t : ↥Y, orderOf t = 2) :
    E3.aParam Y = 1 := by
  classical
  obtain ⟨t, ht⟩ := hinv
  have h2Y : 2 ∣ Nat.card ↥Y := by
    have h := orderOf_dvd_natCard t
    rwa [ht] at h
  have hEvenY : Even (Nat.card Y) := even_iff_two_dvd.mpr h2Y
  have htW : orderOf (t : MulAut W) = 2 := (Subgroup.orderOf_coe t).trans ht
  have ht2 : (t : MulAut W) ^ 2 = 1 := by
    rw [← htW]
    exact pow_orderOf_eq_one _
  have hmem : Subgroup.zpowers (t : MulAut W) ∈ E3.aSet 1 Y := by
    rw [E3.aSet_one]
    refine ⟨Subgroup.zpowers_le.mpr t.2, ?_, CFSG.Quasithin.StabLat.isElemAbelian2_zpowers ht2⟩
    intro hbot
    have h1 : (t : MulAut W) = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [h1] at htW
    simp at htW
  have hset : {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty} = {1} := by
    ext k
    constructor
    · rintro ⟨hk, A, hA⟩
      have hk1 : k = 1 := by
        by_contra hne
        have hA2 := E3.aSet_anti (by omega : 2 ≤ k) Y hA
        rw [h2] at hA2
        exact hA2
      rw [hk1]
      rfl
    · intro hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨by norm_num, ⟨_, hmem⟩⟩
  rw [E3.aParam, if_pos hEvenY, hset, csSup_singleton]

private theorem exists_involution_of_isQuasisimple {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLq : IsQuasisimple ↥L) :
    ∃ t : ↥Y, orderOf t = 2 :=
  exists_prime_orderOf_dvd_card' 2
    ((E6.two_dvd_card_of_isQuasisimple hLq).trans (Subgroup.card_dvd_of_le hLY))


theorem w4Lem10_6_lieModel_of_three_lt {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {t : StatedLieTag} {n p e : ℕ}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel (↥L ⧸ Subgroup.center ↥L) t n p e) (hq3 : 3 < p ^ e) :
    (9 < p ^ e → E3.aParam Y = 1) ∧ E3.aParam Y ≤ 2 := by
  have hinv := exists_involution_of_isQuasisimple hLY hLq
  by_cases hL2 : IsL2Over17 (↥L ⧸ Subgroup.center ↥L) (p ^ e)
  · obtain ⟨r, f, -, hr2, hq, -, hmr⟩ := hL2
    rw [hq]
    exact w4Lem10_6_psl2 hW hLY hLn hF hLq hO2 hr2 hmr
  by_cases hRee : IsReeOver17 ↥L (p ^ e)
  · obtain ⟨m, hq, hRm⟩ := hRee
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hq] at hq3
        norm_num at hq3
      · exact h
    have h1 := aParam_eq_one_of_aSet_two_eq_empty
      (aSet_two_eq_empty_of_ree hW hm1 hLY hLn hF hRm) hinv
    exact ⟨fun _ => h1, h1.le.trans (by norm_num)⟩
  have h3 := aSet_eq_empty_of_not_l2_not_ree hW hLY hLn hF hLq hO2 hp hp2 hm hL2 hRee hq3
    (k := 3) (Or.inl le_rfl)
  refine ⟨fun h9 => ?_, RonanE42.aParam_le_of_aSet_empty Y 2 fun A hA => ?_⟩
  · exact aParam_eq_one_of_aSet_two_eq_empty
      (aSet_eq_empty_of_not_l2_not_ree hW hLY hLn hF hLq hO2 hp hp2 hm hL2 hRee hq3
        (k := 2) (Or.inr ⟨le_rfl, h9⟩)) hinv
  · rw [h3] at hA
    exact hA

theorem w4Lem10_6ResidualQ_holds : W4Lem10_6ResidualQ := by
  intro W _ _ hW Y L t n p e hLY hLn hF hLq hO2 hp hp2 _ _ hm hq3
  exact w4Lem10_6_lieModel_of_three_lt hW hLY hLn hF hLq hO2 hp hp2 hm hq3

theorem w4Lem10_6Q_holds : W4Lem10_6Q :=
  w4Lem10_6Q_of_residualQ w4Lem10_6ResidualQ_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
