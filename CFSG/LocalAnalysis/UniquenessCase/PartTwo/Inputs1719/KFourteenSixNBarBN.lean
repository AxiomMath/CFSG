module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.SplitBNPair
import CFSG.Milestones.ASVolI.I2
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open CFSG.Blueprint CFSG.Open

theorem exists_splitBNPair_of_lieModel {L : Type} [Group L] [Finite L] {t : StatedLieTag}
    {n p f : ℕ} (hL : LieModel L t n p f)
    (ht : (t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3)) :
    p.Prime ∧ p ∣ Nat.card L ∧ ∃ B N : Subgroup L, CFSG.ASVolI.ChIJK.IsSplitBNPair p B N := by
  have htc : t ∈ classicalTags := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hc := hL.statedClassicalModel htc
  have hp : p.Prime := hc.1.1
  have hf : 1 ≤ f := hc.1.2.1
  have hn : 2 ≤ n := by
    rcases ht with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  have hmin : EvenSmallLie.CatalogOrders.lieMin t ≤ n := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact hn
    · decide
  have hexp : 1 ≤ EvenSmallLie.CatalogOrders.lieExp t n :=
    EvenSmallLie.CatalogOrders.one_le_lieExp (by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
      hmin
  refine ⟨hp, ?_, ?_⟩
  · rw [hL.card_eq_lieOrd (by omega)]
    exact ((dvd_pow_self p (by omega)).trans (dvd_pow_self (p ^ f) (by omega))).trans
      (EvenSmallLie.CatalogOrders.pow_lieExp_dvd hmin (p ^ f))
  · rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact CFSG.ASVolI.ChIJK.burnsideI2BN_PSL hp hc.1 hc
    · exact CFSG.ASVolI.ChIJK.burnsideI2BN_PSU hp hc.1 hc

theorem sq_sub_one_dvd_of_lieModel {L : Type} [Group L] [Finite L] {t : StatedLieTag}
    {n p f : ℕ} (hL : LieModel L t n p f)
    (ht : (t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3)) :
    p ^ 2 - 1 ∣ 6 * Nat.card L := by
  have hn : 2 ≤ n := by
    rcases ht with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  have hn6 : n ∣ 6 := by
    rcases ht with ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hpq : p ^ 2 - 1 ∣ (p ^ f) ^ 2 - 1 := by
    rw [show (p ^ f) ^ 2 = (p ^ 2) ^ f by ring]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (p ^ 2) 1 f
  refine hpq.trans ?_
  rw [hL.card_eq_lieOrd (by omega)]
  set q := p ^ f
  have key : ∀ {M d : ℕ}, d ∣ M → d ∣ 6 → q ^ 2 - 1 ∣ M → q ^ 2 - 1 ∣ 6 * (M / d) := by
    intro M d hdM hd6 hqM
    refine hqM.trans ?_
    calc M = M / d * d := (Nat.div_mul_cancel hdM).symm
      _ ∣ M / d * 6 := Nat.mul_dvd_mul_left _ hd6
      _ = 6 * (M / d) := mul_comm _ _
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp only [EvenSmallLie.CatalogOrders.lieOrd]
    unfold ordA
    rw [hn1]
    have hP : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
      Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
    exact key ((Nat.gcd_dvd_right _ _).trans
      ((EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q).trans (hP.mul_left _)))
      ((Nat.gcd_dvd_left _ _).trans hn6) (hP.mul_left _)
  · simp only [EvenSmallLie.CatalogOrders.lieOrd]
    unfold ordTwistedA
    rw [hn1]
    have hP : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
      rw [← EvenSmallLie.CatalogOrders.toNat_sq_sub_neg_one_sq]
      exact Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
        (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
    exact key ((Nat.gcd_dvd_right _ _).trans
      ((EvenSmallLie.CatalogOrders.add_one_dvd_sq_sub_one q).trans (hP.mul_left _)))
      ((Nat.gcd_dvd_left _ _).trans hn6) (hP.mul_left _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
