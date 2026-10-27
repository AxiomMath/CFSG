module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer
public import CFSG.RankThree.PartOne.SEITZ3.G2Odd
public import CFSG.RankThree.PartOne.CTP.SeitzFine
public import CFSG.RankThree.PartOne.SEITZ3.EvenFromMax
public import CFSG.RankThree.PartOne.SEITZ7.D4MaxArith

public section

namespace CFSG.RankThree.PartOne.SEITZ11

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K1214 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem extSeitzAtInnerFor_G2_odd_qplus
    {q : TauCeti.PrimePower} (hq : q.p ≠ 2)
    (hq11 : 11 ≤ q.card) : CTP.ExtSeitzAtInnerFor (.G2 q) fun p => ¬ p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := CTP.exists_adjointG2_model hiso
  have hXq : Nat.card X = q.card := by rw [hX, PrimePower.card_def]
  have : IsSimpleGroup (adjointGroup .G2 X) := MulEquiv.isSimpleGroup e.symm
  have hXodd : Odd (Nat.card X) := by
    rw [hX]
    exact (q.prime_p.odd_of_ne_two hq).pow
  have h11 : 11 ≤ Nat.card X := by rw [hXq]; exact hq11
  refine CTP.closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  by_cases hpq : p ∣ Nat.card X + 1
  · exact SEITZ11.G2Seven.closure_cenGen_adjointG2_odd_qplus_eq_top X hXodd h11 hp hp5 hpq E₁ hE₁p
      hcard₁
  · exfalso
    have hq1 : 1 ≤ Nat.card X := Nat.card_pos
    have hnd : ¬ p ∣ Nat.card X ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hq1]
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hP (by rwa [← hXq])
      · exact hpq h
    have hpQ : ¬ p ∣ Nat.card X := by
      intro h
      rw [hX] at h
      have h1 : p ∣ q.p := hp.dvd_of_dvd_pow h
      have h2 : p = q.p := (Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 h1
      exact hpd (h2.trans (LieTypeIndex.characteristic_G2 q).symm)
    have : Finite (ModGL .G2 X) := finite_modGL
    have hdvd : p ∣ Nat.card (adjointGroup .G2 X) := by
      have h1 := Subgroup.card_subgroup_dvd_card E₁
      rw [hcard₁] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have h1 := pRank_le_one_G2_odd X hXodd hp hp5 hpQ hdvd hnd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
    omega

theorem excG2Nonsplit_qplus
    (h1 : MaxSL2SL2G2) : CTP.ExcG2Nonsplit := by
  intro q hq
  by_cases h2' : q.p = 2
  · exact extSeitzAtInnerFor_G2_even h1 h2'
  · rcases hq with h' | ⟨-, h11⟩
    · exact absurd h' h2'
    · exact extSeitzAtInnerFor_G2_odd_qplus h2' h11

end CFSG.RankThree.PartOne.SEITZ11
