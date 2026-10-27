module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kSporadicThreeRank_holds :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KSporadicThreeRank := by
  intro X _ _ s h
  have hEq : CFSG.pRank 3 (↥(⊤ : Subgroup X)) = CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]
  rw [hEq]
  cases s with
  | M11 =>
    have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      two_le_pRank_three_of_isSpor_M11 h
    obtain ⟨e⟩ := h
    have hcardX : Nat.card X = 7920 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M11
    have hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
      refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
      rw [hcardX]
      norm_num
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := le_antisymm hup hlow
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | M12 =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .M12) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 95040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M12
    have hcardC : Nat.card (Carrier .M12) = 95040 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .M12)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.M12_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .M12) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .M12) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .M12)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .M12)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | M22 =>
    have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      two_le_pRank_three_of_isSpor_M22 h
    obtain ⟨e⟩ := h
    have hcardX : Nat.card X = 443520 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    have hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
      refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
      rw [hcardX]
      norm_num
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := le_antisymm hup hlow
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | M23 =>
    have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      two_le_pRank_three_of_isSpor_M23 h
    obtain ⟨e⟩ := h
    have hcardX : Nat.card X = 10200960 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Schreier.m23_card
    have hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
      refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
      rw [hcardX]
      norm_num
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := le_antisymm hup hlow
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | M24 =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .M24) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 244823040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    have hcardC : Nat.card (Carrier .M24) = 244823040 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .M24)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.M24_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .M24) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .M24) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .M24)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .M24)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | J1 =>
    obtain ⟨e⟩ := h
    have hcardX : Nat.card X = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    have hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
      refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
      rw [hcardX]
      norm_num
    have hlow : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcardX]; norm_num)
      exact CFSG.Quasithin.A3Facts.one_le_pRank_of_orderOf Nat.prime_three hx
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := le_antisymm hup hlow
    refine ⟨?_, ?_⟩ <;> simp [hX]
  | J2 =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .J2) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    have hcardC : Nat.card (Carrier .J2) = 604800 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .J2)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.J2_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .J2) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .J2) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .J2)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .J2)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | J3 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.J3_elementary_three_rank_three
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 3 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
        (k := 3) (by norm_num) le_top hE' hcard'
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | J4 =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .J4) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 86775571046077562880 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    have hcardC : Nat.card (Carrier .J4) = 86775571046077562880 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .J4)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.J4_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .J4) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .J4) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .J4)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .J4)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | HS =>
    have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      two_le_pRank_three_of_isSpor_HS h
    obtain ⟨e⟩ := h
    have hcardX : Nat.card X = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    have hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
      refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
      rw [hcardX]
      norm_num
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := le_antisymm hup hlow
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | McL =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | He =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .He) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 4030387200 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.He.card_He
    have hcardC : Nat.card (Carrier .He) = 4030387200 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .He)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.He_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .He) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .He) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .He)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .He)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Ru =>
    obtain ⟨e⟩ := h
    haveI : Finite (Carrier .Ru) := Finite.of_equiv X e.toEquiv
    have hcardX : Nat.card X = 145926144000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    have hcardC : Nat.card (Carrier .Ru) = 145926144000 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardX
    have hfac : (Nat.card (Carrier .Ru)).factorization 3 = 3 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
        Nat.prime_three (by rw [hcardC]; norm_num)
        ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
      CFSG.SectionRank.Ru_sylow3_cubic_witness
    have h2c : CFSG.pRank 3 (Carrier .Ru) = 2 :=
      CFSG.RankThree.Asc83Table.ex27_pRank (L := Carrier .Ru) hx hy hzx hzy hz hfac
    have h2o : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .Ru)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Carrier .Ru)).symm.trans h2c
    have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2o
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Suz =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Suz_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | ONan =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Co1 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Co1_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Co2 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Co2_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Co3 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Co3_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Fi22 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Fi22_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Fi23 =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Fi23_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Fi24Prime =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Fi24prime_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | HN =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.HN_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Ly =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Ly_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | Th =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Th_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | B =>
    obtain ⟨e⟩ := h
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.B_elementary_three_rank_four
    have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
    have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
    have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
      rw [hmap, hcard]
    have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      le_trans (by norm_num : 3 ≤ 4)
        (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
          (k := 4) (by norm_num) le_top hE' hcard')
    refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
  | M =>
    obtain ⟨e⟩ := h
    by_cases hnt : Nontrivial (Carrier .M)
    · letI : Nontrivial CFSG.Blueprint.NativeSporadic.M := hnt
      obtain ⟨E, hE, hcard⟩ :=
        CFSG.SectionRank.M_nontrivial_elementary_three_rank_four
      have hE' : IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
        CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom
      have hmap : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
        Nat.card_congr
          (Subgroup.equivMapOfInjective E e.symm.toMonoidHom e.symm.injective).symm.toEquiv
      have hcard' : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
        rw [hmap, hcard]
      have hX : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
        le_trans (by norm_num : 3 ≤ 4)
          (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E.map e.symm.toMonoidHom)
            (k := 4) (by norm_num) le_top hE' hcard')
      refine ⟨?_, ?_⟩ <;> simp [hX] <;> omega
    · haveI : Subsingleton (Carrier .M) := not_nontrivial_iff_subsingleton.mp hnt
      haveI : Subsingleton X := e.toEquiv.subsingleton
      have hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        refine CFSG.SectionRank.pRank_le (p := 3) (H := ⊤) (k := 0) (by norm_num) ?_
        intro E _ _
        simpa using (Nat.card_le_one : Nat.card E ≤ 1)
      refine ⟨?_, ?_⟩ <;> simp [hX]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
