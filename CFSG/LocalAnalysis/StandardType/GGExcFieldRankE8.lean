module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Seven
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Nine
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Fourteen
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Fifteen
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eighteen
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twenty
public import CFSG.LieType.SeitzGeneration.ExcTorusE8TwentyFour
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Thirty
public import CFSG.LieType.SeitzGeneration.ExcTorusE8One
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Six
public import CFSG.LieType.SeitzGeneration.ExcTorusThree
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8RestTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Open (IsElemAbelian)

theorem ggE8FiveFourRankLE :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 →
      GGElemAbelianRankLE (adjointGroup .E8 K) 5 4 := by
  intro K _ _ _ he E hE
  by_cases hE4 : 5 ^ 4 ≤ Nat.card E
  · obtain ⟨A, hAel, hAcard⟩ := exists_elemAbelian_E8_four K Nat.prime_five he
    have hA4 : 5 ^ 4 ≤ Nat.card A := by rw [hAcard]
    obtain ⟨c, hc⟩ := CFSG.StandardType.NoOffE8Five.exists_conj_map_eq_E8_five
      (by simpa [pow_two] using dvd_sq_add_one_of_orderOf_eq_four Nat.prime_five he)
      hE hAel hE4 hA4
    have hEq : Nat.card E = 5 ^ 4 := by
      calc Nat.card E = Nat.card (E.map (MulAut.conj c).toMonoidHom) :=
            (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
        _ = Nat.card A := by rw [hc]
        _ = 5 ^ 4 := hAcard
    omega
  · omega

private theorem excToralRankInput_E8_of_dvd {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K p := by
  by_cases hp3 : p = 3
  · subst hp3
    exact TableBExc.Three.ggExcToralRankInput_E8_three hpq
  · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hpq

theorem rankLE_E8 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGElemAbelianRankLE (adjointGroup .E8 K) p (degCount .E8 e) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hncard⟩ := FiniteField.card (K := K) 2
  have hKpow : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hncard
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hKpow]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have he0 : e ≠ 0 := by
    rw [← he]
    exact orderOf_natCast_ne_zero hp hpq
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  intro E hE
  by_cases h0 : degCount .E8 e = 0
  ·
    have he_ne : e ≠ 1 ∧ e ≠ 2 := by
      constructor
      · intro h1
        rw [h1] at h0
        exact absurd h0 (by decide)
      · intro h2
        rw [h2] at h0
        exact absurd h0 (by decide)
    have he3 : 3 ≤ e := by
      have hpos : 1 ≤ e := Nat.pos_of_ne_zero he0
      omega
    have hlt : e < p := orderOf_lt_prime hp hpq he
    have hp3 : 3 < p := by omega
    have hE1 : Nat.card E = 1 :=
      elemAbelian_card_eq_one_of_degCount_zero (τ := .E8) (by simp) K hp hp3 hpq he h0 hE
    rw [hE1, h0, pow_zero]
  · by_cases h1 : degCount .E8 e = 1
    ·
      have hcnt : degCount .E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by
        rw [he]
        omega
      have hcard := rankLE1_E8 K hp hpq hcnt E hE
      rw [h1]
      simpa using hcard
    · by_cases h2 : degCount .E8 e = 2
      ·
        have h30 := le_thirty_of_degCount_pos (τ := .E8) (by simp) (by rw [h2]; norm_num)
        have key : ∀ o ≤ 30, degCount .E8 o = 2 → o = 5 ∨ o = 8 ∨ o = 10 ∨ o = 12 := by
          decide
        rcases key e h30 h2 with rfl | rfl | rfl | rfl
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_five K hp he
          have hcard := hS.rank_le hp hE
          rw [h2]
          simpa using hcard
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_eight K hp he
          have hcard := hS.rank_le hp hE
          rw [h2]
          simpa using hcard
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_ten K hp he
          have hcard := hS.rank_le hp hE
          rw [h2]
          simpa using hcard
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_twelve K hp he
          have hcard := hS.rank_le hp hE
          rw [h2]
          simpa using hcard
      ·
        have hcnt3 : 3 ≤ degCount .E8 e := by omega
        have hdvd : e ∣ p - 1 := by
          haveI : Fact p.Prime := ⟨hp⟩
          have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h0 =>
            hpq ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h0)
          exact he ▸ ZMod.orderOf_dvd_card_sub_one hq0
        rcases eq_of_three_le_degCount_E8 hcnt3 with he1 | he2 | he3 | he4 | he6
        ·
          have hpq1 : p ∣ Nat.card K - 1 := by
            have h := (dvd_pow_sub_one_iff_orderOf (d := 1) hq he).2 (by
              simpa [he1] using dvd_refl 1)
            simpa using h
          have hT := excToralRankInput_E8_of_dvd (K := K) hp hp2 hpq1
          have hcard := hT.card_le (TableBExc.card_torusPow_E8 hp hpq1) hE
          have hrank : Tag.E8.rank = 8 := by decide
          rw [hrank] at hcard
          have hdeg : degCount .E8 e = 8 := by rw [he1]; decide
          rw [hdeg]
          simpa using hcard
        ·
          have hpq2 : p ∣ Nat.card K ^ 2 - 1 := by
            have h := (dvd_pow_sub_one_iff_orderOf (d := 2) hq he).2 (by
              simpa [he2] using dvd_refl 2)
            simpa using h
          let L := GaloisField 2 (2 * (n : ℕ))
          haveI : Fintype L := Fintype.ofFinite L
          have hLne : 2 * (n : ℕ) ≠ 0 := by
            have := PNat.ne_zero n
            omega
          have hLcard : Nat.card L = 2 ^ (2 * (n : ℕ)) := GaloisField.card 2 _ hLne
          haveI : CharP L 2 :=
            charP_of_card_eq_prime_pow (f := 2 * (n : ℕ)) (by
              rw [← Nat.card_eq_fintype_card, hLcard])
          have hLsq : Nat.card L = (Nat.card K) ^ 2 := by
            rw [hLcard, hKpow, ← pow_mul]
            congr 1
            ring
          have hpqL : p ∣ Nat.card L - 1 := by
            rw [hLsq]
            exact hpq2
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨ι⟩ :=
            CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq
              (ℓ := 2) (f := (n : ℕ)) (k := K) (K := L) hKpow (by rw [hLsq, hKpow])
          have hinj : Function.Injective (TableBExcTwo.adjointMap .E8 ι) :=
            TableBExcTwo.adjointMap_injective ι
          have hmapE : IsElemAbelian p (E.map (TableBExcTwo.adjointMap .E8 ι)) := hE.map _
          have hT := excToralRankInput_E8_of_dvd (K := L) hp hp2 hpqL
          have hcard := hT.card_le (TableBExc.card_torusPow_E8 hp hpqL) hmapE
          rw [Subgroup.card_map_of_injective hinj] at hcard
          have hrank : Tag.E8.rank = 8 := by decide
          rw [hrank] at hcard
          have hdeg : degCount .E8 e = 8 := by rw [he2]; decide
          rw [hdeg]
          simpa using hcard
        ·
          have h3dvd : 3 ∣ p - 1 := by rw [← he3]; exact hdvd
          have hp7 : 7 ≤ p := by
            have h2le := hp.two_le
            by_contra h
            interval_cases p
            · exact hp2 rfl
            · exact absurd h3dvd (by norm_num)
            · exact absurd hp (by norm_num)
            · exact absurd h3dvd (by norm_num)
            · exact absurd hp (by norm_num)
          have hS : SylowTorus (adjointGroup .E8 K) p 4 :=
            ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq
              (Or.inl (by rw [he, he3]))
          have hcard := hS.rank_le hp hE
          have hdeg : degCount .E8 e = 4 := by rw [he3]; decide
          rw [hdeg]
          simpa using hcard
        ·
          have hdeg : degCount .E8 e = 4 := by rw [he4]; decide
          rw [hdeg]
          by_cases hp5 : p = 5
          · subst hp5
            have he' : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 := by rw [he, he4]
            exact ggE8FiveFourRankLE K he' E hE
          · have h4dvd : 4 ∣ p - 1 := by rw [← he4]; exact hdvd
            have hp7 : 7 ≤ p := by
              have h2le := hp.two_le
              by_contra h
              interval_cases p
              · exact hp2 rfl
              · exact absurd h4dvd (by norm_num)
              · exact absurd hp (by norm_num)
              · exact hp5 rfl
              · exact absurd hp (by norm_num)
            have hS : SylowTorus (adjointGroup .E8 K) p 4 :=
              ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq
                (Or.inr (Or.inl (by rw [he, he4])))
            exact hS.rank_le hp hE
        ·
          have h6dvd : 6 ∣ p - 1 := by rw [← he6]; exact hdvd
          have hp7 : 7 ≤ p := by
            have hpos : 0 < p - 1 := by
              have h2 := hp.two_le
              omega
            have hle := Nat.le_of_dvd hpos h6dvd
            omega
          have hS : SylowTorus (adjointGroup .E8 K) p 4 :=
            ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq
              (Or.inr (Or.inr (by rw [he, he6])))
          have hcard := hS.rank_le hp hE
          have hdeg : degCount .E8 e = 4 := by rw [he6]; decide
          rw [hdeg]
          simpa using hcard

theorem exists_E8 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGExcElemAbelianExists (adjointGroup .E8 K) p (degCount .E8 e - 1) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hncard⟩ := FiniteField.card (K := K) 2
  have hKpow : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hncard
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hKpow]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have he0 : e ≠ 0 := by
    rw [← he]
    exact orderOf_natCast_ne_zero hp hpq
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  by_cases h0 : degCount .E8 e = 0
  ·
    refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
    rw [h0]
    simp
  · by_cases h1 : degCount .E8 e = 1
    ·
      refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
      rw [h1]
      simp
    · by_cases h2 : degCount .E8 e = 2
      ·
        have h30 := le_thirty_of_degCount_pos (τ := .E8) (by simp) (by rw [h2]; norm_num)
        have key : ∀ o ≤ 30, degCount .E8 o = 2 → o = 5 ∨ o = 8 ∨ o = 10 ∨ o = 12 := by
          decide
        rcases key e h30 h2 with rfl | rfl | rfl | rfl
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_five K hp he
          obtain ⟨E, hE, hcard⟩ := hS.exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, h2]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2)
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_eight K hp he
          obtain ⟨E, hE, hcard⟩ := hS.exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, h2]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2)
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_ten K hp he
          obtain ⟨E, hE, hcard⟩ := hS.exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, h2]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2)
        · have hS : SylowTorus (adjointGroup .E8 K) p 2 := sylowTorus_E8_twelve K hp he
          obtain ⟨E, hE, hcard⟩ := hS.exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, h2]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2)
      ·
        have hcnt3 : 3 ≤ degCount .E8 e := by omega
        rcases eq_of_three_le_degCount_E8 hcnt3 with he1 | he2 | he3 | he4 | he6
        ·
          by_cases hp3 : 3 < p
          · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E8_one K hp hp3 (by rw [he, he1])
            refine ⟨E, hE, ?_⟩
            rw [hcard]
            have hdeg : degCount .E8 e = 8 := by rw [he1]; decide
            rw [hdeg]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 7 ≤ 8)
          ·
            have hp_eq : p = 3 := by
              have hp2le := hp.two_le
              omega
            subst hp_eq
            have hrat := relIndex_dvd_untwisted 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K
            obtain ⟨E, hE, hle⟩ :=
              exists_elemAbelian_three_of_blocks (d := 1) (by norm_num) K hrat
                (IsWeylMatrix.of_word .E8 e8OneWord) [1, 1, 1, 1, 1, 1, 1, 1]
                e8One_charpoly e8One_pow (by rw [he, he1]) (by norm_num) (by decide)
            refine ⟨E, hE, ?_⟩
            have hcard : 3 ^ 7 ≤ Nat.card E := by
              have h1' : (3 : ℕ) ^ 8 ≤ 1 * Nat.card E := by simpa using hle
              have h1'' : (3 : ℕ) ^ 8 ≤ Nat.card E := by simpa using h1'
              calc (3 : ℕ) ^ 7 ≤ 3 ^ 8 := by norm_num
                _ ≤ Nat.card E := h1''
            have hdeg : degCount .E8 e = 8 := by rw [he1]; decide
            rw [hdeg]
            simpa using hcard
        ·
          by_cases hp3 : 3 < p
          · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E8_two K hp hp3 (by rw [he, he2])
            refine ⟨E, hE, ?_⟩
            rw [hcard]
            have hdeg : degCount .E8 e = 8 := by rw [he2]; decide
            rw [hdeg]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 7 ≤ 8)
          ·
            have hp_eq : p = 3 := by
              have hp2le := hp.two_le
              omega
            subst hp_eq
            have hrat := relIndex_dvd_untwisted 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K
            obtain ⟨E, hE, hle⟩ :=
              exists_elemAbelian_three_of_blocks (d := 1) (by norm_num) K hrat
                (IsWeylMatrix.of_word .E8 e8TwoWord) [2, 2, 2, 2, 2, 2, 2, 2]
                e8Two_charpoly e8Two_pow (by rw [he, he2]) (by norm_num) (by decide)
            refine ⟨E, hE, ?_⟩
            have hcard : 3 ^ 7 ≤ Nat.card E := by
              have h1' : (3 : ℕ) ^ 8 ≤ 1 * Nat.card E := by simpa using hle
              have h1'' : (3 : ℕ) ^ 8 ≤ Nat.card E := by simpa using h1'
              calc (3 : ℕ) ^ 7 ≤ 3 ^ 8 := by norm_num
                _ ≤ Nat.card E := h1''
            have hdeg : degCount .E8 e = 8 := by rw [he2]; decide
            rw [hdeg]
            simpa using hcard
        ·
          obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E8_three K hp (by rw [he, he3])
          refine ⟨E, hE, ?_⟩
          rw [hcard]
          have hdeg : degCount .E8 e = 4 := by rw [he3]; decide
          rw [hdeg]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4)
        ·
          obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E8_four K hp (by rw [he, he4])
          refine ⟨E, hE, ?_⟩
          rw [hcard]
          have hdeg : degCount .E8 e = 4 := by rw [he4]; decide
          rw [hdeg]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4)
        ·
          obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E8_six K hp (by rw [he, he6])
          refine ⟨E, hE, ?_⟩
          rw [hcard]
          have hdeg : degCount .E8 e = 4 := by rw [he6]; decide
          rw [hdeg]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4)

end CFSG.StandardType
