module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE7
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Seven
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Nine
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Fourteen
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Eighteen
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE7One
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusThree
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Open (IsElemAbelian)

private theorem not_dvd_small_of_three_lt {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hk0 : 0 < k) (hk : k ≤ 6) (hk5 : k ≠ 5) : ¬ p ∣ k := by
  intro h
  have hle : p ≤ k := Nat.le_of_dvd hk0 h
  have hp4 : 4 ≤ p := by omega
  have hp6 : p ≤ 6 := by omega
  interval_cases p
  · exact absurd hp (by norm_num)
  · have hk6 : k = 6 := by omega
    subst k
    norm_num at h
  · exact absurd hp (by norm_num)

theorem excToralRankInput_E7_of_dvd {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K p := by
  by_cases hp3 : p = 3
  · subst p
    exact TableBExc.Three.ggExcToralRankInput_E7_three hpq
  · exact ggExcToralRankInput_E7_of_ne_three hp hp2 hp3 hpq

theorem rankLE_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGElemAbelianRankLE (adjointGroup .E7 K) p (degCount .E7 e) := by
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
  by_cases h0 : degCount .E7 e = 0
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
      elemAbelian_card_eq_one_of_degCount_zero (τ := .E7) (by simp) K hp hp3 hpq he h0 hE
    rw [hE1, h0, pow_zero]
  · by_cases h1 : degCount .E7 e = 1
    ·
      have hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by
        rw [he]
        omega
      have hR := CFSG.LieType.SeitzGeneration.rankLE1_E7 K hp hpq hcnt
      have hcard := hR E hE
      simpa [h1] using hcard
    · by_cases h2 : degCount .E7 e = 2
      ·
        have he4 : e = 4 := by
          have h30 := le_thirty_of_degCount_pos (τ := .E7) (by simp) (by rw [h2]; norm_num)
          have key : ∀ o ≤ 30, degCount .E7 o = 2 → o = 4 := by decide
          exact key e h30 h2
        have hS : SylowTorus (adjointGroup .E7 K) p 2 :=
          sylowTorus_E7_four K hp (by rw [he, he4])
        have hcard := hS.rank_le hp hE
        simpa [h2] using hcard
      ·
        have hcnt3 : 3 ≤ degCount .E7 e := by omega
        rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCount_E7 hcnt3 with
          he1 | he2 | he3 | he6
        ·
          have hpq1 : p ∣ Nat.card K - 1 := by
            have h := (dvd_pow_sub_one_iff_orderOf (d := 1) hq he).2 (by
              simpa [he1] using dvd_refl 1)
            simpa using h
          have hT := excToralRankInput_E7_of_dvd (K := K) hp hp2 hpq1
          have hcard := hT.card_le (TableBExc.card_torusPow_E7 hp hpq1) hE
          have hrank : Tag.E7.rank = 7 := by decide
          rw [hrank] at hcard
          have hdeg : degCount .E7 e = 7 := by rw [he1]; decide
          simpa [hdeg] using hcard
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
          have hinj : Function.Injective (TableBExcTwo.adjointMap .E7 ι) :=
            TableBExcTwo.adjointMap_injective ι
          have hmapE : IsElemAbelian p (E.map (TableBExcTwo.adjointMap .E7 ι)) := hE.map _
          have hT := excToralRankInput_E7_of_dvd (K := L) hp hp2 hpqL
          have hcard := hT.card_le (TableBExc.card_torusPow_E7 hp hpqL) hmapE
          rw [Subgroup.card_map_of_injective hinj] at hcard
          have hrank : Tag.E7.rank = 7 := by decide
          rw [hrank] at hcard
          have hdeg : degCount .E7 e = 7 := by rw [he2]; decide
          simpa [hdeg] using hcard
        ·
          have hlt : e < p := orderOf_lt_prime hp hpq he
          have hp3 : 3 < p := by omega
          have hS : SylowTorus (adjointGroup .E7 K) p 3 :=
            sylowTorus_of_blocks_of_three_lt (e := 3) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
              hpq (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly
              e7Three_pow (by rw [he, he3])
              (by
                intro d hd hde
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl | rfl | rfl
                · exact not_dvd_small_of_three_lt (k := 1) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                all_goals exact absurd rfl hde)
              (by
                intro d hd hed
                simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · norm_num at hed
                · norm_num at hed ⊢
                  exact not_dvd_small_of_three_lt (k := 2) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                · norm_num at hed
                · norm_num at hed
                · norm_num at hed ⊢
                  exact not_dvd_small_of_three_lt (k := 4) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                · norm_num at hed
                · norm_num at hed ⊢
                  exact not_dvd_small_of_three_lt (k := 6) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num))
              (by decide)
          have hcard := hS.rank_le hp hE
          have hdeg : degCount .E7 e = 3 := by rw [he3]; decide
          simpa [hdeg] using hcard
        ·
          have hlt : e < p := orderOf_lt_prime hp hpq he
          have hp3 : 3 < p := by omega
          have hS : SylowTorus (adjointGroup .E7 K) p 3 :=
            sylowTorus_of_blocks_of_three_lt (e := 6) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
              hpq (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly
              e7Six_pow (by rw [he, he6])
              (by
                intro d hd hde
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl | rfl | rfl
                · exact not_dvd_small_of_three_lt (k := 2) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                all_goals exact absurd rfl hde)
              (by
                intro d hd hed
                simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · norm_num at hed
                · norm_num at hed ⊢
                  exact hp.ne_one
                · norm_num at hed
                · norm_num at hed
                · norm_num at hed ⊢
                  exact not_dvd_small_of_three_lt (k := 2) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                · norm_num at hed
                · norm_num at hed ⊢
                  exact not_dvd_small_of_three_lt (k := 3) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num))
              (by decide)
          have hcard := hS.rank_le hp hE
          have hdeg : degCount .E7 e = 3 := by rw [he6]; decide
          simpa [hdeg] using hcard

theorem exists_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    GGExcElemAbelianExists (adjointGroup .E7 K) p (degCount .E7 e - 1) := by
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
  by_cases h0 : degCount .E7 e = 0
  ·
    refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
    rw [h0]
    simp
  · by_cases h1 : degCount .E7 e = 1
    ·
      refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
      rw [h1]
      simp
    · by_cases h2 : degCount .E7 e = 2
      ·
        have he4 : e = 4 := by
          have h30 := le_thirty_of_degCount_pos (τ := .E7) (by simp) (by rw [h2]; norm_num)
          have key : ∀ o ≤ 30, degCount .E7 o = 2 → o = 4 := by decide
          exact key e h30 h2
        have hS : SylowTorus (adjointGroup .E7 K) p 2 :=
          sylowTorus_E7_four K hp (by rw [he, he4])
        obtain ⟨E, hE, hcard⟩ := hS.exists_elemAbelian
        refine ⟨E, hE, ?_⟩
        rw [hcard, h2]
        exact Nat.pow_le_pow_right hp.pos (by norm_num : 1 ≤ 2)
      ·
        have hcnt3 : 3 ≤ degCount .E7 e := by omega
        rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCount_E7 hcnt3 with
          he1 | he2 | he3 | he6
        ·
          by_cases hp3 : 3 < p
          · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E7_one K hp hp3 (by rw [he, he1])
            refine ⟨E, hE, ?_⟩
            rw [hcard]
            have hdeg : degCount .E7 e = 7 := by rw [he1]; decide
            rw [hdeg]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 6 ≤ 7)
          ·
            have hp_eq : p = 3 := by
              have hp2le := hp.two_le
              omega
            subst p
            have hrat := relIndex_dvd_untwisted 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K
            obtain ⟨E, hE, hle⟩ :=
              exists_elemAbelian_three_of_blocks (d := 2) (by norm_num) K hrat
                (IsWeylMatrix.of_word Tag.E7 e7OneWord) [1, 1, 1, 1, 1, 1, 1]
                e7One_charpoly e7One_pow (by rw [he, he1]) (by norm_num) (by decide)
            refine ⟨E, hE, ?_⟩
            have hcard : 3 ^ 6 ≤ Nat.card E := by
              have h1' : (2187 : ℕ) ≤ 2 * Nat.card E := by simpa using hle
              omega
            have hdeg : degCount .E7 e = 7 := by rw [he1]; decide
            rw [hdeg]
            simpa using hcard
        ·
          by_cases hp3 : 3 < p
          · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_E7_two K hp hp3 (by rw [he, he2])
            refine ⟨E, hE, ?_⟩
            rw [hcard]
            have hdeg : degCount .E7 e = 7 := by rw [he2]; decide
            rw [hdeg]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 6 ≤ 7)
          ·
            have hp_eq : p = 3 := by
              have hp2le := hp.two_le
              omega
            subst p
            have hrat := relIndex_dvd_untwisted 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K
            obtain ⟨E, hE, hle⟩ :=
              exists_elemAbelian_three_of_blocks (d := 2) (by norm_num) K hrat
                (IsWeylMatrix.of_word Tag.E7 e7TwoWord) [2, 2, 2, 2, 2, 2, 2]
                e7Two_charpoly e7Two_pow (by rw [he, he2]) (by norm_num) (by decide)
            refine ⟨E, hE, ?_⟩
            have hcard : 3 ^ 6 ≤ Nat.card E := by
              have h1' : (2187 : ℕ) ≤ 2 * Nat.card E := by simpa using hle
              omega
            have hdeg : degCount .E7 e = 7 := by rw [he2]; decide
            rw [hdeg]
            simpa using hcard
        ·
          have hlt : e < p := orderOf_lt_prime hp hpq he
          have hp3 : 3 < p := by omega
          have h := exists_elemAbelian_of_blocks (e := 3) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
            (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3]
            e7Three_charpoly e7Three_pow (by rw [he, he3]) (by norm_num)
            (by
              intro d hd hde
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl | rfl | rfl
              · norm_num
              all_goals exact absurd rfl hde)
          obtain ⟨E, hE, hcard⟩ := h
          refine ⟨E, hE, ?_⟩
          rw [hcard]
          have hdeg : degCount .E7 e = 3 := by rw [he3]; decide
          rw [hdeg]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3)
        ·
          have hlt : e < p := orderOf_lt_prime hp hpq he
          have hp3 : 3 < p := by omega
          have h := exists_elemAbelian_of_blocks (e := 6) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
            (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6]
            e7Six_charpoly e7Six_pow (by rw [he, he6]) (by norm_num)
            (by
              intro d hd hde
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl | rfl | rfl
              · norm_num
              all_goals exact absurd rfl hde)
          obtain ⟨E, hE, hcard⟩ := h
          refine ⟨E, hE, ?_⟩
          rw [hcard]
          have hdeg : degCount .E7 e = 3 := by rw [he6]; decide
          rw [hdeg]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3)

end CFSG.StandardType
