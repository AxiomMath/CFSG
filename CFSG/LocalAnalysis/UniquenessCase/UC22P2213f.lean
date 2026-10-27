module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import Certificates.Certificate113
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213f_false_of_powTwo (D : Data G) (Ch : Choice2011 G) (h8100E : R8100E D)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    (hn0 : IsPowTwo c.n) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hc2 : (conjSetOf D.M K).ncard = 2) {n : ℕ} (hn : 2 ≤ n) (hpow : IsPowTwo n)
    (hL2 : IsL2 (Bar2 K) n) : False := by
  have hSE := h8100E he K hK hc2 n hn hpow hL2
  obtain ⟨k, hk⟩ := hn0
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have h2 : 2 ∣ c.n := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have h3 : 3 ∣ 2 ^ c.n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h2
  have hmem : 3 ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨Nat.prime_three, h3⟩
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hmem
  have hAB : zpowers b ≤ c.B0 := zpowers_le.2 hb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hne : zpowers b ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hp3 : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  exact s21_2 D Ch h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } _ hAB
    (hSE.normalizer_le hne hp3 (hAB.trans c.hBM))

theorem uc22p2213f_strong (D : Data G) (Ch : Choice2011 G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (he : 3 < CFSG.Open.evenRank G) (h117 : R117W D)
    (h869P : F08.R869NPair D) (h17 : S21_17 D Ch) (h15 : S21_15C D Ch) (h21E : S21_21E D Ch)
    (h9 : S21_9N D Ch) (h8E : S21_8E D Ch) (h8100E : R8100E D) (h12 : S22_12 D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) (hn3 : 3 ≤ c.n) {p : ℕ} (hp : p ∈ D.sig) :
    ∃ (K : Subgroup G) (n : ℕ), K2213 D c p K n ∧
      ((¬ IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) := by
  have hV : S22_V D Ch := uc22p22o_s22_V_derived D Ch hx h61
  obtain ⟨L, hL, hnN⟩ := uc22p2213d_exists_not_normal D Ch hx h12 h21E h9 h8E h1930 he c
  rcases uc22p2213c_of_not_normal D Ch h17 h15 h117 hV h1930 he c hp hL hnN with
    ⟨m, hst, hK⟩ | ⟨hc2, n, hn2, hL2, hpow⟩
  · exact ⟨L, m, hK, hst⟩
  · by_cases hn0 : IsPowTwo c.n
    · exact (uc22p2213f_false_of_powTwo D Ch h8100E h1930 he c.toCtx21 hn3 hn0 hL hc2
        (by omega) hpow hL2).elim
    · exact (uc22p2213a_false_of_not_isPowTwo D Ch h117 h869P hV h1930 c hL hc2 hn2 hL2 hpow
        hn0).elim

theorem uc22p2213f_s22_13 (D : Data G) (Ch : Choice2011 G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (he : 3 < CFSG.Open.evenRank G) (h117 : R117W D)
    (h869P : F08.R869NPair D) (h17 : S21_17 D Ch) (h15 : S21_15C D Ch) (h21E : S21_21E D Ch)
    (h9 : S21_9N D Ch) (h8E : S21_8E D Ch) (h8100E : R8100E D)
    (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) :
    S22_12 D Ch → S22_13 D Ch := fun h12 h1930 c _ hp => by
  obtain ⟨K, n, hK, -⟩ := uc22p2213f_strong D Ch hx h61 he h117 h869P h17 h15 h21E h9 h8E
    h8100E h12 h1930 c (hn3 h1930 c) hp
  exact ⟨K, n, hK⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
