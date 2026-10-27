module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Adapters.Certificate43Check
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213t_not_stronglyEmbedded_three (D : Data G) (Ch : Choice2011 G)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hn2 : 2 ≤ c.n) (hpow : IsPowTwo c.n) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  intro hse
  obtain ⟨k, hk⟩ := hpow
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have hev : Even c.n := by
    rw [hk]
    exact Nat.even_pow.2 ⟨even_two, hk0⟩
  have h3 : 3 ∈ piSet c.B0 := by
    rw [c.hpi]
    refine ⟨Nat.prime_three, ?_⟩
    have h := Nat.dvd_sub_mod (n := 3) (2 ^ c.n)
    rwa [CFSG.two_pow_mod_three_of_even hev] at h
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAB : zpowers b ≤ c.B0 := zpowers_le.2 hb
  have hA1 : zpowers b ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at hbo
    omega
  have hA3 : IsPGroup 3 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  exact s21_2 D Ch h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } _ hAB
    (hse.normalizer_le hA1 hA3 (hAB.trans c.hBM))

theorem uc22p2213t_l2sz (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn2 : 2 < n)
    (h : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) : K2213 D c p L n := by
  have hLV := uc22p2213a_not_le_centralizer D Ch h117 hV h1930 c hL hc2
  rcases h with ⟨hL2, hcong⟩ | ⟨hSz, hcong⟩
  · haveI : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
    obtain ⟨e⟩ := uc22p2213c_bar2_equiv D hV h1930 c hL hLV
    exact ⟨hL, Or.inr (Or.inl hcong), Or.inr (Or.inr (Or.inl
      ⟨Or.inl ⟨hn2, Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)⟩, hc2⟩))⟩
  · haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    obtain ⟨e⟩ := uc22p2213c_bar2_equiv D hV h1930 c hL hLV
    have hSz' : IsSz ↥(mbarImage D.M c.V L) n := CFSG.Blueprint.LieModel.of_mulEquiv e hSz
    exact ⟨hL, Or.inr (Or.inr ⟨hSz', hcong⟩), Or.inr (Or.inr (Or.inl
      ⟨Or.inl ⟨hn2, Or.inr hSz'⟩, hc2⟩))⟩

theorem uc22p2213t_j1 (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (hV : S22_V D Ch) (h17J : S21_17J D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ}
    (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    (hJ : IsJ1 (Bar2 L)) (hn : c.n = 3) : K2213 D c p L 3 := by
  haveI : IsSimpleGroup (Bar2 L) := (kJ1_holds (Bar2 L) hJ).2.1
  obtain ⟨e⟩ := uc22p2213c_bar2_equiv D hV h1930 c hL
    (uc22p2213a_not_le_centralizer D Ch h117 hV h1930 c hL hc2)
  have hJ' : IsJ1 ↥(mbarImage D.M c.V L) := by
    obtain ⟨f⟩ := hJ
    exact ⟨e.symm.trans f⟩
  obtain ⟨hpr, hp2⟩ := D.sig_prime p hp
  have hpL : p ∣ Nat.card (Bar2 L) := by
    have h := h17J h1930 c.toCtx21 L hL hc2 hJ hn p hp
    rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)] at h
    exact (hpr.dvd_mul.1 h).resolve_right
      (uc22p20c_not_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup hpr hp2)
  refine ⟨hL, Or.inl ⟨hJ', rfl, ?_, not_isL2_of_isJ1 hJ'⟩,
    Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨hJ', rfl⟩, hc2⟩))⟩
  rwa [← Nat.card_congr e.toEquiv]

theorem uc22p2213t_of_not_normal (D : Data G) (Ch : Choice2011 G) (h17 : S21_17 D Ch)
    (h15 : S21_15C D Ch) (h17J : S21_17J D Ch) (h8100 : R8100T D) (h117 : R117W D)
    (h869P : F08.R869NPair D) (hV : S22_V D Ch) (he : CFSG.Open.evenRank G = 3)
    (h1930 : H1930 D) (c : Ctx22b D Ch) (hn2 : 2 ≤ c.n) {p : ℕ} (hp : p ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) :
    ∃ n : ℕ, K2213 D c p L n := by
  have hLM : L ≤ D.M := uc22p22a_le_of_isSubnormal hL.1
  rcases h17 h1930 c.toCtx21 L hL with h1 | ⟨hc2, n, hn, hL2 | hSz⟩ | ⟨hc2, hJ, hn3, -⟩
  · exact (hnN (uc22p21j_normal_of_conjClosure_eq hLM h1)).elim
  · refine ⟨n, uc22p2213t_l2sz D Ch h117 hV h1930 c hL hc2 hn ?_⟩
    by_cases hpow : IsPowTwo n
    · by_cases hn0 : IsPowTwo c.n
      · exact Or.inl ⟨hL2, h8100 he L hL hc2 n hn hpow hL2
          (uc22p2213t_not_stronglyEmbedded_three D Ch h1930 c.toCtx21 hn2 hn0) p hp⟩
      · exact (uc22p2213a_false_of_not_isPowTwo D Ch h117 h869P hV
          h1930 c hL hc2 hn hL2 hpow hn0).elim
    · exact h15 h1930 c.toCtx21 L hL hc2 n (Or.inr ⟨hL2, hpow⟩) p hp
  · exact ⟨n, uc22p2213t_l2sz D Ch h117 hV h1930 c hL hc2 hn
      (h15 h1930 c.toCtx21 L hL hc2 n (Or.inl hSz) p hp)⟩
  · exact ⟨3, uc22p2213t_j1 D Ch h117 hV h17J h1930 c hp hL hc2 hJ hn3⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
