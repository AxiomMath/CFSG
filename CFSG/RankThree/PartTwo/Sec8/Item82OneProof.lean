module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofSL34
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82OneProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

section Alternatives

variable (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
  (hAN : A ≤ Subgroup.normalizer (L : Set G))
  (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))

include h h27 hAN hcyc

theorem isList82One_of_alt47_three (hG2 : KF82E9GTwo) (hPGU : KF82E9PGUThree)
    (hRee : KF82E9ReeF4) (hL3 : KF82LThreeWrong) (hSL4 : KF82SLThreeFour)
    (h3 : (∃ m : ℕ, 1 ≤ m ∧
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 m)) ∨
          (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 ∧
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
              CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 m) ∨
          ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * m) ∧
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
              CFSG.Assembly.LowTwoRank.StatedSL 3 K))) ∨
      ∃ n : ℕ, Odd n ∧
        (Blueprint.SuzukiModel (L ⧸ aschbacherSolvableCore 3 L) 2 n ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) ∨
          Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 n ∨
          Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 n)) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  rcases h3 with ⟨m, hm, he₁ | ⟨K, _, _, hK, ⟨e₁⟩⟩ | he₁ | ⟨K, _, _, hK, ⟨e₁⟩⟩⟩ |
    ⟨n, hn, hSz | he₁ | he₁ | hX | hX⟩
  · exact isList82One_of_psl2 h h27 hAN hcyc hm he₁.some
  · exact isList82One_of_statedSU h h27 hAN hcyc hPGU hm hK e₁
  · exact isList82One_of_projSU h h27 hAN hcyc hPGU hm he₁.some
  · exact isList82One_of_statedSL h hSL4 (by omega)
      (two_pow_mod_three_of_even ⟨m, by ring⟩) hK e₁
  · exact (false_of_suzuki h h27 hAN hcyc hSz).elim
  · exact isList82One_of_projSL3 h h27 hAN hcyc hL3 hn.pos he₁.some
  · exact (false_of_projSp h h27 hAN hcyc he₁.some).elim
  · exact (false_of_g2 h h27 hAN hcyc hG2 hn hX).elim
  · exact (false_of_ree h h27 hAN hcyc hRee hn hX).elim

theorem isList82One_of_alt47_four (hPGU : KF82E9PGUThree) (hL3 : KF82LThreeWrong)
    (hSL4 : KF82SLThreeFour) {n : ℕ} (hn : 1 ≤ n)
    (hX : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ n) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 n) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  rcases hX with ⟨K, _, _, ⟨hK, hq, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ | ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
  · have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · obtain rfl : n = 1 := by omega
        norm_num at hq
      · exact h2
    exact isList82One_of_statedSL h hSL4 hn2 hq hK e₁
  · exact isList82One_of_statedSU h h27 hAN hcyc hPGU hn hK e₁
  · exact isList82One_of_projSL3 h h27 hAN hcyc hL3 hn e₁
  · exact isList82One_of_projSU h h27 hAN hcyc hPGU hn e₁

end Alternatives

theorem isList82One_of_alt47W (hG2 : KF82E9GTwo) (hPGU : KF82E9PGUThree) (hRee : KF82E9ReeF4)
    (hD4 : KF82E9TrialityD4) (hL3 : KF82LThreeWrong) (hOdd : KF82OddSLThree)
    (hSL4 : KF82SLThreeFour) (h : Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (halt : Alt47W L a) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcyc := outThreeCyclic_of_alt47W hq halt
  rcases halt with ⟨p, e, _, -, he, ⟨e₁⟩, -⟩ | ⟨p, e, _, hp3, he1, he2, hX, -⟩ | ⟨h3, -⟩ |
    ⟨n, hn, hX, -⟩ | ⟨n, -, hD⟩
  · exact isList82One_of_psl2 h h27 hAN hcyc (by omega) e₁
  · exact (false_of_oddSLThree h hOdd hp3 he1 he2 hX).elim
  · exact isList82One_of_alt47_three h h27 hAN hcyc hG2 hPGU hRee hL3 hSL4 h3
  · exact isList82One_of_alt47_four h h27 hAN hcyc hPGU hL3 hSL4 hn hX
  · exact (false_of_trialityD4 h h27 hAN hcyc hD4 hD).elim

end CFSG.RankThree.PartTwo.Sec8.Item82OneProof

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec8.Item82OneProof

theorem item82One_of_item47W (h45 : Item4_5) (h47 : Item4_7W) (hG2 : KF82E9GTwo)
    (hPGU : KF82E9PGUThree) (hRee : KF82E9ReeF4) (hD4 : KF82E9TrialityD4)
    (hL3 : KF82LThreeWrong) (hOdd : KF82OddSLThree) : Item82One := by
  intro G _ _ A c L a h h27
  have hAN := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp
    h.mem_partTwoF.1 h.mem_A h.ne_one L h.mem_thetaComponentsAt
  exact isList82One_of_alt47W hG2 hPGU hRee hD4 hL3 hOdd kF82SLThreeFour h h27 hAN
    (alt47W_of_hyp81 h47 h)

end CFSG.RankThree.PartTwo.Sec8
