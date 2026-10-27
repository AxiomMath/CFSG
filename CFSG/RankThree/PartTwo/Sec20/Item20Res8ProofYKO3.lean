module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofYKO3
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KFactKO3Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ K O : Subgroup G, O ≠ ⊤ → Group.IsPerfect K →
      ((∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
        (∃ n : ℕ, Even n ∧ 4 ≤ n ∧
          Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n)))) →
      K ≤ Subgroup.normalizer (O : Set G) → Nat.Coprime 3 (Nat.card O) →
      (∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p O ≤ 2) →
      ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O

@[expose] def Step204YKO3CommSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        yTwenty X c ≤ kTwenty M c ⊔ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c) →
        (Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)) ∨
          Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 2 (GaloisField 2 2))) →
          ∀ k ∈ kTwenty M c, ∀ o ∈ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c),
            k * o * k⁻¹ * o⁻¹ ∈
              CFSG.Open.pCoreOf 2 (inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c))

theorem step204YKO3Comm_of_small (hKF : KFactKO3Cent) (hS : Step204YKO3CommSmall) :
    Step204YKO3Comm := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := hset.isSimpleGroup
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set O := inSubgroup (CFSG.pPrimeCore 3) Y with hOdef
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYX : Y ≤ X := Res6.normalClosureIn_le_self (hKX (self_mem_normalClosureIn M c))
  have hOX : O ≤ X := (Res6.inSubgroup_pPrimeCore_le 3 Y).trans hYX
  have hX2 : CFSG.Assembly.IsTwoLocal X := hX.1.1
  have hXtop : X ≠ ⊤ := by
    obtain ⟨Q, hQ1, hQ2, hXQ⟩ := hX2
    rw [hXQ]
    exact Late.normalizer_ne_top_of_isPGroup_two hset.nonabelian hQ2 hQ1
  have hOtop : O ≠ ⊤ := fun h => hXtop (top_le_iff.mp (h ▸ hOX))
  have hperf : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    hKY.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hO3 : Nat.Coprime 3 (Nat.card O) := Res6.coprime_card_inSubgroup_pPrimeCore 3 Y
  have hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p O ≤ 2 := by
    intro p hp hp5
    have hloc : CFSG.Open.pRank p X ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
      le_csSup ⟨Nat.card G, by
        rintro _ ⟨Z, -, rfl⟩
        exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
          (Subgroup.card_le_card_group Z)⟩ ⟨X, hX2, rfl⟩
    have hlt := hset.localRank_lt p hp (by omega)
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hOX).trans (Nat.lt_succ_iff.mp
      (hloc.trans_lt hlt))
  rcases hset.kType with ⟨n, hn, he⟩ | ⟨n, hn, hn0, he⟩
  · by_cases h1 : n = 1
    · subst h1
      exact hS G A M L N c T i j P hset X hX hXM hm hle (Or.inl he)
    · have h3 : 3 ≤ n := by
        obtain ⟨k, rfl⟩ := hn
        omega
      exact hKF G hset.kProper K O hOtop hperf (Or.inl ⟨n, hn, h3, he⟩) hKO hO3 hrank
  · by_cases h2 : n = 2
    · subst h2
      exact hS G A M L N c T i j P hset X hX hXM hm hle (Or.inr he)
    · have h4 : 4 ≤ n := by
        obtain ⟨k, rfl⟩ := hn
        omega
      exact hKF G hset.kProper K O hOtop hperf (Or.inr ⟨n, hn, h4, he⟩) hKO hO3 hrank

end CFSG.RankThree.PartTwo.Sec20
