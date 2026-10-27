module

public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

namespace Item228Proof

theorem exists_even_mulEquiv_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) := by
  obtain ⟨-, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  rcases hcase with ⟨-, n, hn, hne, -, hKn, -⟩ | ⟨-, n, hn, hne, -, hKn, -⟩ |
      ⟨-, n, hn, hne, -, hKn | hKn, -⟩ | ⟨-, -, hKn | hKn, -⟩ | ⟨h81, -⟩
  · exact ⟨n, hn, hne, hKn⟩
  · exact ⟨n, hn, hne, hKn⟩
  · exact ⟨n, hn, hne, hKn⟩
  · exact ⟨2 * n, by omega, even_two_mul n, hKn⟩
  · exact ⟨2, by norm_num, even_two, hKn⟩
  · exact ⟨4, by norm_num, by decide, hKn⟩
  · rw [hA27] at h81
    norm_num at h81

theorem not_isTransvectionOn_of_mem_wStar [Finite G] (h2131 : Item2131One)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) :
    ∀ ρ ∈ wStar A, ¬ IsTransvectionOn ρ := by
  obtain ⟨f, hW, -⟩ := h2131 G A E U c L hpair hA27
  intro ρ hρ
  exact not_isTransvectionOn_of_mem_monomial hpair.mem_S.1.1.1 f (hW ⟨ρ, hρ, rfl⟩)

theorem item228One [Finite G] (h2131 : Item2131One) (h222 : Item222) (hList : Item228OneList)
    (hPSp : Item228NotPSp45) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) {φ : MulAut A} (hφ : φ ∈ dStar A) {X : Subgroup G}
    (hX : X ∈ lStar A) (hKX : kOf A φ ≤ X) : Item228OneConcl A φ X := by
  obtain ⟨m, hm0, hme, hKm⟩ := exists_even_mulEquiv_kOf h222 hpair hA27 hφ
  rcases hList G A E U c L hpair hA27 (not_isTransvectionOn_of_mem_wStar h2131 hpair hA27) φ hφ
    X hX hKX m hm0 hme hKm with h | ⟨-, hP⟩
  · exact ⟨m, hm0, hme, hKm, h⟩
  · exact (hPSp G A E U c L hpair hA27 φ hφ X hX hKX hP).elim

end Item228Proof

open Item228Proof

end CFSG.RankThree.PartTwo.Sec21
