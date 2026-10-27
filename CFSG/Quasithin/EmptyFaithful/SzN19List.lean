module

public import CFSG.Quasithin.Background.S1549CIn
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.SzN19B56
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C
open scoped commutatorElement

namespace SzN19

section List

variable {V : Type} [CommGroup V] [Finite V]

theorem list_of_mem_cComp {J K : Subgroup (MulAut V)}
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) (hK : K ∈ cComp J) :
    CFSG.IsQuasisimple ↥K ∧ B56QuasisimpleList ↥K := by
  rcases S153L.b56_components hcases with ⟨hc6, -⟩ | ⟨G₁, G₂, hsup, -, hc, ⟨h6₁, -⟩, ⟨h6₂, -⟩⟩ |
      ⟨N₁, N₂, -, -, -, -, -, hq₁, hq₂, hall⟩
  · exact (false_of_mem_cComp_of_solvable hK (S153L.comp_solvable_of_card_six hc6)).elim
  · have hs : Group.IsSolvable ↥(G₁ ⊔ G₂) :=
      F1.isSolvable_sup_of_le_normalizer (S153L.comp_solvable_of_card_six h6₁)
        (S153L.comp_solvable_of_card_six h6₂) (le_normalizer_of_commute hc)
    rw [hsup] at hs
    exact (false_of_mem_cComp_of_solvable hK hs).elim
  · have hKne := ne_bot_of_mem_cComp hK
    rcases hall K hK with rfl | rfl
    · rcases hq₁ with h | h
      · exact absurd h hKne
      · exact h
    · rcases hq₂ with h | h
      · exact absurd h hKne
      · exact h

end List

section ListType

theorem false_of_quasisimple_card_six {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hc : Nat.card X = 6) : False := by
  have hsolv : Group.IsSolvable X := S153L.comp_solvable_of_card_six hc
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hperf : Group.IsPerfect X := hq.1
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial X
  rw [Group.IsPerfect.commutator_eq_top] at h1
  exact lt_irrefl _ h1

theorem isListL_of_b56
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hl : B56QuasisimpleList X) (hE : ∀ e : ℕ, 1 < e → ¬ IsLieOver2e X e) : IsListL X := by
  rcases hl with ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ |
    ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ | he6 | he7 | hhat |
    ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨e4⟩ | ⟨e5⟩
  ·
    have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · exact (hE n hn (Or.inl ⟨K, hKf, hKfin, hK, ⟨e⟩⟩)).elim
    · obtain rfl : n = 1 := by omega
      have hcard : Nat.card X = 6 := by
        rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hK]
        norm_num
      exact (false_of_quasisimple_card_six hq hcard).elim
  ·
    have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · exact (hE n hn (Or.inr (Or.inl ⟨K, hKf, hKfin, hK, ⟨e⟩⟩))).elim
    · obtain rfl : n = 1 := by omega
      have hK2 : Nat.card K = 2 := by simpa using hK
      exact Or.inl ⟨3, le_rfl, by norm_num, ⟨e.trans (Insp9.statedSLEquivZMod2 K hK2 3)⟩⟩
  ·
    have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · exact (hE n hn (Or.inr (Or.inr (Or.inl ⟨K, hKf, hKfin, hK, ⟨e⟩⟩)))).elim
    · obtain rfl : n = 1 := by omega
      exact (R3c2.not_isQuasisimple_statedSp_two (by simpa using hK) e hq).elim
  ·
    have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · exact (hE n hn (Or.inr (Or.inr (Or.inr ⟨K, hKf, hKfin, hK, ⟨e⟩⟩)))).elim
    · obtain rfl : n = 1 := by omega
      exact (R3c2.not_isQuasisimple_quasithinG2_two (by simpa using hK) e hq).elim
  · exact Or.inr (Or.inl he6)
  · exact Or.inr (Or.inr (Or.inr (Or.inl he7)))
  · exact Or.inr (Or.inr (Or.inl hhat))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hKf, hKfin, hK, ⟨e⟩⟩)))
  · exact Or.inl ⟨4, by norm_num, by norm_num, e4⟩
  · exact Or.inl ⟨5, by norm_num, by norm_num, e5⟩

end ListType

end SzN19

end CFSG.Quasithin
