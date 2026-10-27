module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Assembly.RankThreeEven (projSL)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

theorem simple_nonab_of_mulEquiv {S T : Type} [Group S] [Group T] (e : T ≃* S)
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) :
    IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a := by
  haveI := hs
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem valid_A {r : ℕ} {q : PrimePower} (hr : 1 ≤ r) (h1 : r = 1 → 4 ≤ q.card ∧
      q.card ≠ 4 ∧ q.card ≠ 5 ∧ q.card ≠ 9) (h23 : (r = 2 ∨ r = 3) → q.card ≠ 2) :
    (LieTypeIndex.A r q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  refine ⟨⟨hr, fun h => (h1 h).1⟩, ?_⟩
  rintro (⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩)
  · obtain ⟨-, h4, h5, h9⟩ := h1 h
    rcases h' with h' | h' | h' <;> contradiction
  · exact h23 (Or.inl h) h'
  · exact h23 (Or.inr h) h'

theorem valid_twistedA {r : ℕ} {q : PrimePower} (hr : 2 ≤ r) (h2 : r = 2 → 3 ≤ q.card) :
    (LieTypeIndex.twistedA r q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨⟨hr, h2⟩, id⟩

theorem valid_B_two {q : PrimePower} (h2 : q.card ≠ 2) (h3 : q.card ≠ 3) :
    (LieTypeIndex.B 2 q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨⟨le_rfl, fun h => h2 h.2⟩, fun h => h3 h.2⟩

theorem five_le_pow {p e : ℕ} (hp : 3 < p) (hpr : p.Prime) (he : 1 ≤ e) : 5 ≤ p ^ e := by
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hpr (by decide)
  exact le_trans (show 5 ≤ p by omega) (Nat.le_self_pow (by omega) p)

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem card_projSL_three_two : Nat.card (projSL 3 (GaloisField 2 1)) = 168 := by
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  obtain ⟨ν⟩ := KFacts.nonempty_sl3_mulEquiv_projSL (F := GaloisField 2 1) (by rw [hF])
  rw [← Nat.card_congr ν.toEquiv, KFacts.card_sl_three_eq, hF]
  norm_num

theorem valid_B_of_three_le {r f : ℕ} (hr : 3 ≤ r) (hf : 1 ≤ f) :
    (LieTypeIndex.B r ⟨2, f, Nat.prime_two, hf⟩).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩

theorem eq_one_one_of_irreducible {b c : GaloisField 2 1}
    (h : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  have h01 : ∀ x : GaloisField 2 1, x = 0 ∨ x = 1 := by
    classical
    intro x
    by_contra hx
    push Not at hx
    have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have h3 : 3 ≤ Fintype.card (GaloisField 2 1) := by
      have : ({0, 1, x} : Finset (GaloisField 2 1)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hx.1.symm, zero_ne_one]),
          Finset.card_pair (Ne.symm hx.2)]
      rw [← this]
      exact Finset.card_le_univ _
    rw [← Nat.card_eq_fintype_card, hcard] at h3
    omega
  have hc : c ≠ 0 := fun hc0 => h 0 (by rw [hc0]; ring)
  have h2 : (2 : GaloisField 2 1) = 0 := by
    have : CharP (GaloisField 2 1) 2 := inferInstance
    exact CharTwo.two_eq_zero
  have hc1 : c = 1 := (h01 c).resolve_left hc
  refine ⟨?_, hc1⟩
  rcases h01 b with hb | hb
  · exfalso
    apply h 1
    rw [hb, hc1]
    calc (1 : GaloisField 2 1) ^ 2 + 0 * 1 + 1 = 2 := by ring
      _ = 0 := h2
  · exact hb

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
