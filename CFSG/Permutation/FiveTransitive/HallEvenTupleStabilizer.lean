module

public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.HallEvenTupleStabilizer

open MulAction SubMulAction
open Research.HighDegreeHallReduction

private theorem even_card
    (r : ℕ) (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hdegree : r + 27 ≤ Nat.card X)
    (htrans : IsMultiplyPretransitive G X (r + 4)) (e : Fin (r + 4) ↪ X) :
    Even (Nat.card (stabilizer G e)) := by
  induction r generalizing G X with
  | zero =>
    exact Nat.not_odd_iff_even.mp
      (fourTransitiveOddStabilizerImpossibleAtLeastTwentySeven G X hdegree htrans e)
  | succ r ih =>
    let _ : IsMultiplyPretransitive G X (r + 1 + 4) := htrans
    let _ : IsPretransitive G X := is_one_pretransitive_iff.mp
      (isMultiplyPretransitive_of_le (G := G) (α := X) (n := r + 1 + 4)
        (by omega : 1 ≤ r + 1 + 4) (by omega))
    let a : X := e (Fin.last (r + 4))
    let Y := ofStabilizer G a
    let H := stabilizer G a
    let e' : Fin (r + 4) ↪ Y := (Fin.Embedding.init e).codRestrict Y (by
      intro i
      change (Fin.Embedding.init e) i ∈ ofStabilizer G a
      rw [mem_ofStabilizer_iff]
      exact e.injective.ne (Fin.castSucc_ne_last i))
    have hsnoc : ofStabilizer.snoc e' = e := by
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [ofStabilizer.snoc_castSucc]
        rfl
      · exact ofStabilizer.snoc_last e'
    have hY : Nat.card Y = Nat.card X - 1 := nat_card_ofStabilizer_eq G a
    let _ : Fintype Y := Fintype.ofFinite _
    have hnext : IsMultiplyPretransitive H Y (r + 4) :=
      (ofStabilizer.isMultiplyPretransitive (G := G) (α := X)
        (n := r + 4) (a := a)).mp htrans
    have heven := ih H Y (by omega) hnext e'
    rw [← natCard_stabilizer_snoc_eq G X e', hsnoc] at heven
    exact heven

theorem exists_involution_fixing_six
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hdegree : 29 ≤ Nat.card X) (h6 : IsMultiplyPretransitive G X 6)
    (e : Fin 6 ↪ X) : ∃ g : G, orderOf g = 2 ∧ ∀ i, g • e i = e i := by
  have heven := even_card 2 G X hdegree h6 e
  let _ : Fintype (stabilizer G e) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (p := 2) (G := stabilizer G e)
    (by simpa only [even_iff_two_dvd, Nat.card_eq_fintype_card] using heven)
  refine ⟨g, (Subgroup.orderOf_coe g).trans hg, ?_⟩
  intro i
  exact DFunLike.congr_fun g.property i

end FiveTransitive.HallEvenTupleStabilizer

end CFSG
