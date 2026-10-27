module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Shape
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251L
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Loss

open CFSG.Open Subgroup

@[expose] def LossAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ (P : Type) [Group P] [Finite P], (∀ x : P, x ^ p = 1) → (∀ x y : P, x * y = y * x) →
    ∀ φ : P →* MulAut X, ∃ x : X, orderOf x = 3 ∧
      ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x

theorem lossAt_of_thinShape {X : Type} [Group X] [Finite X] (hX : R8107Shape.ThinShape X)
    (hZ : center X = ⊥) (h3 : 3 ∣ Nat.card X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcp : ∀ B : Subgroup X, IsPGroup p B → IsCyclic ↥B) : LossAt X p := by
  intro P _ _ hexp hPab φ
  have hinn : KOddOutInner → (∃ k : ℕ, 1 ≤ k ∧ IsL2 X (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd X q) ∨ IsJ1 X →
      φ.range ≤ (MulAut.conj : X →* MulAut X).range := fun hK hs => by
    rintro _ ⟨u, rfl⟩
    exact hK X hs (φ u) (Odd.of_dvd_nat (hp.odd_of_ne_two hp2)
      (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hexp, map_one])))
  have h3x : ∃ x : X, orderOf x = 3 := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  rcases hX with ⟨n, h⟩ | ⟨q, hq, hq5, h⟩ | h
  · exact P2251L.exists_orderOf_three_index_le (P22fin.isL2Ev_of_isL2 h).1 hp hp2 hexp hPab φ
  · exact P2251L.exists_orderOf_three_index_le_of_le_inner hZ hp hcp h3x hexp hPab φ
      (hinn KBridge.kOddOutInner_holds (Or.inr (Or.inl ⟨q, hq, hq5, h⟩)))
  · exact P2251L.exists_orderOf_three_index_le_of_le_inner hZ hp hcp h3x hexp hPab φ
      (hinn KBridge.kOddOutInner_holds (Or.inr (Or.inr h)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Loss

end
