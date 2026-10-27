module

public import CFSG.Permutation.FiveTransitive.TwoGroupOrbitCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitResidueSum
public import CFSG.Permutation.FiveTransitive.Degree80TwoEightNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoEightGeometry
open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem geometry
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 80) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 8)
    (g5 g7 : Subgroup.normalizer (Q : Set G)) (hg5 : g5 ^ 5 = 1) (hg7 : g7 ^ 7 = 1)
    (h5 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g5.val • x = x} ≤ 2)
    (h7 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g7.val • x = x} ≤ 2) :
    Nat.card (Family (X := X) Q 2) = 36 ∧ (∀ x : X, Nat.card (orbit Q x) ≤ 2) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hb : Nat.card X ≤ 127 := by omega
  have ht := TwoGroupOrbitCount.card_eq_orbit_sum hb Q hQ
  rw [hX,hF] at ht
  have hs5 := (NormalizerOrbitResidueSum.sum_le 5 Q g5 hg5
    ({2,4,8,16,32,64} : Finset ℕ) (by intro m hm; simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega)).trans h5
  have hs7 := (NormalizerOrbitResidueSum.sum_le 7 Q g7 hg7
    ({2,4,8,16,32,64} : Finset ℕ) (by intro m hm; simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega)).trans h7
  norm_num [Finset.sum_insert,Finset.sum_singleton] at hs5 hs7
  obtain ⟨h2,h4,h8,h16,h32,h64⟩ := Degree80TwoEightNumeric.geometry
    (Nat.card (Family (X := X) Q 2)) (Nat.card (Family (X := X) Q 4))
    (Nat.card (Family (X := X) Q 8)) (Nat.card (Family (X := X) Q 16))
    (Nat.card (Family (X := X) Q 32)) (Nat.card (Family (X := X) Q 64))
    (by omega) (by omega) (by omega)
  refine ⟨h2,?_⟩
  intro x
  have hc := TwoGroupOrbitCount.orbit_card_cases hb Q hQ (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hc
  have hnot (m : ℕ) (hm : Nat.card (Family (X := X) Q m) = 0) :
      Nat.card (orbit Q x) ≠ m := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q m) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
    omega
  have hn4 := hnot 4 h4
  have hn8 := hnot 8 h8
  have hn16 := hnot 16 h16
  have hn32 := hnot 32 h32
  have hn64 := hnot 64 h64
  omega
end FiveTransitive.Degree80TwoEightGeometry

end CFSG
