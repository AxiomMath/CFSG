module

public import CFSG.Permutation.FiveTransitive.TwoGroupOrbitCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitResidueSum
public import CFSG.Permutation.FiveTransitive.Degree80TwoSixNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoSixGeometry
open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem all_pairs
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 80) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 6)
    (g3 g5 : Subgroup.normalizer (Q : Set G)) (hg3 : g3 ^ 3 = 1) (hg5 : g5 ^ 5 = 1)
    (h3 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g3.val • x = x} ≤ 2)
    (h5 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g5.val • x = x} ≤ 4)
    (h4 : 9 ∣ Nat.card (Family (X := X) Q 4))
    (h16 : 9 ∣ Nat.card (Family (X := X) Q 16))
    (h32 : 9 ∣ Nat.card (Family (X := X) Q 32)) :
    Nat.card (Family (X := X) Q 2) = 37 ∧ ∀ x : X, Nat.card (orbit Q x) ≤ 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hb : Nat.card X ≤ 127 := by omega
  have ht := TwoGroupOrbitCount.card_eq_orbit_sum hb Q hQ
  rw [hX,hF] at ht
  have hs3 := (NormalizerOrbitResidueSum.sum_le 3 Q g3 hg3
    ({2,4,8,16,32,64} : Finset ℕ) (by intro m hm; simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega)).trans h3
  have hs5 := (NormalizerOrbitResidueSum.sum_le 5 Q g5 hg5
    ({2,4,8,16,32,64} : Finset ℕ) (by intro m hm; simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega)).trans h5
  norm_num [Finset.sum_insert,Finset.sum_singleton] at hs3 hs5
  obtain ⟨h2,hfour,h8,hsixteen,hthirtytwo,h64⟩ := Degree80TwoSixNumeric.all_pairs
    (Nat.card (Family (X := X) Q 2)) (Nat.card (Family (X := X) Q 4))
    (Nat.card (Family (X := X) Q 8)) (Nat.card (Family (X := X) Q 16))
    (Nat.card (Family (X := X) Q 32)) (Nat.card (Family (X := X) Q 64))
    (by omega) (by omega) (by omega) h4 h16 h32
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
  have hn4 := hnot 4 hfour
  have hn8 := hnot 8 h8
  have hn16 := hnot 16 hsixteen
  have hn32 := hnot 32 hthirtytwo
  have hn64 := hnot 64 h64
  omega

end FiveTransitive.Degree80TwoSixGeometry

end CFSG
