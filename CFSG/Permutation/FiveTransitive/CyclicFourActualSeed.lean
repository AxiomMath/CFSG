module

public import CFSG.Permutation.FiveTransitive.HighDegreeNormalizedFourSeed
public import CFSG.Permutation.FiveTransitive.CyclicNormalizerCentralizes
public import CFSG.Permutation.FiveTransitive.CentralFreeFixedDivisibility
public import CFSG.Permutation.FiveTransitive.EvenInvolutionFixed

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicFourActualSeed

open MulAction FixedNormalizerAction

theorem exists_seed
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (Q : Subgroup G) (hcyclic : IsCyclic Q) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤) :
    ∃ y : Normalizer Q, orderOf y.val = 2 ∧ y.val ∉ Q ∧
      (∀ q : Q, Commute q.val y.val) ∧
      (fixedBy X y.val \ fixedPoints Q X).ncard = 4 ∧
      (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3 := by
  classical
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 2) (by simpa using hQ)
  have hne : Q ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_fintype_card] at hQ
    simp at hQ
  obtain ⟨y, hy, hyQ, hfour, _, _⟩ := HighDegreeNormalizedFourSeed.exists_normalized_seed
    hcard h5 hmax Q hQp hne hseven hfree S hS
  have hcentral := CyclicNormalizerCentralizes.normalizer_centralizes Q hcyclic S hS himage y
  have hcomm : ∀ q : Q, Commute q.val y.val := by
    intro q
    exact (Subgroup.mem_centralizer_iff.mp hcentral) q.val q.property
  have hd := CentralFreeFixedDivisibility.complementary_fixed_dvd Q hfree y hcomm
  rw [hQ] at hd
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X y.val) (fixedPoints Q X)
  have hupper := hmax y.val hy
  have hout : (fixedBy X y.val \ fixedPoints Q X).ncard = 4 := by omega
  have hp := EvenInvolutionFixed.card_mod_four y.val hy (heven y.val)
  have hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3 := by omega
  exact ⟨y, hy, hyQ, hcomm, hout, hlocal⟩

end FiveTransitive.CyclicFourActualSeed

end CFSG
