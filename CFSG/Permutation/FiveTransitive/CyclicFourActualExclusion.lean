module

public import CFSG.Permutation.FiveTransitive.CyclicFourActualSeed
public import CFSG.Permutation.FiveTransitive.CyclicFourZeroOrbitExclusion
public import CFSG.Permutation.FiveTransitive.CyclicEvenComplementDivisibility

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicFourActualExclusion

open MulAction FixedNormalizerAction

theorem false_of_card_four
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (Q : Subgroup G) (hcyclic : IsCyclic Q) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ (u : Normalizer Q), u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    False := by
  classical
  let _ : IsCyclic Q := hcyclic
  have hdiv := CyclicEvenComplementDivisibility.twice_card_dvd Q hcyclic
    (show Even (Nat.card Q) by rw [hQ]; decide) (fun q => heven q.val) hfree
  have hF : (fixedPoints Q X).ncard = 7 := by rwa [← Nat.card_coe_set_eq]
  have hdiv8 : 8 ∣ Nat.card X - 7 := by simpa only [hQ, hF] using hdiv
  have hdegree : Fintype.card X % 4 = 3 := by
    rw [Nat.card_eq_fintype_card] at hdiv8
    omega
  obtain ⟨y, hy, _, _, hout, hlocal⟩ := CyclicFourActualSeed.exists_seed
    hcard h5 hmax heven hdegree Q hcyclic hQ hseven hfree S hS himage
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  rw [hQ] at hb
  have hcentral : ∀ n : Normalizer Q, ∀ q : Q, Commute n.val q.val := by
    intro n q
    exact ((Subgroup.mem_centralizer_iff.mp
      (CyclicNormalizerCentralizes.normalizer_centralizes Q hcyclic S hS himage n))
        q.val q.property).symm
  have hfull : Image (X := X) Q = ⊤ := by
    apply top_unique
    rw [← himage]
    rintro σ ⟨n, _, hn⟩
    exact ⟨n, hn⟩
  have hypos : ∃ t : X, t ∉ fixedPoints Q X ∧ y.val • t = t := by
    obtain ⟨t, ht⟩ := Set.nonempty_of_ncard_ne_zero (show
      (fixedBy X y.val \ fixedPoints Q X).ncard ≠ 0 by omega)
    exact ⟨t, ht.2, ht.1⟩
  exact CyclicFourZeroOrbitExclusion.false_of_double_seed hmax Q hcyclic hQ hseven hfree
    hdiv8 S hS hfull hcentral hzero b hb y hy hlocal hypos

end FiveTransitive.CyclicFourActualExclusion

end CFSG
