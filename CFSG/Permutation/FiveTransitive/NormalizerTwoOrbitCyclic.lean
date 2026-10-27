module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount
public import CFSG.Permutation.FiveTransitive.SevenLocalSquare
public import CFSG.Permutation.FiveTransitive.NormalizerEvenCentralizerTwo
public import CFSG.Permutation.FiveTransitive.InvolutiveCosetCyclic
public import CFSG.Permutation.FiveTransitive.CosetFixedSquare

public section

namespace CFSG

namespace FiveTransitive.NormalizerTwoOrbitCyclic

open MulAction NormalizerFixedComplement

theorem coset_square_eq_one
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    ∀ q ∈ Q, (q * x.val) ^ 2 = 1 := by
  have htwo := NormalizerSevenOrbitCount.saturated_coset_fixed_two
    hmax Q A hQA hA hfree x hx hxQ hlocal horbits
  intro q hq
  let qi : Inside Q := ⟨⟨q, Q.le_normalizer hq⟩, hq⟩
  have hn : Nonempty (fixedBy (Domain (X := X) Q) ((qi : Normalizer Q) * x)) :=
    (Nat.card_pos_iff.mp (by rw [htwo qi]; omega)).1
  obtain ⟨z, hz⟩ := hn
  let g : A := ⟨q * x.val, A.mul_mem (hQA hq) hx⟩
  have hF : (fixedPoints Q X).ncard = 7 := by
    simpa only [Nat.card_coe_set_eq] using hseven
  apply CosetFixedSquare.eq_one_of_maximal_fixed 7 hmax A hA g
    (fixedPoints Q X) hF
    (SevenLocalSquare.coset_square_fixes Q hseven x.val x.property hlocal ⟨q, hq⟩)
    z.val z.property
  exact congrArg Subtype.val hz

theorem isCyclic_of_two_fixed_orbits
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) : IsCyclic Q := by
  have hsq := coset_square_eq_one hmax Q A hQA hA hseven hfree x hx hxQ hlocal horbits
  have hxsq : x ^ 2 = 1 := Subtype.ext (by simpa using hsq 1 Q.one_mem)
  have hxne : x ≠ 1 := by
    intro he
    apply hxQ
    rw [he]
    exact Q.one_mem
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hxsq, hxne⟩
  have hc := (NormalizerEvenCentralizerTwo.actual_coset heven hdegree hmax Q hQ hne
    hfree x hlocal 1 (by simpa using hx2)).1
  apply InvolutiveCosetCyclic.isCyclic_of_centralizer_subgroup_card_two Q x.val hQ hsq
  simpa only [OneMemClass.coe_one, one_mul, Subgroup.subgroupOf] using hc

end FiveTransitive.NormalizerTwoOrbitCyclic

end CFSG
