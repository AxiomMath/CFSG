module

public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem two_dvd_five_point_stabilizer_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5) :
    2 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change 2 ∣ h
  by_contra hnotTwo
  have hh : h ≠ 0 := Nat.card_pos.ne'
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 6375600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have heNonempty : Nonempty (Fin 3 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 3 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP3.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 13800 := by
    change
      (fixingSubgroup P (Set.range e)).index = 13800
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 462 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJfactorization :
      (462 * h).factorization 2 = 1 := by
    rw [show 462 = 2 * 231 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      Nat.prime_two.factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotTwo]
    norm_num
  let T : Sylow 2 J := Sylow.nonempty.some
  have hTcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T := isCyclic_of_prime_card hTcard
  let C : Subgroup J :=
    Subgroup.centralizer ((T : Subgroup J) : Set J)
  let N : Subgroup J :=
    Subgroup.normalizer ((T : Subgroup J) : Set J)
  have hAutCard : Nat.card (MulAut T) = 1 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime Nat.prime_two]
  have hrangeDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 1 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrangeCard :
      Nat.card T.normalizerMonoidHom.range = 1 :=
    Nat.dvd_one.mp hrangeDvd
  have hrEq :
      C.relIndex N =
        Nat.card T.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer
          ((T : Subgroup J) : Set J)).relIndex
          (Subgroup.normalizer
            ((T : Subgroup J) : Set J)) =
        Nat.card T.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      T.normalizerMonoidHom_ker]
  have hnormalizer :
      Subgroup.normalizer ((T : Subgroup J) : Set J) ≤
        Subgroup.centralizer ((T : Subgroup J) : Set J) := by
    exact Subgroup.relIndex_eq_one.mp
      (show C.relIndex N = 1 by
        rw [hrEq, hrangeCard])
  let transfer : J →* T :=
    MonoidHom.transferSylow T hnormalizer
  let Q : Subgroup J := transfer.ker
  letI : Q.Normal := by
    dsimp only [Q, transfer]
    infer_instance
  have hcomplement : IsComplement' Q T := by
    simpa only [Q, transfer] using
      MonoidHom.ker_transferSylow_isComplement'
        T hnormalizer
  have hcardMul := hcomplement.card_mul
  have hQcard : Nat.card Q = 231 * h := by
    rw [hTcard, hJcard] at hcardMul
    nlinarith
  let Z := SubMulAction.ofFixingSubgroup P (Set.range e)
  have hZcard : Nat.card Z = 22 := by
    change Nat.card ↥((Set.range e)ᶜ : Set X) = 22
    rw [Nat.card_coe_set_eq]
    have htotal :=
      Set.ncard_add_ncard_compl (Set.range e)
    rw [Nat.card_eq_fintype_card, hcard,
      hecard] at htotal
    omega
  have hJ2 :
      MulAction.IsMultiplyPretransitive J Z 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    change
      MulAction.IsMultiplyPretransitive
        (fixingSubgroup P (Set.range e))
        (SubMulAction.ofFixingSubgroup P (Set.range e)) 2
    apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
      (m := 2) (n := 5) P (Set.range e)
    omega
  letI : MulAction.IsPreprimitive J Z :=
    MulAction.isPreprimitive_of_is_two_pretransitive hJ2
  letI : Nonempty Z :=
    Fintype.card_pos_iff.mp (by
      rw [← Nat.card_eq_fintype_card, hZcard]
      norm_num)
  have hfaithfulJ :
      ∀ j : J, (∀ z : Z, j • z = z) → j = 1 := by
    intro j hj
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ Set.range e
    · have hfix :=
        (mem_fixingSubgroup_iff P).mp j.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
        using hfix
    · let z : Z := ⟨x, hx⟩
      have hz := hj z
      have hz' := congrArg Subtype.val hz
      simpa [z, Subgroup.smul_def, Equiv.Perm.smul_def]
        using hz'
  have hnormalCases :=
    OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
      J Z hfaithfulJ Q
  have hQneOne : Nat.card Q ≠ 1 := by
    rw [hQcard]
    nlinarith [Nat.card_pos (α := H)]
  have htwentyTwoQ : 22 ∣ Nat.card Q := by
    rcases hnormalCases with hQone | hZdvd
    · exact (hQneOne hQone).elim
    · rwa [hZcard] at hZdvd
  have htwoQ : 2 ∣ Nat.card Q :=
    (by norm_num : 2 ∣ 22).trans htwentyTwoQ
  rw [hQcard] at htwoQ
  rcases Nat.prime_two.dvd_mul.mp htwoQ with htwo | htwo
  · norm_num at htwo
  · exact hnotTwo htwo

end FiveTransitive.Degree25

end CFSG
