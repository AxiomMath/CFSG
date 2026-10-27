module

public import CFSG.Permutation.FiveTransitive.CentralExtensionUniqueSquare
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution
public import CFSG.Permutation.FiveTransitive.UniqueSquareNormalizer
public import CFSG.Permutation.FiveTransitive.NormalizerKernelQuotientOdd

public section

namespace CFSG

namespace FiveTransitive.NormalizerSylowUniqueSquare

open MulAction FixedSetNormalizerHom

theorem exists_sylow
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha : orderOf a = 4) (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4) :
    ∃ P : Sylow 2 (Subgroup.normalizer (Q : Set G)),
      let R := (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype
      a ∈ R ∧ Q ≤ R ∧ ∀ x ∈ R, x ^ 2 = 1 ∨ x ^ 2 = a ^ 2 := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let U : Subgroup N := Q.subgroupOf N
  let f := fixedPermHom G X Q
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hcard : Nat.card Q = 2 := by
    rw [← hQ, Subgroup.card_map_of_injective (fixingSubgroup G s).subtype_injective]
    exact hS
  have hUcard : Nat.card U = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv]
    exact hcard
  have hU : U ≤ f.ker := by
    intro u hu
    apply (mem_ker_iff G X Q u).mpr
    intro x hx
    exact mem_fixedPoints.mp hx ⟨u.val, hu⟩
  have hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' U))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    subst Q
    exact NormalizerKernelQuotientOdd.prime_not_dvd_kernel_quotient G X s S
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hsix
  have hcentral : ∀ q : U, ∀ g : N, (q : N) * g = g * q := by
    intro q g
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hcard g ⟨q.val.val, q.property⟩
  let aN : N := ⟨a, haN⟩
  have haN4 : orderOf aN = 4 := by rw [← Subgroup.orderOf_coe]; exact ha
  obtain ⟨P, haP, hUP, hsq⟩ := CentralExtensionUniqueSquare.exists_sylow_unique_square
    f hsize himage U hU hUcard hodd hcentral aN haN4 hfa
  refine ⟨P, Subgroup.mem_map_of_mem N.subtype haP, ?_, ?_⟩
  · intro q hq
    exact Subgroup.mem_map.mpr ⟨⟨q, Q.le_normalizer hq⟩, hUP hq, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rcases hsq ⟨y, hy⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem exists_sylow_normalizer_centralizes
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha : orderOf a = 4) (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4) :
    ∃ P : Sylow 2 (Subgroup.normalizer (Q : Set G)),
      let R := (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype
      a ∈ R ∧ Q ≤ R ∧ (∀ x ∈ R, x ^ 2 = 1 ∨ x ^ 2 = a ^ 2) ∧
      ∀ n ∈ Subgroup.normalizer (R : Set G), n * a ^ 2 = a ^ 2 * n := by
  obtain ⟨P, haP, hQP, hsq⟩ := exists_sylow G X s S hS Q hQ hsix himage a haN ha hfa
  refine ⟨P, haP, hQP, hsq, ?_⟩
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  exact UniqueSquareNormalizer.normalizer_centralizes _ a haP ha2 hsq

end FiveTransitive.NormalizerSylowUniqueSquare

end CFSG
