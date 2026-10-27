module

public import CFSG.Permutation.FiveTransitive.CentralExtensionSylowCenter
public import CFSG.Permutation.FiveTransitive.NormalizerSylowUniqueSquare

public section

namespace CFSG

namespace FiveTransitive.NormalizerSylowCenter

open MulAction FixedSetNormalizerHom

private theorem center_cases
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (q : Q) (hq : q ≠ 1)
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4)
    (P : Sylow 2 (Subgroup.normalizer (Q : Set G))) :
    let R := (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
      (Subgroup.normalizer (Q : Set G)).subtype
    a ∈ R → ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) →
      x = 1 ∨ x = (q : G) ∨ x = a ^ 2 ∨ x = (q : G) * a ^ 2 := by
  classical
  intro R haR x hxR hcentral
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
  have hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' U))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    subst Q
    exact NormalizerKernelQuotientOdd.prime_not_dvd_kernel_quotient G X s S
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hsix
  let qU : U := ⟨⟨q.val, Q.le_normalizer q.property⟩, q.property⟩
  have hqU : qU ≠ 1 := by
    intro h
    apply hq
    apply Subtype.ext
    exact congrArg (fun u : U => (u.val : G)) h
  obtain ⟨aN, haP, haeq⟩ := Subgroup.mem_map.mp haR
  obtain ⟨xN, hxP, hxeq⟩ := Subgroup.mem_map.mp hxR
  change (aN : G) = a at haeq
  change (xN : G) = x at hxeq
  let aP : P := ⟨aN, haP⟩
  let xP : P := ⟨xN, hxP⟩
  have haeqN : aN = ⟨a, haN⟩ := Subtype.ext haeq
  have hfaP : orderOf (f (aP : N)) = 4 := by
    change orderOf (f aN) = 4
    rw [haeqN]
    exact hfa
  have hcent (y : P) : xP * y = y * xP := by
    apply Subtype.ext
    apply Subtype.ext
    change (xN : G) * ((y : N) : G) = ((y : N) : G) * (xN : G)
    rw [hxeq]
    exact hcentral y.val.val (Subgroup.mem_map_of_mem N.subtype y.property)
  have hc := CentralExtensionSylowCenter.center_cases f hsize himage U hUcard hodd
    qU hqU P aP xP hfaP hcent
  rcases hc with h | h | h | h
  · left
    have he := congrArg (fun n : N => (n : G)) h
    exact hxeq.symm.trans he
  · right; left
    have he := congrArg (fun n : N => (n : G)) h
    exact hxeq.symm.trans he
  · right; right; left
    have he := congrArg (fun n : N => (n : G)) h
    change (xN : G) = (aN : G) ^ 2 at he
    rwa [hxeq, haeq] at he
  · right; right; right
    have he := congrArg (fun n : N => (n : G)) h
    change (xN : G) = (q : G) * (aN : G) ^ 2 at he
    rwa [hxeq, haeq] at he

theorem exists_sylow_unique_square_center
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (q : Q) (hq : q ≠ 1)
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha : orderOf a = 4) (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4) :
    ∃ P : Sylow 2 (Subgroup.normalizer (Q : Set G)),
      let R := (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype
      a ∈ R ∧ Q ≤ R ∧ (∀ x ∈ R, x ^ 2 = 1 ∨ x ^ 2 = a ^ 2) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set G), n * a ^ 2 = a ^ 2 * n) ∧
      ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) →
        x = 1 ∨ x = (q : G) ∨ x = a ^ 2 ∨ x = (q : G) * a ^ 2 := by
  obtain ⟨P, haP, hQP, hsq, hnorm⟩ :=
    NormalizerSylowUniqueSquare.exists_sylow_normalizer_centralizes G X s S hS Q hQ hsix himage a haN ha hfa
  exact ⟨P, haP, hQP, hsq, hnorm,
    center_cases G X s S hS Q hQ hsix himage q hq a haN hfa P haP⟩

end FiveTransitive.NormalizerSylowCenter

end CFSG
