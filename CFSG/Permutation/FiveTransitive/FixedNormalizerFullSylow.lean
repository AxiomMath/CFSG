module

public import CFSG.Permutation.FiveTransitive.CompatiblePreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.FixedNormalizerFullSylow

open MulAction FixedNormalizerAction

theorem exists_containing
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (B : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B) (hQB : Inside Q ≤ B) :
    ∃ A : Sylow 2 (Normalizer Q), B ≤ A ∧
      (A : Subgroup (Normalizer Q)) ⊓
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q ∧
      ((toPermHom (Normalizer Q) (Fixed (X := X) Q)).comp
        (A : Subgroup (Normalizer Q)).subtype).ker =
          (Inside Q).subgroupOf (A : Subgroup (Normalizer Q)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hBA⟩ := hB.exists_le_sylow
  obtain ⟨hk, hkr⟩ := CompatiblePreimageSylow.kernel_eq
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (Inside Q) A
    (FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q)
    (FixedNormalizerCyclicPreimageSylow.kernel_pgroup_le_inside Q S hS)
    (hQB.trans hBA) A.isPGroup'
  exact ⟨A, hBA, hk, hkr⟩

private theorem image_card
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤) (A : Sylow 2 (Normalizer Q)) :
    Nat.card ((A : Subgroup (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))) = 16 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp himage
  let W := Sylow.mapSurjective hf A
  change Nat.card W = 16
  rw [W.card_eq_multiplicity, Nat.card_perm, hseven]
  change 2 ^ (5040).factorization 2 = 16
  rw [show 5040 = 2 ^ 4 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  norm_num

theorem card_eq_thirty_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤) (A : Sylow 2 (Normalizer Q))
    (hQA : Inside Q ≤ (A : Subgroup (Normalizer Q)))
    (hker : ((toPermHom (Normalizer Q) (Fixed (X := X) Q)).comp
      (A : Subgroup (Normalizer Q)).subtype).ker =
        (Inside Q).subgroupOf (A : Subgroup (Normalizer Q))) :
    Nat.card A = 32 := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let φ := f.comp (A : Subgroup (Normalizer Q)).subtype
  have hk : Nat.card φ.ker = 2 := by
    rw [hker]
    calc
      Nat.card ((Inside Q).subgroupOf (A : Subgroup (Normalizer Q))) =
          Nat.card (Inside Q) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv
      _ = Nat.card Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv
      _ = 2 := hQ
  have hr : φ.range = (A : Subgroup (Normalizer Q)).map f := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hi : φ.ker.index = 16 := by
    rw [Subgroup.index_ker, hr]
    exact image_card Q hseven himage A
  have hc := φ.ker.card_mul_index
  rw [hk, hi] at hc
  exact hc.symm

theorem index_two
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hBA : B ≤ A) (hA : Nat.card A = 32) (hB : Nat.card B = 16) :
    (B.subgroupOf A).index = 2 ∧ (B.subgroupOf A).Normal ∧
      ∀ u : A, u ^ 2 ∈ B.subgroupOf A := by
  have hcB : Nat.card (B.subgroupOf A) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv).trans hB
  have hi := (B.subgroupOf A).card_mul_index
  rw [hcB, hA] at hi
  have hi2 : (B.subgroupOf A).index = 2 := by omega
  have hn := Subgroup.normal_of_index_eq_two hi2
  let _ := hn
  exact ⟨hi2, hn, fun u => hi2 ▸ (B.subgroupOf A).pow_index_mem u⟩

end FiveTransitive.FixedNormalizerFullSylow

end CFSG
