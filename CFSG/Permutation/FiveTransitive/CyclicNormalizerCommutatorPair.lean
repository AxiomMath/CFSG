module

public import CFSG.Permutation.FiveTransitive.CyclicCentralCommutatorPair
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.CyclicNormalizerCommutatorPair

open MulAction FixedNormalizerAction

private theorem commutator_mem
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B Q : Subgroup G) (hker : B ⊓ f.ker = Q)
    (himage : IsMulCommutative (B.map f)) (x y : B) : ⁅x.val, y.val⁆ ∈ Q := by
  have hc : Commute (f x.val) (f y.val) :=
    congrArg Subtype.val ((isMulCommutative_iff.mp himage)
      (⟨f x.val, ⟨x.val, x.property, rfl⟩⟩ : B.map f)
      ⟨f y.val, ⟨y.val, y.property, rfl⟩⟩)
  apply hker.le
  change ⁅x.val, y.val⁆ ∈ B ∧ ⁅x.val, y.val⁆ ∈ f.ker
  constructor
  · simpa only [commutatorElement_def] using B.mul_mem
      (B.mul_mem (B.mul_mem x.property y.property) (B.inv_mem x.property)) (B.inv_mem y.property)
  · rw [MonoidHom.mem_ker, map_commutatorElement, hc.commutator_eq]

private theorem pair_eq_and_commute
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (B : Subgroup (Normalizer Q))
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (himage : IsMulCommutative (B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (hcentral : ∀ u : B, ∀ q : Q, Commute u.val.val q.val)
    (a : Q) (ha : orderOf a = 2)
    (x z y : B) (hy : y.val.val ^ 2 = 1)
    (hxy : ¬ Commute x.val.val y.val.val) (hzy : ¬ Commute z.val.val y.val.val) :
    ⁅x.val.val, y.val.val⁆ = a.val ∧ ⁅z.val.val, y.val.val⁆ = a.val ∧
      Commute (x.val.val * z.val.val) y.val.val := by
  let _ : IsCyclic Q := hcyclic
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hmem (u v : B) : ⁅u.val.val, v.val.val⁆ ∈ Q := by
    have hm := commutator_mem f B (Inside Q) hker himage u v
    change ⁅u.val, v.val⁆.val ∈ Q at hm
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hm
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hane : a ≠ 1 := by
    intro he
    rw [he, orderOf_one] at ha
    contradiction
  exact CyclicCentralCommutatorPair.pair_eq_and_commute Q a ha2 hane
    x.val.val z.val.val y.val.val hy (hcentral x) (hcentral y)
    (hmem x y) (hmem z y) hxy hzy

theorem exists_pair_eq_and_commute
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (B : Subgroup (Normalizer Q))
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (himage : IsMulCommutative (B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (hcentral : ∀ u : B, ∀ q : Q, Commute u.val.val q.val)
    (x z y : B) (hy : y.val.val ^ 2 = 1)
    (hxy : ¬ Commute x.val.val y.val.val) (hzy : ¬ Commute z.val.val y.val.val) :
    ∃ a : Q, orderOf a = 2 ∧
      ⁅x.val.val, y.val.val⁆ = a.val ∧ ⁅z.val.val, y.val.val⁆ = a.val ∧
      Commute (x.val.val * z.val.val) y.val.val := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hm : ⁅x.val.val, y.val.val⁆ ∈ Q := by
    have hm := commutator_mem f B (Inside Q) hker himage x y
    change ⁅x.val, y.val⁆.val ∈ Q at hm
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hm
  let a : Q := ⟨⁅x.val.val, y.val.val⁆, hm⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext
    (CyclicCentralCommutatorPair.commutator_square x.val.val y.val.val hy (hcentral y a))
  have hane : a ≠ 1 := by
    intro he
    exact hxy (commutatorElement_eq_one_iff_commute.mp (congrArg (fun q : Q => q.val) he))
  have ha : orderOf a = 2 := orderOf_eq_prime ha2 hane
  exact ⟨a, ha, pair_eq_and_commute Q hcyclic B hker himage hcentral a ha x z y hy hxy hzy⟩

end FiveTransitive.CyclicNormalizerCommutatorPair

end CFSG
