module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Restrict
public import CFSG.SignalizerFunctorTheorem.Inheritance.Induction

public section

universe u

namespace CFSG.SignalizerFunctorTheorem

theorem exists_centralizer_section_of_normalizer {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X : Type*} [Group X] [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x)
    {A W : Subgroup G} (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hA : ∀ a ∈ A, a ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card W)) (hfaith : NoFaithfulSection A W)
    (hXW : IsSectionOf X W) :
    ∃ a ∈ A, a ≠ 1 ∧ IsSectionOf X ↥(W ⊓ Subgroup.centralizer {a}) := by
  have hWB : W ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer
  set B : Subgroup G := Subgroup.normalizer (W : Set G) with hB
  have : (W.subgroupOf B).Normal := Subgroup.normal_in_normalizer
  have hcard : Nat.card (W.subgroupOf B) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWB).toEquiv
  have hA₁ : ∀ a ∈ A.subgroupOf B, a ^ p = 1 := by
    intro a ha
    exact Subtype.ext (hA a ha)
  have hXW₁ : IsSectionOf X (W.subgroupOf B) :=
    hXW.trans (IsSectionOf.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hWB))
  obtain ⟨a₁, ha₁, ha₁1, hsec⟩ := exists_centralizer_section hp hnc _ (W.subgroupOf B)
    (A.subgroupOf B) rfl hA₁ (hcard ▸ hcop) (noFaithfulSection_subgroupOf hAW hfaith) hXW₁
  refine ⟨a₁, ha₁, fun h => ha₁1 (Subtype.ext h), ?_⟩
  let j : ↥(W.subgroupOf B ⊓ Subgroup.centralizer {a₁}) →* ↥(W ⊓ Subgroup.centralizer {(a₁ : G)}) :=
    ((B.subtype).comp (W.subgroupOf B ⊓ Subgroup.centralizer {a₁}).subtype).codRestrict _ fun y =>
      ⟨y.2.1, by
        have h1 : ((y : ↥(W.subgroupOf B ⊓ Subgroup.centralizer {a₁})) : B) ∈
            Subgroup.centralizer ({a₁} : Set B) := y.2.2
        show ((y : B) : G) ∈ Subgroup.centralizer ({(a₁ : G)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
        exact congrArg Subtype.val h1⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(W ⊓ Subgroup.centralizer {(a₁ : G)}) => (z : G)) h
  exact hsec.of_injective j hj

end CFSG.SignalizerFunctorTheorem
