module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3: basic notation

This file records the book-facing vocabulary for Peterfalvi, Section 3,
`TI-Subsets with Cyclic Normalizers`.

No BG results are imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe u

@[expose] public def cyclicTISet {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) : Set G :=
  (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))

@[expose] public def cyclicTISetSubgroup {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) : Set W :=
  {x : W | (x : G) ∈ cyclicTISet W1 W2 W}

public theorem cyclicTISet_subset {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) :
    cyclicTISet W1 W2 W ⊆ (W : Set G) := by
  intro g hg
  exact hg.1

public theorem cyclicTISet_not_mem_left {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) {g : G} (hg : g ∈ cyclicTISet W1 W2 W) :
    g ∉ (W1 : Set G) := by
  intro hg1
  exact hg.2 <| Or.inl hg1

public theorem cyclicTISet_not_mem_right {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) {g : G} (hg : g ∈ cyclicTISet W1 W2 W) :
    g ∉ (W2 : Set G) := by
  intro hg2
  exact hg.2 <| Or.inr hg2

public theorem cyclicTISet_mem_iff {G : Type u} [Group G]
    (W1 W2 W : Subgroup G) {g : G} :
    g ∈ cyclicTISet W1 W2 W ↔ g ∈ (W : Set G) ∧ g ∉ (W1 : Set G) ∧ g ∉ (W2 : Set G) := by
  constructor
  · intro hg
    exact ⟨hg.1, by
      constructor
      · exact cyclicTISet_not_mem_left W1 W2 W hg
      · exact cyclicTISet_not_mem_right W1 W2 W hg⟩
  · intro hg
    exact ⟨hg.1, by
      intro hmem
      rcases hmem with hmem | hmem
      · exact hg.2.1 hmem
      · exact hg.2.2 hmem⟩

@[expose] public def isCyclicTIHypothesis {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G) : Prop :=
  W1 ≤ W ∧ W2 ≤ W ∧
    Section2.IsInternalDirectProduct W W1 W2 ∧
    IsCyclic W ∧ Odd (Nat.card W) ∧
    Nat.card W1 ≠ 1 ∧ Nat.card W2 ≠ 1 ∧
    Section2.IsTISubsetWithNormalizer (cyclicTISet W1 W2 W) W

@[expose] public def IsCFLinearIsometry
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (T : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ α β, Section1.IsClassFunction α → Section1.IsClassFunction β →
    Section1.scalarProduct G (T α) (T β) = Section1.scalarProduct H α β

@[expose] public def MapsVirtualCharacters
    {G H : Type u} [Group G] [Group H]
    (T : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ α : Section1.ClassFunction H, Theory.Character.IsVirtualCharacter α →
    Theory.Character.IsVirtualCharacter (T α)

@[expose] public def MapsClassFunctions
    {G H : Type u} [Group G] [Group H]
    (T : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ α : Section1.ClassFunction H, Section1.IsClassFunction α →
    Section1.IsClassFunction (T α)

@[expose] public def classFunctionImage
    {G H : Type u} [Group G] [Group H]
    (T : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G) :
    Set (Section1.ClassFunction G) :=
  Set.range (fun α : {α : Section1.ClassFunction H // Section1.IsClassFunction α} =>
    T α.1)

@[expose] public def AgreesOnCyclicTISet
    {G : Type u} [Group G]
    (W1 W2 W : Subgroup G)
    (T : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
    ∀ x : G, (hx : x ∈ cyclicTISet W1 W2 W) →
    T α x = α ⟨x, cyclicTISet_subset W1 W2 W hx⟩

@[expose] public def VanishesOn {G : Type u} [Group G]
    (χ : Section1.ClassFunction G) (A : Set G) : Prop :=
  ∀ g : G, g ∈ A → χ g = 0

/-- The map package in Peterfalvi Theorem (3.2), shared by the later
numbered hypotheses and the theorem's proof. -/
@[expose] public def theorem_3_2_map_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  IsCFLinearIsometry σ ∧
    MapsVirtualCharacters σ ∧
    (∀ α : Section1.ClassFunction W,
      Section2.CFOn W (cyclicTISet W1 W2 W) α →
        σ α = Section1.inducedCF W α) ∧
    MapsClassFunctions σ ∧
    σ (Section1.principalCharacter W) = Section1.principalCharacter G ∧
    AgreesOnCyclicTISet W1 W2 W σ ∧
    ∀ χ : Section1.ClassFunction G,
      Section1.IsIrreducibleCharacterOnGroup χ →
        χ ∉ classFunctionImage σ →
          VanishesOn χ (cyclicTISet W1 W2 W)

@[expose] public def IsSignedIrreducibleCharacter
    {G : Type u} [Group G] [Finite G] (χ : Section1.ClassFunction G) : Prop :=
  ∃ ε : ℂ, Section1.IsSign ε ∧
    ∃ μ : Section1.ClassFunction G, Section1.IsIrreducibleCharacterOnGroup μ ∧
      χ = ε • μ

@[expose] public def IsBasisForCFOn
    {G : Type u} [Group G] [Finite G] (W : Subgroup G) (A : Set G)
    {ι : Type*} [Fintype ι] (φ : ι → Section1.ClassFunction W) : Prop :=
  (∀ i, Section2.CFOn W A (φ i)) ∧
    LinearIndependent ℂ φ ∧
    ∀ ψ : Section1.ClassFunction W, Section2.CFOn W A ψ →
      ∃ c : ι → ℂ, ψ = ∑ i, c i • φ i

@[expose] public def IsOrthonormalDoubleFamily
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (χ : I → J → Section1.ClassFunction G) : Prop :=
  ∀ p q : I × J,
    Section1.scalarProduct G (χ p.1 p.2) (χ q.1 q.2) =
      if p = q then 1 else 0

public theorem isOrthonormalDoubleFamily_apply
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {χ : I → J → Section1.ClassFunction G}
    (hχ : IsOrthonormalDoubleFamily χ) (p q : I × J) :
    Section1.scalarProduct G (χ p.1 p.2) (χ q.1 q.2) =
      if p = q then 1 else 0 :=
  hχ p q

public structure OmegaSystem
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W) : Prop where
  card_left : Fintype.card I = Nat.card W1
  card_right : Fintype.card J = Nat.card W2
  principal : ω i0 j0 = Section1.principalCharacter W
  left_kernel : ∀ i, Section1.subgroupInKernel' (ω i j0) (W2.subgroupOf W)
  right_kernel : ∀ j, Section1.subgroupInKernel' (ω i0 j) (W1.subgroupOf W)
  left_kernel_exact :
    ∀ χ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup χ →
        (Section1.subgroupInKernel' χ (W2.subgroupOf W) ↔ ∃ i, χ = ω i j0)
  right_kernel_exact :
    ∀ χ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup χ →
        (Section1.subgroupInKernel' χ (W1.subgroupOf W) ↔ ∃ j, χ = ω i0 j)
  product : ∀ i j x, ω i j x = ω i j0 x * ω i0 j x
  degree_one : ∀ i j, Section1.degree (ω i j) = 1
  is_class : ∀ i j, Section1.IsClassFunction (ω i j)
  irreducible : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (ω i j)
  orthonormal : IsOrthonormalDoubleFamily ω
  pairwise_eq : ∀ {i i' j j'}, ω i j = ω i' j' → i = i' ∧ j = j'
  all_irreducibles :
    ∀ χ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup χ → ∃ i j, χ = ω i j

@[expose] public def alphaIJ
    {G : Type u} [Group G] (W : Subgroup G)
    {I J : Type*} (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W) (i : I) (j : J) :
    Section1.ClassFunction W :=
  Section1.principalCharacter W - ω i j0 - ω i0 j + ω i j

end CFSG.Section3
