module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Generic coset-fiber involution API

For an involution `y` and a subgroup `A`, the involutions lying in the
right coset `A·y` are exactly the products `i·y` with `i ∈ I_A(y)` and
`i ≠ y` (the case `i = y` would give `y·y = 1`, which is not an
involution).  This is the coset-fiber version of Fact 1.4
(`fact_1_4_involution_mul`).

The involutions are partitioned over the right-coset space `G ⧸ A` by
the projection `x ↦ x⁻¹ mod A` (whose fiber over `y⁻¹ mod A` is exactly
`J ∩ A·y`).  The `Jₙ` / `bₙ` bookkeeping then records, for each
`n : ℕ`, the involutions in non-base fibers of size `n` and the number
`bₙ` of such fibers:

* `|Jₙ| = n·bₙ`;
* `|G:A| = 1 + Σₙ bₙ` (the `1` is the base coset `A`);
* `|J| = |J ∩ A| + Σₙ n·bₙ`.

The sums are finite: a fiber of the involution projection has size at
most `|J|`, so `n` ranges over `Finset.range (|J| + 1)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- The elements of `A` inverted by `y`. -/
@[expose] public def invertedIn {G : Type u} [Group G] (A : Subgroup G) (y : G) : Set G :=
  (A : Set G) ∩ invertedElements (⊤ : Subgroup G) y

/-- The ambient and subgroup forms of the inverted set agree.  This exposed
interface is used by source-shaped coset counts whose generic fiber API is
phrased with `invertedIn`. -/
public theorem invertedIn_eq_invertedElements
    {G : Type u} [Group G] (A : Subgroup G) (y : G) :
    invertedIn A y = invertedElements A y := by
  ext x
  simp [invertedIn, invertedElements]

/-- The involutions in the right coset `A·y` are exactly the products
`i·y` with `i ∈ I_A(y)` and `i ≠ y`. -/
public def involution_coset_fiber_eq_inverted_mul
    {G : Type u} [Group G] (A : Subgroup G) {y : G} (hy : IsInvolution y) :
    {x : G // IsInvolution x ∧ x ∈ (A : Set G) * ({y} : Set G)} ≃
      {i : G // i ∈ invertedIn A y ∧ i ≠ y} :=
  { toFun := fun x =>
      ⟨x.1 * y⁻¹, by
        rcases (Set.mem_mul.mp x.2.2) with ⟨a, ha, z, hz, hxz⟩
        have hzy : z = y := by simpa using hz
        have hxeq : x.1 = a * y := by
          calc
            x.1 = a * z := hxz.symm
            _ = a * y := by rw [hzy]
        have hInvA : y * a * y = a⁻¹ :=
          (fact_1_4_involution_mul hy).1 (by simpa [hxeq] using x.2.1) |>.2
        have hA : x.1 * y⁻¹ ∈ (A : Set G) := by
          rw [hxeq]
          simpa using ha
        have hInv : x.1 * y⁻¹ ∈ invertedElements (⊤ : Subgroup G) y := by
          rw [mem_invertedElements_top_iff hy]
          rw [hxeq]
          simpa using hInvA
        exact ⟨hA, hInv⟩, by
        intro h
        have hx1 : x.1 = 1 := by
          calc
            x.1 = (x.1 * y⁻¹) * y := by group
            _ = y * y := by rw [h]
            _ = 1 := by simpa [pow_two] using hy.2
        exact x.2.1.1 hx1⟩
    invFun := fun i =>
      ⟨i.1 * y, by
        rw [fact_1_4_involution_mul hy]
        constructor
        · exact i.2.2
        · exact (mem_invertedElements_top_iff hy).1 i.2.1.2, by
        exact Set.mem_mul.mpr
          ⟨i.1, i.2.1.1, y, by simp, rfl⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      group
    right_inv := by
      intro i
      apply Subtype.ext
      group }

/-- The set form of `involution_coset_fiber_eq_inverted_mul`:
`J ∩ A·y = I_A(y)·y` (with `I_A(y)` punctured at `y`). -/
public theorem involution_coset_fiber_set_eq
    {G : Type u} [Group G] (A : Subgroup G) {y : G} (hy : IsInvolution y) :
    {x : G | IsInvolution x ∧ x ∈ (A : Set G) * ({y} : Set G)} =
      (fun i : G => i * y) '' {i : G | i ∈ invertedIn A y ∧ i ≠ y} := by
  ext x
  constructor
  · intro hx
    let ex := (involution_coset_fiber_eq_inverted_mul A hy) ⟨x, hx⟩
    have hxeq : x = ex.1 * y := by
      change x = (x * y⁻¹) * y
      group
    exact ⟨ex.1, ex.2, hxeq.symm⟩
  · intro hx
    rcases hx with ⟨i, hi, rfl⟩
    have hInv : IsInvolution (i * y) := by
      rw [fact_1_4_involution_mul hy]
      constructor
      · exact hi.2
      · exact (mem_invertedElements_top_iff hy).1 hi.1.2
    have hCoset : i * y ∈ (A : Set G) * ({y} : Set G) :=
      Set.mem_mul.mpr
        ⟨i, hi.1.1, y, by simp, rfl⟩
    exact ⟨hInv, hCoset⟩

/-- The cardinality form of `involution_coset_fiber_eq_inverted_mul`. -/
public theorem involution_coset_fiber_card
    {G : Type u} [Group G] (A : Subgroup G) {y : G} (hy : IsInvolution y) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ (A : Set G) * ({y} : Set G)} =
      Nat.card {i : G // i ∈ invertedIn A y ∧ i ≠ y} :=
  Nat.card_congr (involution_coset_fiber_eq_inverted_mul A hy)

/-- The right-coset projection `x ↦ x⁻¹ mod A`; its fibers are the right
cosets `A·y`. -/
@[expose] public def cosetInvolution_proj {G : Type u} [Group G]
    (A : Subgroup G) (x : G) : G ⧸ A :=
  QuotientGroup.mk (x⁻¹)

/-- The base coset `A`, represented by `1⁻¹ mod A`. -/
@[expose] public def cosetInvolution_base {G : Type u} [Group G]
    (A : Subgroup G) : G ⧸ A :=
  QuotientGroup.mk (1⁻¹ : G)

/-- Membership in the right coset `A·y` is exactly equality of the
right-coset projections. -/
private theorem cosetInvolution_proj_eq_iff_mem_rightCoset
    {G : Type u} [Group G] (A : Subgroup G) {x y : G} :
    cosetInvolution_proj A x = cosetInvolution_proj A y ↔
      x ∈ (A : Set G) * ({y} : Set G) := by
  constructor
  · intro hx
    have hm : x * y⁻¹ ∈ A := by
      simpa [cosetInvolution_proj] using (QuotientGroup.eq (s := A)).mp hx
    exact Set.mem_mul.mpr ⟨x * y⁻¹, hm, y, by simp, by group⟩
  · intro hx
    rcases (Set.mem_mul.mp hx) with ⟨a, ha, z, hz, hxz⟩
    have hzy : z = y := by simpa using hz
    have hxy : x = a * y := by
      calc
        x = a * z := hxz.symm
        _ = a * y := by rw [hzy]
    apply (QuotientGroup.eq (s := A)).mpr
    rw [hxy]
    simpa using ha

/-- The fiber of the involution projection over the base coset is exactly
the involutions of `A`. -/
public def involution_coset_base_fiber_equiv
    {G : Type u} [Group G] (A : Subgroup G) :
    {x : G // IsInvolution x ∧ cosetInvolution_proj A x = cosetInvolution_base A} ≃
      {x : G // IsInvolution x ∧ x ∈ A} :=
  { toFun := fun x => ⟨x.1, x.2.1, by
      have hm : x.1 ∈ A := by
        simpa [cosetInvolution_proj, cosetInvolution_base]
          using (QuotientGroup.eq (s := A)).mp x.2.2
      exact hm⟩
    invFun := fun x => ⟨x.1, x.2.1, by
      apply (QuotientGroup.eq (s := A)).mpr
      simpa [cosetInvolution_proj, cosetInvolution_base] using x.2.2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }

/-- The fiber of the involution projection over `y⁻¹ mod A` consists
exactly of the punctured inverted set `I_A(y)`. -/
public def involution_coset_fiber_equiv_inverted
    {G : Type u} [Group G] (A : Subgroup G) {y : G} (hy : IsInvolution y) :
    {x : G // IsInvolution x ∧ cosetInvolution_proj A x = cosetInvolution_proj A y} ≃
      {i : G // i ∈ invertedIn A y ∧ i ≠ y} := by
  let e1 : {x : G // IsInvolution x ∧
        cosetInvolution_proj A x = cosetInvolution_proj A y} ≃
      {x : G // IsInvolution x ∧ x ∈ (A : Set G) * ({y} : Set G)} :=
    { toFun := fun x =>
        ⟨x.1, x.2.1, (cosetInvolution_proj_eq_iff_mem_rightCoset A).mp x.2.2⟩
      invFun := fun x =>
        ⟨x.1, x.2.1, (cosetInvolution_proj_eq_iff_mem_rightCoset A).mpr x.2.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact e1.trans (involution_coset_fiber_eq_inverted_mul A hy)

/-- The fiber of a map `π : G → Ω` over `ω`, restricted to involutions. -/
@[expose] public def involutionFiber {G : Type u} [Group G] {Ω : Type u}
    (π : G → Ω) (ω : Ω) : Type u :=
  {x : G // IsInvolution x ∧ π x = ω}

/-- The involutions in non-base fibers of size `n`. -/
public def involutionJ_n {G : Type u} [Group G] {Ω : Type u}
    (π : G → Ω) (ω0 : Ω) (n : ℕ) : Type u :=
  {x : G // IsInvolution x ∧ π x ≠ ω0 ∧
    Nat.card (involutionFiber π (π x)) = n}

/-- The number of non-base fibers of size `n`. -/
public def involutionB_n {G : Type u} [Group G] {Ω : Type u}
    (π : G → Ω) (ω0 : Ω) (n : ℕ) : ℕ :=
  Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = n}

/-- The canonical fiber partition of the involutions over `Ω`. -/
public def involution_fiber_partition_equiv
    {G : Type u} [Group G] {Ω : Type u} (π : G → Ω) :
    {x : G // IsInvolution x} ≃ Σ ω : Ω, involutionFiber π ω :=
  { toFun := fun x => ⟨π x.1, ⟨x.1, x.2, rfl⟩⟩
    invFun := fun p => ⟨p.2.1, p.2.2.1⟩
    left_inv := by intro x; rfl
    right_inv := by
      rintro ⟨ω, ⟨x, hx, hω⟩⟩
      cases hω
      rfl }

/-- The fiber partition cardinality: `|J| = Σ_ω |J ∩ π⁻¹(ω)|`. -/
public theorem involution_fiber_partition_card
    {G : Type u} [Group G] [Finite G] {Ω : Type u} [Fintype Ω]
    (π : G → Ω) :
    Nat.card {x : G // IsInvolution x} =
      ∑ ω : Ω, Nat.card (involutionFiber π ω) := by
  classical
  let : Fintype {x : G // IsInvolution x} := Fintype.ofFinite _
  have : ∀ ω : Ω, Finite (involutionFiber π ω) := fun ω => by
    unfold involutionFiber
    infer_instance
  exact (Nat.card_congr (involution_fiber_partition_equiv π)).trans
    Nat.card_sigma

/-- The cardinality of a finite type is the sum of its fiber cardinalities
under any map. -/
private theorem fiber_partition_card
    {α : Type u} {β : Type v} [Finite α] [Fintype β]
    (f : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // f a = b} := by
  classical
  let : Fintype α := Fintype.ofFinite _
  have e : α ≃ Σ b : β, {a : α // f a = b} :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := by intro a; rfl
      right_inv := by
        rintro ⟨b, ⟨a, h⟩⟩
        cases h
        rfl }
  calc
    Nat.card α = Nat.card (Σ b : β, {a : α // f a = b}) := Nat.card_congr e
    _ = ∑ b : β, Nat.card {a : α // f a = b} := Nat.card_sigma

/-- `|Jₙ| = n·bₙ`: the involutions in non-base fibers of size `n` number
`n` times the count of such fibers. -/
public theorem involution_J_n_card
    {G : Type u} [Group G] [Finite G] {Ω : Type u} [Fintype Ω]
    (π : G → Ω) (ω0 : Ω) (n : ℕ) :
    Nat.card (involutionJ_n π ω0 n) = n * involutionB_n π ω0 n := by
  classical
  let N : Type u := {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = n}
  let : Fintype N := Fintype.ofFinite _
  have : Finite (involutionJ_n π ω0 n) := by
    unfold involutionJ_n
    infer_instance
  let p : involutionJ_n π ω0 n → N :=
    fun x => ⟨π x.1, x.2.2.1, x.2.2.2⟩
  have hpart :
      Nat.card (involutionJ_n π ω0 n) =
        ∑ ω : N, Nat.card {x : involutionJ_n π ω0 n // p x = ω} :=
    fiber_partition_card p
  have hfiber (ω : N) :
      Nat.card {x : involutionJ_n π ω0 n // p x = ω} = n := by
    let E : {x : involutionJ_n π ω0 n // p x = ω} ≃
        involutionFiber π (ω : Ω) :=
      { toFun := fun x =>
          ⟨x.1.1, x.1.2.1, by
            have hπ : π x.1.1 = (ω : Ω) := congrArg Subtype.val x.2
            simpa [p] using hπ⟩
        invFun := fun x =>
          ⟨⟨x.1, x.2.1, by
              rw [x.2.2]
              exact ω.2.1, by
              rw [x.2.2]
              exact ω.2.2⟩, by
            apply Subtype.ext
            exact x.2.2⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro x
          apply Subtype.ext
          rfl }
    calc
      Nat.card {x : involutionJ_n π ω0 n // p x = ω} =
          Nat.card (involutionFiber π (ω : Ω)) := Nat.card_congr E
      _ = n := ω.2.2
  calc
    Nat.card (involutionJ_n π ω0 n) =
        ∑ ω : N, Nat.card {x : involutionJ_n π ω0 n // p x = ω} := hpart
    _ = ∑ ω : N, n := by
      apply Finset.sum_congr rfl
      intro ω _hω
      exact hfiber ω
    _ = n * Nat.card N := by
      rw [Finset.sum_const]
      simp [mul_comm]
    _ = n * involutionB_n π ω0 n := by rfl

/-- `|G:A| = 1 + Σₙ bₙ` for the generic projection: the base fiber gives
the `1` and `bₙ` counts all non-base fibers of size `n`. -/
public theorem involution_index_eq_one_add_sum_b
    {G : Type u} [Group G] [Finite G] {Ω : Type u} [Fintype Ω]
    (π : G → Ω) (ω0 : Ω) :
    Nat.card Ω =
      1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        involutionB_n π ω0 n := by
  classical
  let J : Type u := {x : G // IsInvolution x}
  let K : ℕ := Nat.card J + 1
  let Nonbase : Type u := {ω : Ω // ω ≠ ω0}
  let : Fintype Nonbase := Fintype.ofFinite _
  have hsize_le (ω : Nonbase) :
      Nat.card (involutionFiber π (ω : Ω)) ≤ Nat.card J := by
    exact Nat.card_le_card_of_injective
      (fun x : involutionFiber π (ω : Ω) => (⟨x.1, x.2.1⟩ : J))
      (by intro x y h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  have hΩ : Nat.card Ω = 1 + Nat.card Nonbase := by
    have : DecidableEq Ω := Classical.decEq _
    let e : Ω ≃ Option Nonbase :=
      { toFun := fun ω => if h : ω = ω0 then none else some ⟨ω, h⟩
        invFun := fun o => o.elim ω0 (fun ω => ω.1)
        left_inv := by
          intro ω
          by_cases h : ω = ω0 <;> simp [h]
        right_inv := by
          intro o
          cases o with
          | none => simp
          | some ω =>
            simp [dif_neg ω.2] }
    calc
      Nat.card Ω = Nat.card (Option Nonbase) := Nat.card_congr e
      _ = Nat.card Nonbase + 1 := by
        exact Finite.card_option
      _ = 1 + Nat.card Nonbase := by rw [add_comm]
  have hNonbase :
      Nat.card Nonbase =
        ∑ n ∈ Finset.range K, involutionB_n π ω0 n := by
    let size : Nonbase → ℕ := fun ω => Nat.card (involutionFiber π (ω : Ω))
    have hsize_mem (i : Nonbase) : size i ∈ Finset.range K :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize_le i))
    have hsum := Finset.sum_fiberwise_eq_sum_filter
      (s := (Finset.univ : Finset Nonbase)) (t := Finset.range K)
      (g := size) (f := fun _ : Nonbase => (1 : ℕ))
    have hcard (j : ℕ) :
        (∑ i ∈ Finset.univ with size i = j, (1 : ℕ)) =
          involutionB_n π ω0 j := by
      have hfin :
          Fintype.card {i : Nonbase // size i = j} =
            Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} := by
        let eFin : {i : Nonbase // size i = j} ≃
            {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} :=
          { toFun := fun i =>
              ⟨(i.1 : Ω), i.1.2, by simpa [size] using i.2⟩
            invFun := fun ω =>
              ⟨⟨(ω : Ω), ω.2.1⟩, by simpa [size] using ω.2.2⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro ω; apply Subtype.ext; rfl }
        calc
          Fintype.card {i : Nonbase // size i = j} =
              Nat.card {i : Nonbase // size i = j} := by
                rw [Nat.card_eq_fintype_card]
          _ = Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} :=
                Nat.card_congr eFin
          _ = involutionB_n π ω0 j := by rfl
      calc
        (∑ i ∈ Finset.univ with size i = j, (1 : ℕ)) =
            Fintype.card {i : Nonbase // size i = j} := by
              rw [← Finset.card_eq_sum_ones]
              exact (Fintype.card_subtype
                (p := fun i : Nonbase => size i = j)).symm
        _ = involutionB_n π ω0 j := hfin
    calc
      Nat.card Nonbase = ∑ i : Nonbase, (1 : ℕ) := by simp
      _ = ∑ i ∈ (Finset.univ : Finset Nonbase).filter
            (fun i : Nonbase => size i ∈ Finset.range K), (1 : ℕ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i _hi
            simp [hsize_mem i]
      _ = ∑ j ∈ Finset.range K, ∑ i ∈ Finset.univ with size i = j, (1 : ℕ) :=
            hsum.symm
      _ = ∑ n ∈ Finset.range K, involutionB_n π ω0 n := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact hcard j
  calc
    Nat.card Ω = 1 + Nat.card Nonbase := hΩ
    _ = 1 + ∑ n ∈ Finset.range K, involutionB_n π ω0 n := by rw [hNonbase]
    _ = 1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        involutionB_n π ω0 n := by rfl

/-- `|J| = |J ∩ A| + Σₙ n·bₙ` for the generic projection: the base fiber
is the first summand and every non-base fiber of size `n` contributes
`n`. -/
public theorem involution_J_card_eq_base_add_sum
    {G : Type u} [Group G] [Finite G] {Ω : Type u} [Fintype Ω]
    (π : G → Ω) (ω0 : Ω) :
    Nat.card {x : G // IsInvolution x} =
      Nat.card (involutionFiber π ω0) +
        ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
          n * involutionB_n π ω0 n := by
  classical
  let J : Type u := {x : G // IsInvolution x}
  let K : ℕ := Nat.card J + 1
  let Nonbase : Type u := {ω : Ω // ω ≠ ω0}
  let : Fintype Nonbase := Fintype.ofFinite _
  have hsize_le (ω : Nonbase) :
      Nat.card (involutionFiber π (ω : Ω)) ≤ Nat.card J := by
    exact Nat.card_le_card_of_injective
      (fun x : involutionFiber π (ω : Ω) => (⟨x.1, x.2.1⟩ : J))
      (by intro x y h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  have hpart :
      Nat.card J = Nat.card (involutionFiber π ω0) +
        (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) := by
    have hpartCard := involution_fiber_partition_card π
    let s : Finset Ω := Finset.univ.erase ω0
    have hsMem : ∀ ω : Ω, ω ∈ s ↔ ω ≠ ω0 := by intro ω; simp [s]
    have hsSub := Finset.sum_subtype (F := inferInstance) s hsMem
      (fun ω : Ω => Nat.card (involutionFiber π ω))
    have hErase := Finset.sum_erase_add Finset.univ
      (fun ω : Ω => Nat.card (involutionFiber π ω)) (Finset.mem_univ ω0)
    calc
      Nat.card J = ∑ ω : Ω, Nat.card (involutionFiber π ω) := hpartCard
      _ = (∑ ω ∈ s, Nat.card (involutionFiber π ω)) +
            Nat.card (involutionFiber π ω0) := by simpa [s] using hErase.symm
      _ = (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) +
            Nat.card (involutionFiber π ω0) := by rw [hsSub]
      _ = Nat.card (involutionFiber π ω0) +
            (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) := by
              rw [add_comm]
  have hnonbaseSum :
      (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) =
        ∑ n ∈ Finset.range K, n * involutionB_n π ω0 n := by
    let size : Nonbase → ℕ := fun ω => Nat.card (involutionFiber π (ω : Ω))
    have hsize_mem (i : Nonbase) : size i ∈ Finset.range K :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize_le i))
    have hsum := Finset.sum_fiberwise_eq_sum_filter
      (s := (Finset.univ : Finset Nonbase)) (t := Finset.range K)
      (g := size) (f := fun i : Nonbase => Nat.card (involutionFiber π (i : Ω)))
    have hcard (j : ℕ) :
        (∑ i ∈ Finset.univ with size i = j,
            Nat.card (involutionFiber π (i : Ω))) =
          j * involutionB_n π ω0 j := by
      have hfin :
          Fintype.card {i : Nonbase // size i = j} =
            Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} := by
        let eFin : {i : Nonbase // size i = j} ≃
            {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} :=
          { toFun := fun i =>
              ⟨(i.1 : Ω), i.1.2, by simpa [size] using i.2⟩
            invFun := fun ω =>
              ⟨⟨(ω : Ω), ω.2.1⟩, by simpa [size] using ω.2.2⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro ω; apply Subtype.ext; rfl }
        calc
          Fintype.card {i : Nonbase // size i = j} =
              Nat.card {i : Nonbase // size i = j} := by
                rw [Nat.card_eq_fintype_card]
          _ = Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j} :=
                Nat.card_congr eFin
          _ = involutionB_n π ω0 j := by rfl
      calc
        (∑ i ∈ Finset.univ with size i = j,
            Nat.card (involutionFiber π (i : Ω))) =
            (∑ i ∈ Finset.univ with size i = j, j) := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa [size] using (Finset.mem_filter.mp hi).2
        _ = j * Fintype.card {i : Nonbase // size i = j} := by
              rw [Finset.sum_const]
              simp
              rw [mul_comm]
              exact congrArg (fun z : ℕ => j * z)
                ((Fintype.card_subtype
                  (p := fun i : Nonbase => size i = j)).symm)
        _ = j * involutionB_n π ω0 j := by
              change j * Fintype.card {i : Nonbase // size i = j} =
                j * Nat.card {ω : Ω // ω ≠ ω0 ∧ Nat.card (involutionFiber π ω) = j}
              rw [← hfin]
    calc
      (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) =
          ∑ i ∈ (Finset.univ : Finset Nonbase).filter
            (fun i : Nonbase => size i ∈ Finset.range K),
            Nat.card (involutionFiber π (i : Ω)) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i _hi
            simp [hsize_mem i]
      _ = ∑ j ∈ Finset.range K, ∑ i ∈ Finset.univ with size i = j,
            Nat.card (involutionFiber π (i : Ω)) := hsum.symm
      _ = ∑ n ∈ Finset.range K, n * involutionB_n π ω0 n := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact hcard j
  calc
    Nat.card {x : G // IsInvolution x} = Nat.card J := by rfl
    _ = Nat.card (involutionFiber π ω0) +
        (∑ ω : Nonbase, Nat.card (involutionFiber π (ω : Ω))) := hpart
    _ = Nat.card (involutionFiber π ω0) +
        ∑ n ∈ Finset.range K, n * involutionB_n π ω0 n := by rw [hnonbaseSum]
    _ = Nat.card (involutionFiber π ω0) +
        ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
          n * involutionB_n π ω0 n := by rfl

/-- The coset-fiber specialization of `involutionFiber`. -/
@[expose] public def cosetInvolution_fiber {G : Type u} [Group G]
    (A : Subgroup G) (ω : G ⧸ A) : Type u :=
  involutionFiber (cosetInvolution_proj A) ω

/-- Exposed reduction of the coset fiber to the generic involution fiber. -/
public theorem cosetInvolution_fiber_eq_involutionFiber
    {G : Type u} [Group G] (A : Subgroup G) (ω : G ⧸ A) :
    cosetInvolution_fiber A ω = involutionFiber (cosetInvolution_proj A) ω := rfl

/-- The coset-fiber specialization of `involutionJ_n`. -/
public def cosetInvolution_J_n {G : Type u} [Group G]
    (A : Subgroup G) (n : ℕ) : Type u :=
  involutionJ_n (cosetInvolution_proj A) (cosetInvolution_base A) n

/-- The coset-fiber specialization of `involutionB_n`. -/
public def cosetInvolution_b {G : Type u} [Group G]
    (A : Subgroup G) (n : ℕ) : ℕ :=
  involutionB_n (cosetInvolution_proj A) (cosetInvolution_base A) n

/-- The expansion of `cosetInvolution_b` as the number of non-base fibres
of size `n`. -/
public theorem cosetInvolution_b_card
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) (n : ℕ) :
    cosetInvolution_b A n =
      Nat.card {ω : G ⧸ A // ω ≠ cosetInvolution_base A ∧
        Nat.card (involutionFiber (cosetInvolution_proj A) ω) = n} := by
  rfl

/-- `|Jₙ| = n·bₙ` for the right-coset fibers of `A`. -/
public theorem cosetInvolution_J_n_card
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) (n : ℕ) :
    Nat.card (cosetInvolution_J_n A n) = n * cosetInvolution_b A n := by
  classical
  let : Fintype (G ⧸ A) := Fintype.ofFinite _
  simpa [cosetInvolution_J_n, cosetInvolution_b] using
    (involution_J_n_card (π := cosetInvolution_proj A)
      (ω0 := cosetInvolution_base A) n)

/-- `|G:A| = 1 + Σₙ bₙ`: the base coset `A` plus the non-base right-coset
fibers, grouped by size. -/
public theorem cosetInvolution_index_eq_one_add_sum_b
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    A.index =
      1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        cosetInvolution_b A n := by
  classical
  let : Fintype (G ⧸ A) := Fintype.ofFinite _
  calc
    A.index = Nat.card (G ⧸ A) := (Subgroup.index_eq_card A).symm
    _ = 1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        involutionB_n (cosetInvolution_proj A) (cosetInvolution_base A) n :=
          involution_index_eq_one_add_sum_b (π := cosetInvolution_proj A)
            (ω0 := cosetInvolution_base A)
    _ = 1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        cosetInvolution_b A n := by simp [cosetInvolution_b]

/-- `|J| = |J ∩ A| + Σₙ n·bₙ` for the right-coset fibers of `A`. -/
public theorem cosetInvolution_J_card_eq_base_add_sum
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card {x : G // IsInvolution x} =
      Nat.card {x : G // IsInvolution x ∧ x ∈ A} +
        ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
          n * cosetInvolution_b A n := by
  classical
  let : Fintype (G ⧸ A) := Fintype.ofFinite _
  have h := involution_J_card_eq_base_add_sum (π := cosetInvolution_proj A)
    (ω0 := cosetInvolution_base A)
  have hBase := Nat.card_congr (involution_coset_base_fiber_equiv A)
  calc
    Nat.card {x : G // IsInvolution x} =
        Nat.card (involutionFiber (cosetInvolution_proj A) (cosetInvolution_base A)) +
          ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
            n * involutionB_n (cosetInvolution_proj A) (cosetInvolution_base A) n := h
    _ = Nat.card {x : G // IsInvolution x ∧ x ∈ A} +
          ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
            n * cosetInvolution_b A n := by
              change Nat.card {x : G // IsInvolution x ∧
                  cosetInvolution_proj A x = cosetInvolution_base A} +
                  ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
                    n * involutionB_n (cosetInvolution_proj A)
                      (cosetInvolution_base A) n =
                Nat.card {x : G // IsInvolution x ∧ x ∈ A} +
                  ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
                    n * cosetInvolution_b A n
              rw [hBase]
              simp [cosetInvolution_b]

end CFSG.GorensteinWalter
