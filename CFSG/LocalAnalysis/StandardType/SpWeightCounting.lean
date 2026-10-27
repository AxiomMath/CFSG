module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

namespace SpCount

open Matrix

section Fibres

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [DecidableEq κ] {Ω : Type*} [Field Ω]

theorem card_fiber_le_card_fiber_of_isUnit (wt : ι → κ) (inv : κ → κ)
    (hinv : Function.Involutive inv) {M : Matrix ι ι Ω} (hM : IsUnit M)
    (hMw : ∀ α β, M α β ≠ 0 → wt β = inv (wt α)) (k : κ) :
    (Finset.univ.filter fun α => wt α = k).card ≤
      (Finset.univ.filter fun α => wt α = inv k).card := by
  classical
  set Sk := Finset.univ.filter fun α => wt α = k with hSk
  set Sk' := Finset.univ.filter fun α => wt α = inv k with hSk'
  let q : ι → Submodule Ω Ω := fun β => if β ∈ Sk' then ⊤ else ⊥
  let p : Submodule Ω (ι → Ω) := Submodule.pi Set.univ q
  have hmem : ∀ x ∈ p, ∀ i, i ∉ Sk' → x i = 0 := by
    intro x hx i hi
    have := (Submodule.mem_pi.mp hx) i trivial
    simpa [q, hi] using this
  have hli : LinearIndependent Ω M.row := Matrix.linearIndependent_rows_of_isUnit hM
  have hli_sub : LinearIndependent Ω (fun α : Sk => M.row α.val) :=
    hli.comp (fun α : Sk => α.val) Subtype.val_injective
  have hrow_mem : ∀ α : Sk, (fun α : Sk => M.row α.val) α ∈ p := by
    intro α
    rw [Submodule.mem_pi]
    intro β _
    by_cases hβ : β ∈ Sk'
    · simp [q, hβ]
    · have hzero : M α.val β = 0 := by
        by_contra hne
        exact hβ (Finset.mem_filter.mpr ⟨Finset.mem_univ β, by
          rw [hMw α.val β hne, (Finset.mem_filter.mp α.2).2]⟩)
      have hq : q β = ⊥ := by simp [q, hβ]
      rw [hq]
      simpa [Matrix.row] using hzero
  let v : Sk → p := fun α => ⟨M.row α.val, hrow_mem α⟩
  have hli_p : LinearIndependent Ω v := LinearIndependent.of_comp p.subtype hli_sub
  have hle1 : Fintype.card Sk ≤ Module.finrank Ω p := hli_p.fintype_card_le_finrank
  let f : p →ₗ[Ω] (Sk' → Ω) :=
    LinearMap.pi fun β : Sk' => (LinearMap.proj (β : ι)).comp p.subtype
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ Sk'
    · have := congrFun hxy ⟨i, hi⟩
      simpa [f] using this
    · rw [hmem x.val x.2 i hi, hmem y.val y.2 i hi]
  have hle2 : Module.finrank Ω p ≤ Module.finrank Ω (Sk' → Ω) :=
    LinearMap.finrank_le_finrank_of_injective hf_inj
  calc Sk.card = Fintype.card Sk := (Fintype.card_coe Sk).symm
    _ ≤ Module.finrank Ω p := hle1
    _ ≤ Module.finrank Ω (Sk' → Ω) := hle2
    _ = Fintype.card Sk' := Module.finrank_pi Ω
    _ = Sk'.card := Fintype.card_coe Sk'

theorem card_fiber_eq_of_isUnit (wt : ι → κ) (inv : κ → κ) (hinv : Function.Involutive inv)
    {M : Matrix ι ι Ω} (hM : IsUnit M) (hMw : ∀ α β, M α β ≠ 0 → wt β = inv (wt α)) (k : κ) :
    (Finset.univ.filter fun α => wt α = k).card =
      (Finset.univ.filter fun α => wt α = inv k).card := by
  refine le_antisymm (card_fiber_le_card_fiber_of_isUnit wt inv hinv hM hMw k) ?_
  have h := card_fiber_le_card_fiber_of_isUnit wt inv hinv hM hMw (inv k)
  rwa [hinv k] at h

theorem card_fiber_add_card_fiber_le (wt : ι → κ) (inv : κ → κ) (hinv : Function.Involutive inv)
    {M : Matrix ι ι Ω} (hM : IsUnit M) (hMw : ∀ α β, M α β ≠ 0 → wt β = inv (wt α)) {k : κ}
    (hk : k ≠ inv k) :
    2 * (Finset.univ.filter fun α => wt α = k).card ≤ Fintype.card ι ∧
      (2 * (Finset.univ.filter fun α => wt α = k).card = Fintype.card ι →
        ∀ α, wt α = k ∨ wt α = inv k) := by
  classical
  set Sk := Finset.univ.filter fun α => wt α = k with hSk
  set Sk' := Finset.univ.filter fun α => wt α = inv k with hSk'
  have heq : Sk.card = Sk'.card := card_fiber_eq_of_isUnit wt inv hinv hM hMw k
  have hdisj : Disjoint Sk Sk' := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have h1 : wt a = k := (Finset.mem_filter.mp ha).2
    have h2 : wt a = inv k := (Finset.mem_filter.mp ha').2
    exact hk (h1.symm.trans h2)
  refine ⟨?_, ?_⟩
  · calc 2 * Sk.card = Sk.card + Sk.card := by ring
      _ = Sk.card + Sk'.card := by rw [heq]
      _ = (Sk ∪ Sk').card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  · intro h2 α
    have hcard : (Sk ∪ Sk').card = Fintype.card ι := by
      rw [Finset.card_union_of_disjoint hdisj, ← heq, ← two_mul]
      exact h2
    have huniv : Sk ∪ Sk' = Finset.univ := Finset.eq_univ_of_card _ hcard
    have : α ∈ Sk ∪ Sk' := by rw [huniv]; exact Finset.mem_univ α
    rcases Finset.mem_union.mp this with h | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · exact Or.inr (Finset.mem_filter.mp h).2

end Fibres

section CubeRoots

theorem card_le_three_of_injective_cube {D : Type*} [Fintype D] {Ω : Type*} [Field Ω] (χ : D → Ω)
    (hχ : Function.Injective χ) (h3 : ∀ a, χ a ^ 3 = 1) : Fintype.card D ≤ 3 := by
  classical
  have himg : (Finset.univ.image χ).card = Fintype.card D := by
    rw [Finset.card_image_of_injective Finset.univ hχ, Finset.card_univ]
  have hsubset : Finset.univ.image χ ⊆ Polynomial.nthRootsFinset 3 (1 : Ω) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, -, ha⟩
    rw [Polynomial.mem_nthRootsFinset (by norm_num : (0 : ℕ) < 3) (1 : Ω), ← ha]
    exact h3 a
  calc Fintype.card D = (Finset.univ.image χ).card := himg.symm
    _ ≤ (Polynomial.nthRootsFinset 3 (1 : Ω)).card := Finset.card_le_card hsubset
    _ ≤ (Polynomial.nthRoots 3 (1 : Ω)).card := by
        rw [Polynomial.nthRootsFinset_def]
        exact Multiset.toFinset_card_le (α := Ω) _
    _ ≤ 3 := Polynomial.card_nthRoots 3 (1 : Ω)

end CubeRoots

end SpCount

end CFSG.StandardType
