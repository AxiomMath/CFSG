module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofAffine

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGReflDatum (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {N : Type}
    (X : Matrix N N ℤ) where
  refl : N → MulAut ↥Bs
  mem : ∀ i, refl i ∈ ggInduced ⊤ Bs
  coroot : N → V
  root : N → Module.Dual (ZMod p) V
  lin : ∀ i w, ggLin (p := p) ι (refl i) w = w - root i w • coroot i
  pair : ∀ i j, root i (coroot j) = (X i j : ZMod p)
  diag : ∀ i, X i i = 2
  ind : LinearIndependent (ZMod p) coroot
  span : Submodule.span (ZMod p) (Set.range coroot) = ⊤

section Datum

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

def GGReflDatum.comap {ι : Additive ↥Bs ≃+ V} {N N' : Type} {X : Matrix N N ℤ}
    (D : GGReflDatum p ι X) (σ : N' ≃ N) : GGReflDatum p ι (X.submatrix σ σ) where
  refl := fun i => D.refl (σ i)
  mem := fun i => D.mem (σ i)
  coroot := fun i => D.coroot (σ i)
  root := fun i => D.root (σ i)
  lin := fun i w => D.lin (σ i) w
  pair := fun i j => D.pair (σ i) (σ j)
  diag := fun i => D.diag (σ i)
  ind := D.ind.comp σ σ.injective
  span := by
    have h : Set.range (fun i => D.coroot (σ i)) = Set.range D.coroot := by
      rw [Set.range_comp', σ.surjective.range_eq, Set.image_univ]
    rw [h, D.span]

variable {ι : Additive ↥Bs ≃+ V} {N : Type} [Fintype N] [DecidableEq N] {X : Matrix N N ℤ}

theorem GGReflDatum.sum_root_eq_zero (D : GGReflDatum p ι X) {n : N → ℕ}
    (hn : ∀ i, ∑ j, (n j : ℤ) * X j i = 0) : ∑ j, (n j : ZMod p) • D.root j = 0 := by
  apply LinearMap.ext_on D.span
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, D.pair]
  have hcast : ((∑ j, (n j : ℤ) * X j i : ℤ) : ZMod p)
      = ∑ j, (n j : ZMod p) * (X j i : ZMod p) := by
    push_cast
    rfl
  rw [← hcast, hn i, Int.cast_zero]

@[expose] def ggStepRoot (X : Matrix N N ℤ) (k : N) (c : N → ℤ) : N → ℤ :=
  fun j => c j - if j = k then ∑ i, c i * X i k else 0

@[expose] def ggStepCoroot (X : Matrix N N ℤ) (k : N) (d : N → ℤ) : N → ℤ :=
  fun j => d j - if j = k then ∑ i, X k i * d i else 0

@[expose] def ggWordRoot (X : Matrix N N ℤ) (w : List N) (j : N) : N → ℤ :=
  w.foldr (ggStepRoot X) fun i => if i = j then 1 else 0

@[expose] def ggWordCoroot (X : Matrix N N ℤ) (w : List N) (j : N) : N → ℤ :=
  w.foldr (ggStepCoroot X) fun i => if i = j then 1 else 0

theorem ggWordCoroot_apply_eq_zero {j₀ : N} {w : List N} (hw : ∀ k ∈ w, k ≠ j₀) {j₁ : N}
    (hj₁ : j₁ ≠ j₀) : ggWordCoroot X w j₁ j₀ = 0 := by
  revert hw
  induction w with
  | nil =>
      intro _
      have hj₁' : j₀ ≠ j₁ := fun h => hj₁ h.symm
      simp [ggWordCoroot, hj₁']
  | cons k w ih =>
      intro hw
      have hk : k ≠ j₀ := hw k (List.mem_cons_self ..)
      have hw' : ∀ k' ∈ w, k' ≠ j₀ := fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')
      change ggStepCoroot X k (ggWordCoroot X w j₁) j₀ = 0
      unfold ggStepCoroot
      rw [ih hw']
      have hk' : j₀ ≠ k := fun h => hk h.symm
      simp [hk']

end Datum

end CFSG.StandardType
