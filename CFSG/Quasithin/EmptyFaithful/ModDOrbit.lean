module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.ModD

variable {Γ M ι : Type*} [Group Γ] [Group M]

@[expose] def stabSub (φ : Γ →* MulAut M) (z : M) : Subgroup Γ where
  carrier := {g | φ g z = z}
  mul_mem' := by
    intro a b ha hb
    have ha' : φ a z = z := ha
    have hb' : φ b z = z := hb
    show φ (a * b) z = z
    rw [map_mul, MulAut.mul_apply, hb', ha']
  one_mem' := by
    show φ 1 z = z
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : φ a z = z := ha
    show φ a⁻¹ z = z
    calc φ a⁻¹ z = φ a⁻¹ (φ a z) := by rw [ha']
      _ = z := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_stabSub {φ : Γ →* MulAut M} {z : M} {g : Γ} : g ∈ stabSub φ z ↔ φ g z = z := Iff.rfl

theorem apply_inv_mul_eq {φ : Γ →* MulAut M} {z : M} {g g' : Γ} (h : φ g z = φ g' z) :
    φ (g⁻¹ * g') z = z := by
  rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem exists_label (φ : Γ →* MulAut M) (z : M) (π : Γ →* Equiv.Perm ι) (i₀ : ι)
    (hst : ∀ g, φ g z = z ↔ π g i₀ = i₀) :
    ∃ ε : M → ι, (∀ g, ε (φ g z) = π g i₀) ∧
      (∀ m n, (∃ g, φ g z = m) → (∃ g, φ g z = n) → ε m = ε n → m = n) ∧
      (∀ g m, (∃ h, φ h z = m) → ε (φ g m) = π g (ε m)) := by
  classical
  have key : ∀ g g', φ g z = φ g' z → π g i₀ = π g' i₀ := by
    intro g g' h
    have h1 := (hst _).1 (apply_inv_mul_eq h)
    rw [map_mul, Equiv.Perm.mul_apply] at h1
    have h2 := congrArg (π g) h1
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h2
    exact h2.symm
  let ε : M → ι := fun m => if h : ∃ g, φ g z = m then π (Classical.choose h) i₀ else i₀
  have hε : ∀ g, ε (φ g z) = π g i₀ := by
    intro g
    have h : ∃ g', φ g' z = φ g z := ⟨g, rfl⟩
    show (if h : ∃ g', φ g' z = φ g z then π (Classical.choose h) i₀ else i₀) = π g i₀
    simp only [h, ↓reduceDIte]
    exact key _ _ (Classical.choose_spec h)
  refine ⟨ε, hε, ?_, ?_⟩
  · rintro m n ⟨g, rfl⟩ ⟨g', rfl⟩ h
    rw [hε, hε] at h
    have h1 : π (g⁻¹ * g') i₀ = i₀ := by
      rw [map_mul, Equiv.Perm.mul_apply, ← h, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have h2 := congrArg (φ g) ((hst (g⁻¹ * g')).2 h1)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left] at h2
    exact h2.symm
  · rintro g m ⟨h, rfl⟩
    rw [← MulAut.mul_apply, ← map_mul, hε, hε, map_mul, Equiv.Perm.mul_apply]

theorem orbit_eq_ne_one [Finite M] [Finite ι] (φ : Γ →* MulAut M) {z : M} (hz : z ≠ 1)
    (hcard : Nat.card M = Nat.card ι + 1) (ε : M → ι)
    (hinj : ∀ m n, (∃ g, φ g z = m) → (∃ g, φ g z = n) → ε m = ε n → m = n)
    (hsurj : ∀ j, ∃ g, ε (φ g z) = j) : ∀ m, m ≠ 1 → ∃ g, φ g z = m := by
  classical
  let O : Set M := {m | ∃ g, φ g z = m}
  have hOsub : O ⊆ {m : M | m ≠ 1} := by
    rintro m ⟨g, rfl⟩ h1
    apply hz
    exact (φ g).injective (by rw [h1, map_one])
  have hOinj : Set.InjOn ε O := fun m hm n hn h => hinj m n hm hn h
  have himg : ε '' O = Set.univ := by
    ext j
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := hsurj j
    exact ⟨φ g z, ⟨g, rfl⟩, hg⟩
  have hOcard : O.ncard = Nat.card ι := by
    rw [← hOinj.ncard_image, himg, Set.ncard_univ]
  have hne : ({m : M | m ≠ 1}).ncard = Nat.card ι := by
    have h1 : ({m : M | m ≠ 1}) = (Set.univ \ {1} : Set M) := by
      ext m
      simp
    rw [h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
    omega
  have hEq : O = {m : M | m ≠ 1} :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hne, hOcard]) (Set.toFinite _)
  intro m hm
  have : m ∈ O := by rw [hEq]; exact hm
  exact this

end CFSG.Quasithin.ModD
