module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem signedPermGroupOn_univ (t : ℕ) :
    signedPermGroupOn t Finset.univ = signedPermGroup t := by
  rw [signedPermGroupOn, signedPermGroup]
  congr 1
  ext T
  simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_univ, true_and]

private theorem funCongrLeft_mem_signedPermGroupOn {t : ℕ} (S : Finset (Fin t))
    (σ : Equiv.Perm (Fin t)) (hσ : ∀ i ∉ S, σ i = i) :
    LinearEquiv.funCongrLeft F F σ ∈ signedPermGroupOn t S := by
  classical
  have hσsupp : ∀ x, σ x ≠ x → x ∈ S := by
    intro x hx
    by_contra h
    exact hx (hσ x h)
  have hσinv : ∀ x, σ x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hxS
      by_contra h
      have h1 : σ x = x := hσ x h
      exact h (by rwa [h1] at hxS)
    · intro hx
      by_contra h
      have h1 : σ (σ x) = σ x := hσ (σ x) h
      have h2 : σ x = x := σ.injective h1
      exact h (by rwa [← h2] at hx)
  have hσ' : σ = Equiv.Perm.ofSubtype (σ.subtypePerm hσinv) :=
    (Equiv.Perm.ofSubtype_subtypePerm hσinv hσsupp).symm
  rw [hσ']
  refine Equiv.Perm.swap_induction_on (σ.subtypePerm hσinv) ?_ ?_
  · rw [map_one]
    rw [show LinearEquiv.funCongrLeft F F (1 : Equiv.Perm (Fin t)) = 1 from rfl]
    exact Subgroup.one_mem _
  · intro f x y hxy ih
    have hswap : LinearEquiv.funCongrLeft F F
        (Equiv.Perm.ofSubtype (Equiv.swap x y)) ∈ signedPermGroupOn t S := by
      rw [Equiv.Perm.ofSubtype_swap_eq]
      exact Subgroup.subset_closure (Or.inl ⟨x.1, x.2, y.1, y.2, rfl⟩)
    rw [map_mul]
    change LinearEquiv.funCongrLeft F F (Equiv.Perm.ofSubtype f) *
      LinearEquiv.funCongrLeft F F (Equiv.Perm.ofSubtype (Equiv.swap x y)) ∈
      signedPermGroupOn t S
    exact mul_mem ih hswap

private theorem piCongrRight_neg_mem_signedPermGroupOn {t : ℕ} (S : Finset (Fin t))
    (A : Finset (Fin t)) (hA : A ⊆ S) :
    LinearEquiv.piCongrRight (fun j : Fin t =>
      if j ∈ A then LinearEquiv.neg F else LinearEquiv.refl F F) ∈
      signedPermGroupOn t S := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have h1 : LinearEquiv.piCongrRight (fun j : Fin t =>
        if j ∈ (∅ : Finset (Fin t)) then LinearEquiv.neg F else
          LinearEquiv.refl F F) = LinearEquiv.refl F (V t) := by
      ext u j
      simp
    rw [h1]
    exact Subgroup.one_mem _
  | insert a A ha ih =>
    have haS : a ∈ S := hA (Finset.mem_insert_self a A)
    have hAS' : A ⊆ S := fun x hx => hA (Finset.mem_insert_of_mem hx)
    have h1 : LinearEquiv.piCongrRight (fun j : Fin t =>
        if j ∈ insert a A then LinearEquiv.neg F else LinearEquiv.refl F F) =
        negEquiv t a * LinearEquiv.piCongrRight (fun j : Fin t =>
          if j ∈ A then LinearEquiv.neg F else LinearEquiv.refl F F) := by
      ext u j
      simp only [negEquiv, LinearEquiv.piCongrRight_apply, LinearEquiv.mul_apply]
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj, Finset.mem_insert]
    rw [h1]
    exact mul_mem (Subgroup.subset_closure (Or.inr ⟨a, haS, rfl⟩)) (ih hAS')

private theorem orientEquiv_mem_signedPermGroupOn {t : ℕ} (S : Finset (Fin t))
    (ε : Fin t → F) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hεS : ∀ i ∉ S, ε i = 1) :
    orientEquiv t ε ∈ signedPermGroupOn t S := by
  classical
  have hAεS : Finset.univ.filter (fun k => ε k = -1) ⊆ S := by
    intro k hk
    by_contra hks
    have hk1 : ε k = -1 := (Finset.mem_filter.mp hk).2
    have hk2 : ε k = 1 := hεS k hks
    rw [hk1] at hk2
    exact (by decide : (-1 : F) ≠ 1) hk2
  have horient : orientEquiv t ε =
      LinearEquiv.piCongrRight (fun j : Fin t =>
        if j ∈ Finset.univ.filter (fun k => ε k = -1) then
          LinearEquiv.neg F else LinearEquiv.refl F F) := by
    ext u j
    simp only [orientEquiv, LinearEquiv.piCongrRight_apply, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [horient]
  exact piCongrRight_neg_mem_signedPermGroupOn S _ hAεS

theorem mem_signedPermGroupOn_of_apply {t : ℕ} (S : Finset (Fin t)) (φ : V t ≃ₗ[F] V t)
    (π : Equiv.Perm (Fin t)) (ε : Fin t → F) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hπ : ∀ i ∉ S, π i = i) (hεS : ∀ i ∉ S, ε i = 1) (h : ∀ u i, φ u (π i) = ε i * u i) :
    φ ∈ signedPermGroupOn t S := by
  classical
  have hπ' : ∀ i ∉ S, π.symm i = i := by
    intro i hi
    calc π.symm i = π.symm (π i) := by rw [hπ i hi]
      _ = i := Equiv.symm_apply_apply π i
  have hperm : LinearEquiv.funCongrLeft F F π.symm ∈ signedPermGroupOn t S :=
    funCongrLeft_mem_signedPermGroupOn S π.symm hπ'
  have horient : orientEquiv t ε ∈ signedPermGroupOn t S :=
    orientEquiv_mem_signedPermGroupOn S ε hε hεS
  have hφeq : φ = LinearEquiv.funCongrLeft F F π.symm * orientEquiv t ε := by
    ext u j
    rw [LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    have hk : (orientEquiv t ε u) (π.symm j) = ε (π.symm j) * u (π.symm j) := by
      simp only [orientEquiv, LinearEquiv.piCongrRight_apply]
      rcases hε (π.symm j) with h1 | h1
      · rw [h1]
        simp [show (1 : F) ≠ -1 by decide]
      · rw [h1]
        simp
    rw [hk, ← h u (π.symm j)]
    exact congrArg (φ u) (Equiv.apply_symm_apply π j).symm
  rw [hφeq]
  exact mul_mem hperm horient

theorem mem_signedPermGroup_of_apply {t : ℕ} (φ : V t ≃ₗ[F] V t) (π : Equiv.Perm (Fin t))
    (ε : Fin t → F) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (h : ∀ u i, φ u (π i) = ε i * u i) :
    φ ∈ signedPermGroup t := by
  rw [← signedPermGroupOn_univ t]
  exact mem_signedPermGroupOn_of_apply Finset.univ φ π ε hε
    (fun i hi => absurd (Finset.mem_univ i) hi) (fun i hi => absurd (Finset.mem_univ i) hi) h

end CFSG.StandardType.GGQ2Frame.PlaneRaw
