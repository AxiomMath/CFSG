module

public import CFSG.LieType.Chevalley.FoldedRootOrbits
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace CFSG.StandardType.TwE6SplitFold

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] noncomputable def twE6OrbSum (β : Fin TwistTag.E6.tag.rank → ℤ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ α ∈ TwistTag.E6.diagramOrbit β, α

open CFSG.RankThree.E6 in
private def tf_e6RootVec (m : Fin 72) : Fin TwistTag.E6.tag.rank → ℤ := e6RootVec m

section Helpers


private theorem tf_permLattice_one (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin TwistTag.E6.tag.rank)) v = v := rfl

private theorem tf_permLattice_mul (g h : Equiv.Perm (Fin TwistTag.E6.tag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice (g * h) v = permLattice g (permLattice h v) := rfl

private theorem tf_permLattice_perm (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm v) = v := by
  rw [← tf_permLattice_mul]
  have h2 : TwistTag.E6.perm * TwistTag.E6.perm = 1 := by
    rw [← pow_two, show (2 : ℕ) = TwistTag.E6.order from rfl]
    exact TwistTag.perm_pow_order (t := TwistTag.E6)
  rw [h2, tf_permLattice_one]

private theorem tf_diagramOrbit_eq (β : Fin TwistTag.E6.tag.rank → ℤ) :
    TwistTag.E6.diagramOrbit β = {β, permLattice TwistTag.E6.perm β} := by
  simp only [TwistTag.diagramOrbit]
  rw [show TwistTag.E6.order = 2 from rfl]
  have hr : (Finset.range 2 : Finset ℕ) = {0, 1} := by decide
  rw [hr, Finset.image_insert, Finset.image_singleton]
  simp only [pow_zero, pow_one, tf_permLattice_one]

private theorem tf_orbSum_fixed {β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : permLattice TwistTag.E6.perm β = β) : twE6OrbSum β = β := by
  simp only [twE6OrbSum, tf_diagramOrbit_eq, h]
  simp

private theorem tf_orbSum_ne {β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : permLattice TwistTag.E6.perm β ≠ β) :
    twE6OrbSum β = β + permLattice TwistTag.E6.perm β := by
  simp only [twE6OrbSum, tf_diagramOrbit_eq]
  rw [Finset.sum_insert (by simpa [eq_comm] using h)]
  simp

private theorem tf_orbSum_perm (β : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6OrbSum (permLattice TwistTag.E6.perm β) = twE6OrbSum β := by
  by_cases h : permLattice TwistTag.E6.perm β = β
  · rw [h]
  · have h' : permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm β) ≠
        permLattice TwistTag.E6.perm β := by
      rw [tf_permLattice_perm]
      exact fun hh => h hh.symm
    rw [tf_orbSum_ne (β := permLattice TwistTag.E6.perm β) h', tf_orbSum_ne h,
      tf_permLattice_perm, add_comm]

private theorem tf_symmetrizedCartan_perm (i j : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.tag.symmetrizedCartan (TwistTag.E6.perm i) (TwistTag.E6.perm j) =
      TwistTag.E6.tag.symmetrizedCartan i j := by
  have h : TwistTag.E6.tag.symmetrizer = 1 := rfl
  simp only [Tag.symmetrizedCartan, h, Matrix.one_mul]
  exact TwistTag.cartan_perm TwistTag.E6 i j

private theorem tf_iform_permLattice (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform (permLattice TwistTag.E6.perm x) (permLattice TwistTag.E6.perm y) = iform x y := by
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.symm_apply_apply]
  rw [tf_symmetrizedCartan_perm]

private theorem tf_isRoot_permLattice_iff (v : Fin TwistTag.E6.tag.rank → ℤ) :
    IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm v) ↔ IsRoot TwistTag.E6.tag v := by
  refine ⟨fun hv => ?_, fun hv => hv.permLattice (TwistTag.cartan_perm TwistTag.E6)⟩
  have h := hv.permLattice (cartan_perm_symm (TwistTag.cartan_perm TwistTag.E6))
  convert h using 1
  ext i
  simp [permLattice]

private theorem tf_exists_fold {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ γ : Fin TwistTag.E6.foldedTag.rank → ℤ, IsRoot TwistTag.E6.foldedTag γ ∧
      TwistTag.E6.foldMap γ = twE6OrbSum β := by
  let O : TwistTag.E6.diagramRootOrbits :=
    ⟨TwistTag.E6.diagramOrbit β, ⟨β, hβ, rfl⟩⟩
  refine ⟨TwistTag.E6.diagramOrbitRoot O, (TwistTag.E6.diagramOrbitRoot O).2, ?_⟩
  rw [TwistTag.E6.foldMap_diagramOrbitRoot]
  rfl

private theorem tf_exists_preimage {γ : Fin TwistTag.E6.foldedTag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.foldedTag γ) :
    ∃ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot Tag.E6 β ∧
      TwistTag.E6.foldMap γ = twE6OrbSum β := by
  obtain ⟨O, hO⟩ := TwistTag.E6.diagramOrbitRoot_surjective ⟨γ, hγ⟩
  obtain ⟨β, hβ, hOβ⟩ := O.2
  refine ⟨β, hβ, ?_⟩
  have hfold := TwistTag.E6.foldMap_diagramOrbitRoot O
  rw [hO] at hfold
  rw [hfold]
  simp only [twE6OrbSum, hOβ]

private theorem tf_iform_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → (Fin TwistTag.E6.tag.rank → ℤ)) (y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform (∑ x ∈ s, f x) y = ∑ x ∈ s, iform (f x) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [iform]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_left, ih]

private theorem tf_iform_sum_right {ι : Type*} (s : Finset ι)
    (f : ι → (Fin TwistTag.E6.tag.rank → ℤ)) (x : Fin TwistTag.E6.tag.rank → ℤ) :
    iform x (∑ y ∈ s, f y) = ∑ y ∈ s, iform x (f y) := by
  classical
  induction s using Finset.induction with
  | empty => simp [iform]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_right, ih]

private theorem tf_iform_single_single (a b : Fin TwistTag.E6.foldedTag.rank) :
    iform (Pi.single a 1 : Fin TwistTag.E6.foldedTag.rank → ℤ) (Pi.single b 1) =
      TwistTag.E6.foldedTag.symmetrizedCartan a b := by
  simp only [iform, Pi.single_apply]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi])
    (fun ha => absurd (Finset.mem_univ a) ha)]
  rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj])
    (fun hb => absurd (Finset.mem_univ b) hb)]
  simp

private theorem tf_iform_orbitSum : ∀ a b : Fin TwistTag.E6.foldedTag.rank,
    iform (TwistTag.E6.orbitSum a) (TwistTag.E6.orbitSum b) =
      iform (Pi.single a 1 : Fin TwistTag.E6.foldedTag.rank → ℤ)
        (Pi.single b 1) := by
  decide +kernel

private theorem tf_iform_foldMap (u v : Fin TwistTag.E6.foldedTag.rank → ℤ) :
    iform (TwistTag.E6.foldMap u) (TwistTag.E6.foldMap v) = iform u v := by
  rw [TwistTag.E6.foldMap_apply, TwistTag.E6.foldMap_apply]
  rw [tf_iform_sum_left]
  simp only [tf_iform_sum_right]
  rw [show iform u v =
    ∑ a, ∑ b, u a * TwistTag.E6.foldedTag.symmetrizedCartan a b * v b from rfl]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [iform_smul_left, iform_smul_right, tf_iform_orbitSum a b, tf_iform_single_single]
  ring

private theorem tf_chi_comb {M : Type*} [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    {β α : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : χ₆ (Multiplicative.ofAdd β) = 1) (hα : χ₆ (Multiplicative.ofAdd α) = 1) :
    χ₆ (Multiplicative.ofAdd (β + permLattice TwistTag.E6.perm α)) = 1 ∧
    χ₆ (Multiplicative.ofAdd (β - permLattice TwistTag.E6.perm α)) = 1 ∧
    χ₆ (Multiplicative.ofAdd (-β + permLattice TwistTag.E6.perm α)) = 1 ∧
    χ₆ (Multiplicative.ofAdd (-β - permLattice TwistTag.E6.perm α)) = 1 := by
  have hρα : χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm α)) = 1 := by
    rw [hρ α, hα]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [ofAdd_add, ofAdd_sub, ofAdd_neg, map_mul, map_inv, map_div, hβ, hρα, inv_one,
      mul_one, one_mul, div_one, one_div]

private theorem tf_chi_orbSum {M : Type*} [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ kernelRoots χ₆) :
    χ₆ (Multiplicative.ofAdd (twE6OrbSum β)) = 1 := by
  by_cases h : permLattice TwistTag.E6.perm β = β
  · rw [tf_orbSum_fixed h]
    exact hβ.2
  · rw [tf_orbSum_ne h, ofAdd_add, map_mul, hβ.2, hρ β, hβ.2, one_mul]

private theorem tf_kernel_fold_iff {M₄ M : Type*} [CommGroup M₄] [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    (h2 : ∀ m : M, m ^ 2 = 1 → m = 1)
    (χ₄ : Multiplicative (Fin TwistTag.E6.foldedTag.rank → ℤ) →* M₄)
    (j : M₄ →* M) (hj : Function.Injective j)
    (hχ : ∀ γ, j (χ₄ (Multiplicative.ofAdd γ)) =
      χ₆ (Multiplicative.ofAdd (TwistTag.E6.foldMap γ)))
    {β : Fin TwistTag.E6.tag.rank → ℤ} {γ : Fin TwistTag.E6.foldedTag.rank → ℤ}
    (hβroot : IsRoot Tag.E6 β) (hγroot : IsRoot TwistTag.E6.foldedTag γ)
    (hfold : TwistTag.E6.foldMap γ = twE6OrbSum β) :
    β ∈ kernelRoots χ₆ ↔ γ ∈ kernelRoots χ₄ := by
  constructor
  · intro hβ
    refine ⟨hγroot, ?_⟩
    apply hj
    rw [map_one, hχ γ, hfold, tf_chi_orbSum χ₆ hρ hβ]
  · intro hγ
    refine ⟨hβroot, ?_⟩
    have h6 : χ₆ (Multiplicative.ofAdd (twE6OrbSum β)) = 1 := by
      rw [← hfold, ← hχ γ, hγ.2, map_one]
    by_cases h : permLattice TwistTag.E6.perm β = β
    · rwa [tf_orbSum_fixed h] at h6
    · rw [tf_orbSum_ne h, ofAdd_add, map_mul, hρ β] at h6
      have hsq : (χ₆ (Multiplicative.ofAdd β)) ^ 2 = 1 := by
        rw [pow_two]
        exact h6
      exact h2 _ hsq

private theorem tf_kernelRoots_perm {M : Type*} [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ kernelRoots χ₆) :
    permLattice TwistTag.E6.perm x ∈ kernelRoots χ₆ :=
  ⟨(tf_isRoot_permLattice_iff x).2 hx.1, by rw [hρ x]; exact hx.2⟩

private theorem tf_N1_check :
    ∀ m m' : Fin 72, iform (tf_e6RootVec m) (tf_e6RootVec m') ≠ 0 →
    iform (twE6OrbSum (tf_e6RootVec m)) (twE6OrbSum (tf_e6RootVec m')) ≠ 0 ∨
    ∃ n : Fin 72,
      (tf_e6RootVec n = tf_e6RootVec m + permLattice TwistTag.E6.perm (tf_e6RootVec m') ∨
       tf_e6RootVec n = tf_e6RootVec m - permLattice TwistTag.E6.perm (tf_e6RootVec m') ∨
       tf_e6RootVec n = -tf_e6RootVec m + permLattice TwistTag.E6.perm (tf_e6RootVec m') ∨
       tf_e6RootVec n = -tf_e6RootVec m - permLattice TwistTag.E6.perm (tf_e6RootVec m')) ∧
      iform (twE6OrbSum (tf_e6RootVec n)) (twE6OrbSum (tf_e6RootVec m)) ≠ 0 ∧
      iform (twE6OrbSum (tf_e6RootVec n)) (twE6OrbSum (tf_e6RootVec m')) ≠ 0 := by
  decide +kernel

private theorem tf_N1 {β β' : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (hβ' : IsRoot Tag.E6 β') (hif : iform β β' ≠ 0) :
    iform (twE6OrbSum β) (twE6OrbSum β') ≠ 0 ∨
    ∃ δ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot Tag.E6 δ ∧
      (δ = β + permLattice TwistTag.E6.perm β' ∨
       δ = β - permLattice TwistTag.E6.perm β' ∨
       δ = -β + permLattice TwistTag.E6.perm β' ∨
       δ = -β - permLattice TwistTag.E6.perm β') ∧
      iform (twE6OrbSum δ) (twE6OrbSum β) ≠ 0 ∧ iform (twE6OrbSum δ) (twE6OrbSum β') ≠ 0 := by
  obtain ⟨m, hm⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hβ
  obtain ⟨m', hm'⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hβ'
  have hmv : tf_e6RootVec m = β := hm
  have hmv' : tf_e6RootVec m' = β' := hm'
  have hcheck := tf_N1_check m m' (by rw [hmv, hmv']; exact hif)
  rcases hcheck with hcase | ⟨n, hn, h1, h2⟩
  · left
    rw [← hmv, ← hmv']
    exact hcase
  · right
    refine ⟨tf_e6RootVec n, CFSG.RankThree.E6.isRoot_e6RootVec n, ?_, ?_, ?_⟩
    · rcases hn with h | h | h | h
      · left; rw [h, hmv, hmv']
      · right; left; rw [h, hmv, hmv']
      · right; right; left; rw [h, hmv, hmv']
      · right; right; right; rw [h, hmv, hmv']
    · rw [← hmv]
      exact h1
    · rw [← hmv']
      exact h2

private theorem tf_exists_of_iform_orbSum_ne_zero {δ ε : Fin TwistTag.E6.tag.rank → ℤ}
    (h : iform (twE6OrbSum δ) (twE6OrbSum ε) ≠ 0) :
    ∃ a ∈ TwistTag.E6.diagramOrbit δ, ∃ b ∈ TwistTag.E6.diagramOrbit ε,
      iform a b ≠ 0 := by
  by_contra hc
  push Not at hc
  refine h ?_
  simp only [twE6OrbSum]
  rw [tf_iform_sum_left]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [tf_iform_sum_right]
  exact Finset.sum_eq_zero fun y hy => hc x hx y hy

private theorem tf_component_fold {M₄ M : Type*} [CommGroup M₄] [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    (h2 : ∀ m : M, m ^ 2 = 1 → m = 1)
    (χ₄ : Multiplicative (Fin TwistTag.E6.foldedTag.rank → ℤ) →* M₄)
    (j : M₄ →* M) (hj : Function.Injective j)
    (hχ : ∀ γ, j (χ₄ (Multiplicative.ofAdd γ)) =
      χ₆ (Multiplicative.ofAdd (TwistTag.E6.foldMap γ)))
    (i₆ : KernelComponent χ₆) :
    ∃ i₄ : KernelComponent χ₄,
      (∀ δ ∈ componentRoots χ₆ i₆,
        ∃ γ ∈ componentRoots χ₄ i₄, TwistTag.E6.foldMap γ = twE6OrbSum δ) ∧
      (∀ γ ∈ componentRoots χ₄ i₄,
        ∃ δ ∈ componentRoots χ₆ i₆, TwistTag.E6.foldMap γ = twE6OrbSum δ) := by
  classical
  obtain ⟨β0, hβ0eq⟩ := Quotient.exists_rep i₆
  have hβ0root : IsRoot Tag.E6 (β0 : Fin TwistTag.E6.tag.rank → ℤ) := β0.2.1
  obtain ⟨γ0, hγ0root, hγ0fold⟩ := tf_exists_fold hβ0root
  have hγ0ker : γ0 ∈ kernelRoots χ₄ :=
    (tf_kernel_fold_iff χ₆ hρ h2 χ₄ j hj hχ hβ0root hγ0root hγ0fold).1 β0.2
  let i4 : KernelComponent χ₄ := ⟦⟨γ0, hγ0ker⟩⟧
  let Ψ6 : Set (Fin TwistTag.E6.tag.rank → ℤ) := componentRoots χ₆ i₆
  let Ψ4 : Set (Fin TwistTag.E6.foldedTag.rank → ℤ) := componentRoots χ₄ i4
  have hΨ6 : IsRootComponent Ψ6 := isRootComponent_componentRoots (χ := χ₆) i₆
  have hΨ4 : IsRootComponent Ψ4 := isRootComponent_componentRoots (χ := χ₄) i4
  have hβ0Ψ : (β0 : Fin TwistTag.E6.tag.rank → ℤ) ∈ Ψ6 := ⟨β0.2, hβ0eq⟩
  have hγ0Ψ : γ0 ∈ Ψ4 := ⟨hγ0ker, rfl⟩
  have hA : ∀ δ ∈ Ψ6, ∃ γ ∈ Ψ4, TwistTag.E6.foldMap γ = twE6OrbSum δ := by
    let S6 : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
      {β | β ∈ Ψ6 ∧ ∃ γ ∈ Ψ4, TwistTag.E6.foldMap γ = twE6OrbSum β}
    have hS6sub : S6 ⊆ Ψ6 := fun _ h => h.1
    have hS6ne : S6.Nonempty := ⟨β0, hβ0Ψ, γ0, hγ0Ψ, hγ0fold⟩
    have hS6closed : ∀ α ∈ S6, ∀ β ∈ Ψ6, iform α β ≠ 0 → β ∈ S6 := by
      intro α hα β hβ hif
      obtain ⟨hαΨ, γα, hγαΨ, hγαfold⟩ := hα
      have hαker : α ∈ kernelRoots χ₆ := hαΨ.1
      obtain ⟨hγαker, hγαclass⟩ := hγαΨ
      have hβker : β ∈ kernelRoots χ₆ := hβ.1
      have hαroot : IsRoot Tag.E6 α := hΨ6.isRoot α hαΨ
      have hβroot : IsRoot Tag.E6 β := hΨ6.isRoot β hβ
      obtain ⟨γβ, hγβroot, hγβfold⟩ := tf_exists_fold hβroot
      have hγβker : γβ ∈ kernelRoots χ₄ :=
        (tf_kernel_fold_iff χ₆ hρ h2 χ₄ j hj hχ hβroot hγβroot hγβfold).1 hβker
      have hγβclass : (⟦⟨γβ, hγβker⟩⟧ : KernelComponent χ₄) = i4 := by
        have hif' : iform β α ≠ 0 := by
          rw [iform_comm]
          exact hif
        rcases tf_N1 hβroot hαroot hif' with hcase | ⟨δ, hδroot, hδform, hδβmem, hδαmem⟩
        · have hne : iform γβ γα ≠ 0 := by
            have hfm := tf_iform_foldMap γβ γα
            rw [hγβfold, hγαfold] at hfm
            rw [← hfm]
            exact hcase
          exact (mk_eq_of_iform_ne_zero (χ := χ₄) (α := ⟨γβ, hγβker⟩)
            (β := ⟨γα, hγαker⟩) hne).trans hγαclass
        · have hδker : δ ∈ kernelRoots χ₆ := ⟨hδroot, ?_⟩
          · obtain ⟨γδ, hγδroot, hγδfold⟩ := tf_exists_fold hδroot
            have hγδker : γδ ∈ kernelRoots χ₄ :=
              (tf_kernel_fold_iff χ₆ hρ h2 χ₄ j hj hχ hδroot hγδroot hγδfold).1 hδker
            have hδγβ : iform γδ γβ ≠ 0 := by
              have hfm := tf_iform_foldMap γδ γβ
              rw [hγδfold, hγβfold] at hfm
              rw [← hfm]
              exact hδβmem
            have hδγα : iform γδ γα ≠ 0 := by
              have hfm := tf_iform_foldMap γδ γα
              rw [hγδfold, hγαfold] at hfm
              rw [← hfm]
              exact hδαmem
            calc (⟦⟨γβ, hγβker⟩⟧ : KernelComponent χ₄)
                = ⟦⟨γδ, hγδker⟩⟧ :=
                  mk_eq_of_iform_ne_zero (χ := χ₄) (α := ⟨γβ, hγβker⟩)
                    (β := ⟨γδ, hγδker⟩) (by rw [iform_comm]; exact hδγβ)
              _ = ⟦⟨γα, hγαker⟩⟧ :=
                  mk_eq_of_iform_ne_zero (χ := χ₄) (α := ⟨γδ, hγδker⟩)
                    (β := ⟨γα, hγαker⟩) hδγα
              _ = i4 := hγαclass
          · rcases hδform with h | h | h | h
            · rw [h]
              exact (tf_chi_comb χ₆ hρ hβker.2 hαker.2).1
            · rw [h]
              exact (tf_chi_comb χ₆ hρ hβker.2 hαker.2).2.1
            · rw [h]
              exact (tf_chi_comb χ₆ hρ hβker.2 hαker.2).2.2.1
            · rw [h]
              exact (tf_chi_comb χ₆ hρ hβker.2 hαker.2).2.2.2
      exact ⟨hβ, γβ, ⟨hγβker, hγβclass⟩, hγβfold⟩
    have horth : ∀ α ∈ S6, ∀ β ∈ Ψ6, β ∉ S6 → iform α β = 0 := by
      intro α hα β hβ hβS
      by_contra hif
      exact hβS (hS6closed α hα β hβ hif)
    rcases hΨ6.irreducible S6 hS6sub horth with h | h
    · exact absurd hS6ne (by rw [h]; exact Set.not_nonempty_empty)
    · intro δ hδ
      rw [← h] at hδ
      exact hδ.2
  have hB : ∀ γ ∈ Ψ4, ∃ δ ∈ Ψ6, TwistTag.E6.foldMap γ = twE6OrbSum δ := by
    let T4 : Set (Fin TwistTag.E6.foldedTag.rank → ℤ) :=
      {γ | γ ∈ Ψ4 ∧ ∃ δ ∈ Ψ6, TwistTag.E6.foldMap γ = twE6OrbSum δ}
    have hT4sub : T4 ⊆ Ψ4 := fun _ h => h.1
    have hT4ne : T4.Nonempty := ⟨γ0, hγ0Ψ, β0, hβ0Ψ, hγ0fold⟩
    have hT4closed : ∀ α' ∈ T4, ∀ β' ∈ Ψ4, iform α' β' ≠ 0 → β' ∈ T4 := by
      intro α' hα' β' hβ' hif
      obtain ⟨hα'Ψ, δ, hδΨ, hα'fold⟩ := hα'
      obtain ⟨hδker, hδclass⟩ := hδΨ
      have hβ'ker : β' ∈ kernelRoots χ₄ := hβ'.1
      have hβ'root : IsRoot TwistTag.E6.foldedTag β' := hβ'ker.1
      obtain ⟨ε, hεroot, hεfold⟩ := tf_exists_preimage hβ'root
      have hεker : ε ∈ kernelRoots χ₆ :=
        (tf_kernel_fold_iff χ₆ hρ h2 χ₄ j hj hχ hεroot hβ'root hεfold).2 hβ'ker
      have hsum : iform (twE6OrbSum δ) (twE6OrbSum ε) ≠ 0 := by
        have hfm := tf_iform_foldMap α' β'
        rw [hα'fold, hεfold] at hfm
        rw [hfm]
        exact hif
      obtain ⟨a, ha, b, hb, hab⟩ := tf_exists_of_iform_orbSum_ne_zero hsum
      have ha' : a = δ ∨ a = permLattice TwistTag.E6.perm δ := by
        rw [tf_diagramOrbit_eq] at ha
        simpa using ha
      have hb' : b = ε ∨ b = permLattice TwistTag.E6.perm ε := by
        rw [tf_diagramOrbit_eq] at hb
        simpa using hb
      have hbker : b ∈ kernelRoots χ₆ := by
        rcases hb' with hbε | hbε
        · rw [hbε]; exact hεker
        · rw [hbε]; exact tf_kernelRoots_perm χ₆ hρ hεker
      rcases ha' with ha | ha
      · refine ⟨hβ', b, ⟨hbker, ?_⟩, ?_⟩
        · refine (mk_eq_of_iform_ne_zero (χ := χ₆) (α := ⟨b, hbker⟩)
            (β := ⟨δ, hδker⟩) ?_).trans hδclass
          rw [ha] at hab
          rwa [iform_comm]
        · rw [hεfold]
          rcases hb' with hbε | hbε
          · rw [hbε]
          · rw [hbε, tf_orbSum_perm]
      · refine ⟨hβ', permLattice TwistTag.E6.perm b, ⟨?_, ?_⟩, ?_⟩
        · exact tf_kernelRoots_perm χ₆ hρ hbker
        · refine (mk_eq_of_iform_ne_zero (χ := χ₆)
            (α := ⟨permLattice TwistTag.E6.perm b, tf_kernelRoots_perm χ₆ hρ hbker⟩)
            (β := ⟨δ, hδker⟩) ?_).trans hδclass
          have hshift : iform (permLattice TwistTag.E6.perm δ) b ≠ 0 := by
            rw [← ha]
            exact hab
          have hiso := tf_iform_permLattice δ (permLattice TwistTag.E6.perm b)
          rw [tf_permLattice_perm] at hiso
          rw [iform_comm, ← hiso]
          exact hshift
        · rw [hεfold]
          rcases hb' with hbε | hbε
          · rw [hbε, tf_orbSum_perm]
          · rw [hbε, tf_permLattice_perm]
    have horth : ∀ α ∈ T4, ∀ β ∈ Ψ4, β ∉ T4 → iform α β = 0 := by
      intro α hα β hβ hβT
      by_contra hif
      exact hβT (hT4closed α hα β hβ hif)
    rcases hΨ4.irreducible T4 hT4sub horth with h | h
    · exact absurd hT4ne (by rw [h]; exact Set.not_nonempty_empty)
    · intro γ hγ
      rw [← h] at hγ
      exact hγ.2
  exact ⟨i4, hA, hB⟩

end Helpers

theorem fold_class
    {M₄ M : Type*} [CommGroup M₄] [CommGroup M]
    (χ₆ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* M)
    (hρ : ∀ x, χ₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      χ₆ (Multiplicative.ofAdd x))
    (h2 : ∀ m : M, m ^ 2 = 1 → m = 1)
    (χ₄ : Multiplicative (Fin TwistTag.E6.foldedTag.rank → ℤ) →* M₄)
    (j : M₄ →* M) (hj : Function.Injective j)
    (hχ : ∀ γ, j (χ₄ (Multiplicative.ofAdd γ)) =
      χ₆ (Multiplicative.ofAdd (TwistTag.E6.foldMap γ)))
    (i₆ : KernelComponent χ₆) :
    ∃ i₄ : KernelComponent χ₄,
      (∀ δ ∈ componentRoots χ₆ i₆,
        ∃ γ ∈ componentRoots χ₄ i₄, TwistTag.E6.foldMap γ = twE6OrbSum δ) ∧
      (∀ γ ∈ componentRoots χ₄ i₄,
        ∃ δ ∈ componentRoots χ₆ i₆, TwistTag.E6.foldMap γ = twE6OrbSum δ) := by
  exact tf_component_fold χ₆ hρ h2 χ₄ j hj hχ i₆

end CFSG.StandardType.TwE6SplitFold

end
