module

public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.SimplyLacedCover
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem corootPair_eq_iform_of_symmetrizer_eq_one (hτ : ∀ i, τ.symmetrizer i i = 1)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (v : Fin τ.rank → ℤ) : corootPair α v = iform α v := by
  rw [corootPair, iform_self_eq_two hτ hα, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem iform_single_single_of_ne (hτ : ∀ i, τ.symmetrizer i i = 1) {i j : Fin τ.rank}
    (hij : i ≠ j) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) = τ.cartan i j := by
  rw [iform_single_left, hτ i, one_mul,
    Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
      (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem pi_single_one_ne_of_ne (i j : Fin τ.rank) (hij : i ≠ j) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := by
  intro h
  have h' := congrFun h j
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm] at h'
  exact one_ne_zero h'

theorem pi_single_one_ne_neg_of_ne (i j : Fin τ.rank) (hij : i ≠ j) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := by
  intro h
  have h' := congrFun h j
  simp only [Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_of_ne hij.symm, neg_zero] at h'
  exact one_ne_zero h'

theorem eq_or_eq_neg_of_rootReflection_eq (hτ : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h : rootReflection β = rootReflection γ) : γ = β ∨ γ = -β := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne, hne'⟩ := hcon
  have hcβ : rootReflection γ • β = β - iform γ β • γ := by
    rw [rootReflection_smul hγ, corootPair_eq_iform_of_symmetrizer_eq_one hτ hγ]
  have h1 : rootReflection β • β = rootReflection γ • β := by rw [h]
  rw [rootReflection_smul_self hβ, hcβ] at h1
  have h2 : iform γ β • γ = (2 : ℤ) • β := by
    have h1' : -β + iform γ β • γ = β := by
      have := congrArg (fun x : Fin τ.rank → ℤ => x + iform γ β • γ) h1
      simpa only [sub_add_cancel] using this
    have h1'' : iform γ β • γ + (-β) = β := by rw [add_comm]; exact h1'
    have hsub : iform γ β • γ = β - (-β) := eq_sub_iff_add_eq.mpr h1''
    rw [hsub]
    abel
  have hββ : iform β β = 2 := iform_self_eq_two hτ hβ
  have h4 : iform γ β ^ 2 = 4 := by
    have := congrArg (iform β) h2
    rw [iform_smul_right, iform_smul_right, hββ, iform_comm β γ] at this
    simpa [pow_two] using this
  have hmem : iform γ β = -1 ∨ iform γ β = 0 ∨ iform γ β = 1 :=
    iform_mem hτ hγ hβ hne hne'
  rcases hmem with hc | hc | hc <;> rw [hc] at h4 <;> norm_num at h4

theorem iform_eq_zero_of_commute_rootReflection (hτ : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hne : γ ≠ β) (hne' : γ ≠ -β)
    (h : Commute (rootReflection β) (rootReflection γ)) : iform β γ = 0 := by
  have e := rootReflection_smul_root (rootReflection β) hγ
  have hcomm : rootReflection β * rootReflection γ * (rootReflection β)⁻¹ = rootReflection γ := by
    rw [h.eq]
    group
  have heq : rootReflection (rootReflection β • γ) = rootReflection γ := by rw [e, hcomm]
  have hroot : IsRoot τ (rootReflection β • γ) := IsRoot.smul hγ (rootReflection β)
  have hcase := eq_or_eq_neg_of_rootReflection_eq hτ hroot hγ heq
  have hcβ : rootReflection β • γ = γ - iform β γ • β := by
    rw [rootReflection_smul hβ, corootPair_eq_iform_of_symmetrizer_eq_one hτ hβ]
  have hmem : iform β γ = -1 ∨ iform β γ = 0 ∨ iform β γ = 1 := by
    have := iform_mem hτ hγ hβ hne hne'
    rwa [iform_comm γ β] at this
  rcases hcase with hcase | hcase
  · have h0 : iform β γ • β = 0 := by
      have h' := hcase
      rw [hcβ] at h'
      exact sub_eq_self.mp h'.symm
    have hh : iform β γ * height β = 0 := by
      have := congrArg height h0
      rw [height_zsmul] at this
      simpa [height] using this
    exact (mul_eq_zero.mp hh).resolve_right hβ.height_ne_zero
  · have h2 : iform β γ • β = (2 : ℤ) • γ := by
      have h' := hcase
      rw [hcβ, neg_sub] at h'
      have h'' := congrArg (fun x : Fin τ.rank → ℤ => x + γ) h'
      rw [sub_add_cancel] at h''
      rw [← h'']
      abel
    have h4 : iform β γ ^ 2 = 4 := by
      have := congrArg (iform γ) h2
      rw [iform_smul_right, iform_smul_right, iform_self_eq_two hτ hγ, iform_comm γ β] at this
      simpa [pow_two] using this
    rcases hmem with hc | hc | hc <;> rw [hc] at h4 <;> norm_num at h4

theorem commute_simple_iff (hτ : ∀ i, τ.symmetrizer i i = 1) {i j : Fin τ.rank} (hij : i ≠ j) :
    Commute (simple τ i) (simple τ j) ↔ τ.cartan i j = 0 := by
  have hsi : rootReflection (Pi.single i 1 : Fin τ.rank → ℤ) = simple τ i := by
    simpa using rootReflection_eq_conj (β := Pi.single i 1) (w := 1) (j := i)
      (one_smul (WeylGroup τ) (Pi.single i 1 : Fin τ.rank → ℤ))
  have hsj : rootReflection (Pi.single j 1 : Fin τ.rank → ℤ) = simple τ j := by
    simpa using rootReflection_eq_conj (β := Pi.single j 1) (w := 1) (j := j)
      (one_smul (WeylGroup τ) (Pi.single j 1 : Fin τ.rank → ℤ))
  constructor
  · intro h
    have h' : Commute (rootReflection (Pi.single i 1 : Fin τ.rank → ℤ))
        (rootReflection (Pi.single j 1 : Fin τ.rank → ℤ)) := by
      rw [hsi, hsj]
      exact h
    have hzero := iform_eq_zero_of_commute_rootReflection hτ (isRoot_single τ i)
      (isRoot_single τ j) (pi_single_one_ne_of_ne i j hij) (pi_single_one_ne_neg_of_ne i j hij) h'
    rwa [iform_single_single_of_ne hτ hij] at hzero
  · intro h
    have h0 : iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) = 0 := by
      rw [iform_single_single_of_ne hτ hij, h]
    have hcomm := rootReflection_commute_of_iform_eq_zero (isRoot_single τ i)
      (isRoot_single τ j) h0
    rwa [hsi, hsj] at hcomm

end CFSG.StandardType

end
