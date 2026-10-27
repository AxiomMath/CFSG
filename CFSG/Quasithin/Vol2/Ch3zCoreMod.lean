module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

open G6

namespace Ch3z

@[expose] def Small (m : ℕ) : Prop := m = 3 ∨ m = 5 ∨ m = 7

theorem Small.odd {m : ℕ} (h : Small m) : Odd m := by
  rcases h with rfl | rfl | rfl <;> decide

instance decMemCoreMod (m : ℕ) : DecidablePred (· ∈ coreMod m) := fun x =>
  decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) mem_coreMod.symm

@[expose] def uvec (m : ℕ) (k : Fin m) : PermMod m :=
  Multiplicative.ofAdd (fun l => if l = k then (0 : ZMod 2) else 1)

theorem uvec_mem {m : ℕ} (hm : Odd m) (k : Fin m) : uvec m k ∈ coreMod m := by
  rw [mem_coreMod]
  simp only [uvec, toAdd_ofAdd]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (Finset.univ.filter fun l : Fin m => ¬ l = k) = Finset.univ.erase k := by
    ext l
    simp
  rw [h1, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  obtain ⟨n, rfl⟩ := hm
  have : 2 * n + 1 - 1 = 2 * n := by omega
  rw [this]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

@[expose] def uCore (m : ℕ) (hm : Odd m) (k : Fin m) : coreMod m := ⟨uvec m k, uvec_mem hm k⟩

theorem coreAct_uCore (m : ℕ) (hm : Odd m) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    coreAct m σ (uCore m hm k) = uCore m hm (σ k) := by
  apply Subtype.ext
  show permAct m σ (uvec m k) = uvec m (σ k)
  apply Multiplicative.toAdd.injective
  funext l
  simp only [permAct_apply, uvec, toAdd_ofAdd]
  by_cases h : l = σ k
  · subst h
    simp
  · have : σ⁻¹ l ≠ k := by
      intro h'
      apply h
      rw [← h']
      simp
    simp only [h, this, ite_false]

theorem uCore_injective (m : ℕ) (hm : Odd m) : Function.Injective (uCore m hm) := by
  intro a b h
  by_contra hab
  have := congrArg (fun v : coreMod m => Multiplicative.toAdd (v : PermMod m) a) h
  simp [uCore, uvec, hab] at this

theorem uCore_ne_one (m : ℕ) (hm : Odd m) (h3 : 3 ≤ m) (k : Fin m) : uCore m hm k ≠ 1 := by
  intro h
  by_cases hk : k.val = 0
  · have hne : (⟨1, by omega⟩ : Fin m) ≠ k := fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega
    have h1 := congrArg (fun v : coreMod m => Multiplicative.toAdd (v : PermMod m) ⟨1, by omega⟩) h
    simp [uCore, uvec, hne] at h1
  · have hne : (⟨0, by omega⟩ : Fin m) ≠ k := fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega
    have h1 := congrArg (fun v : coreMod m => Multiplicative.toAdd (v : PermMod m) ⟨0, by omega⟩) h
    simp [uCore, uvec, hne] at h1

theorem core_gen (m : ℕ) (hm : Small m) (v : coreMod m) :
    v = ∏ i ∈ Finset.univ.filter (fun i => Multiplicative.toAdd (v : PermMod m) i ≠ 0),
      uCore m hm.odd i := by
  revert v
  rcases hm with rfl | rfl | rfl <;> decide

theorem mulAut_ext_uCore (m : ℕ) (hm : Small m) {x y : MulAut (coreMod m)}
    (h : ∀ k, x (uCore m hm.odd k) = y (uCore m hm.odd k)) : x = y := by
  refine MulEquiv.ext fun v => ?_
  rw [core_gen m hm v, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => h i

theorem coreAct_eq_one_iff (m : ℕ) (hm : Odd m) (σ : Equiv.Perm (Fin m)) :
    coreAct m σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    refine Equiv.ext fun k => ?_
    have h1 : coreAct m σ (uCore m hm k) = uCore m hm k := by rw [h]; rfl
    rw [coreAct_uCore] at h1
    exact uCore_injective m hm h1
  · rintro rfl
    exact map_one _

theorem coreAct_injective (m : ℕ) (hm : Odd m) : Function.Injective (coreAct m) := by
  rw [injective_iff_map_eq_one]
  intro σ h
  exact (coreAct_eq_one_iff m hm σ).1 h

theorem exists_perm_of_uCore (m : ℕ) (hm : Small m) (x : MulAut (coreMod m))
    (hU : ∀ k : Fin m, ∃ j : Fin m, x (uCore m hm.odd k) = uCore m hm.odd j) :
    ∃ σ : Equiv.Perm (Fin m), x = coreAct m σ := by
  choose g hg using hU
  have hginj : Function.Injective g := fun a b h =>
    uCore_injective m hm.odd
      (x.injective ((hg a).trans ((congrArg (uCore m hm.odd) h).trans (hg b).symm)))
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
  refine ⟨σ, mulAut_ext_uCore m hm fun k => ?_⟩
  rw [coreAct_uCore, hg k]
  rfl

@[expose] def orbSize (m : ℕ) (v : coreMod m) : ℕ :=
  (Finset.univ.image fun σ : Equiv.Perm (Fin m) => coreAct m σ v).card

theorem orbSize_uCore5 (k : Fin 5) : orbSize 5 (uCore 5 (by decide) k) = 5 := by
  revert k
  decide +kernel

theorem eq_uCore_of_orbSize5 (v : coreMod 5) (h : orbSize 5 v = 5) :
    ∃ j, v = uCore 5 (by decide) j := by
  revert v
  decide +kernel

theorem eq_uCore_of_ne_one3 (v : coreMod 3) (h : v ≠ 1) : ∃ j, v = uCore 3 (by decide) j := by
  revert v
  decide

theorem orbSize_normalizes (m : ℕ) (hm : Odd m) (x : MulAut (coreMod m))
    (hN : ∀ σ : Equiv.Perm (Fin m), ∃ τ : Equiv.Perm (Fin m),
      x * coreAct m σ * x⁻¹ = coreAct m τ) (v : coreMod m) : orbSize m (x v) = orbSize m v := by
  choose f hf using hN
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 : x * coreAct m a * x⁻¹ = x * coreAct m b * x⁻¹ := by rw [hf a, hf b, h]
    have h2 : coreAct m a = coreAct m b := by
      have := mul_right_cancel h1
      exact mul_left_cancel this
    exact coreAct_injective m hm h2
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  have hx : ∀ σ, x (coreAct m σ v) = coreAct m (f σ) (x v) := by
    intro σ
    have := congrArg (fun y : MulAut (coreMod m) => y (x v)) (hf σ)
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
    exact this
  unfold orbSize
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun y => x⁻¹ y) ?_ x⁻¹.injective.injOn
    intro y hy
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨σ, rfl⟩ := hfsurj τ
    refine Finset.mem_image.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [← hx σ]
    simp
  · refine Finset.card_le_card_of_injOn (fun y => x y) ?_ x.injective.injOn
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨f σ, Finset.mem_univ _, (hx σ).symm⟩

theorem normLemma (m : ℕ) (hm : m = 3 ∨ m = 5) (x : MulAut (coreMod m))
    (hN : ∀ σ : Equiv.Perm (Fin m), ∃ τ : Equiv.Perm (Fin m),
      x * coreAct m σ * x⁻¹ = coreAct m τ) : ∃ σ : Equiv.Perm (Fin m), x = coreAct m σ := by
  rcases hm with rfl | rfl
  · refine exists_perm_of_uCore 3 (Or.inl rfl) x fun k => ?_
    refine eq_uCore_of_ne_one3 _ fun h => ?_
    exact uCore_ne_one 3 (by decide) (by decide) k (x.injective (h.trans (map_one x).symm))
  · refine exists_perm_of_uCore 5 (Or.inr (Or.inl rfl)) x fun k => ?_
    refine eq_uCore_of_orbSize5 _ ?_
    rw [orbSize_normalizes 5 (by decide) x hN, orbSize_uCore5]

end Ch3z

end CFSG.Quasithin
