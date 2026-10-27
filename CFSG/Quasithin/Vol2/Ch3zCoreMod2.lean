module

public import CFSG.Quasithin.Vol2.Ch3zCoreMod
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin

open G6

namespace Ch3z

@[expose] def wt {m : ℕ} (v : coreMod m) : ℕ :=
  (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (v : PermMod m) i ≠ 0).card

theorem supp_coreAct {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : coreMod m) :
    (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd ((coreAct m σ v : coreMod m) : PermMod m) i ≠ 0) =
      (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (v : PermMod m) i ≠ 0).map
        σ.toEmbedding := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  rfl

theorem wt_coreAct {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : coreMod m) : wt (coreAct m σ v) = wt v := by
  unfold wt
  rw [supp_coreAct, Finset.card_map]

theorem exists_perm_of_wt_eq {m : ℕ} {v w : coreMod m} (h : wt v = wt w) :
    ∃ σ : Equiv.Perm (Fin m), coreAct m σ v = w := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (v : PermMod m) i ≠ 0)
    (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (w : PermMod m) i ≠ 0) h
  refine ⟨σ, Subtype.ext ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  have h1 : i ∈ (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (w : PermMod m) i ≠ 0) ↔
      σ.symm i ∈ (Finset.univ.filter fun i : Fin m => Multiplicative.toAdd (v : PermMod m) i ≠ 0) := by
    rw [← hσ, Finset.mem_map_equiv]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  show Multiplicative.toAdd (v : PermMod m) (σ⁻¹ i) = Multiplicative.toAdd (w : PermMod m) i
  have h2 : σ⁻¹ i = σ.symm i := rfl
  rw [h2]
  generalize Multiplicative.toAdd (v : PermMod m) (σ.symm i) = a at h1 ⊢
  generalize Multiplicative.toAdd (w : PermMod m) i = b at h1 ⊢
  revert a b
  decide

theorem image_coreAct_eq {m : ℕ} (v : coreMod m) :
    Finset.univ.image (fun σ : Equiv.Perm (Fin m) => coreAct m σ v) =
      Finset.univ.filter fun w : coreMod m => wt w = wt v := by
  classical
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨σ, rfl⟩
    exact wt_coreAct σ v
  · intro h
    obtain ⟨σ, hσ⟩ := exists_perm_of_wt_eq h.symm
    exact ⟨σ, hσ⟩

theorem orbSize_eq_card_wt {m : ℕ} (v : coreMod m) :
    orbSize m v = (Finset.univ.filter fun w : coreMod m => wt w = wt v).card := by
  unfold orbSize
  rw [image_coreAct_eq]

theorem orbSize_uCore7 (k : Fin 7) : orbSize 7 (uCore 7 (by decide) k) = 7 := by
  rw [orbSize_eq_card_wt]
  revert k
  decide +kernel

theorem eq_uCore_of_orbSize7 (v : coreMod 7) (h : orbSize 7 v = 7) :
    ∃ j, v = uCore 7 (by decide) j := by
  rw [orbSize_eq_card_wt] at h
  revert v
  decide +kernel

theorem normLemma7 (x : MulAut (coreMod 7))
    (hN : ∀ σ : Equiv.Perm (Fin 7), ∃ τ : Equiv.Perm (Fin 7), x * coreAct 7 σ * x⁻¹ = coreAct 7 τ) :
    ∃ σ : Equiv.Perm (Fin 7), x = coreAct 7 σ := by
  refine exists_perm_of_uCore 7 (Or.inr (Or.inr rfl)) x fun k => ?_
  refine eq_uCore_of_orbSize7 _ ?_
  rw [orbSize_normalizes 7 (by decide) x hN, orbSize_uCore7]

set_option synthInstance.maxSize 4096 in
theorem core_key3 (v w : coreMod 3) (hv : v ≠ 1) :
    w = 1 ∨ wt w = wt v ∨ ∃ a b : coreMod 3, wt a = wt v ∧ wt b = wt v ∧ w = a * b := by
  revert v w
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem core_key5 (v w : coreMod 5) (hv : v ≠ 1) :
    w = 1 ∨ wt w = wt v ∨ ∃ a b : coreMod 5, wt a = wt v ∧ wt b = wt v ∧ w = a * b := by
  revert v w
  decide +kernel

theorem core_irred (m : ℕ) (hm : m = 3 ∨ m = 5) (W : Subgroup (coreMod m))
    (hW : ∀ σ : Equiv.Perm (Fin m), ∀ w ∈ W, coreAct m σ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv1⟩ : ∃ v ∈ W, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot.mpr (hcon x hx)))
  have hclass : ∀ a : coreMod m, wt a = wt v → a ∈ W := fun a ha => by
    obtain ⟨σ, hσ⟩ := exists_perm_of_wt_eq ha.symm
    rw [← hσ]
    exact hW σ v hvW
  have key : ∀ w : coreMod m, w = 1 ∨ wt w = wt v ∨
      ∃ a b : coreMod m, wt a = wt v ∧ wt b = wt v ∧ w = a * b := by
    rcases hm with rfl | rfl
    · exact fun w => core_key3 v w hv1
    · exact fun w => core_key5 v w hv1
  rw [eq_top_iff]
  intro w _
  rcases key w with h | h | ⟨a, b, ha, hb, rfl⟩
  · rw [h]
    exact W.one_mem
  · exact hclass w h
  · exact W.mul_mem (hclass a ha) (hclass b hb)

set_option synthInstance.maxSize 4096 in
theorem core_fixed_all (m : ℕ) (hm : m = 3 ∨ m = 5) (v : coreMod m)
    (h : ∀ σ : Equiv.Perm (Fin m), coreAct m σ v = v) : v = 1 := by
  rcases hm with rfl | rfl
  · revert v
    decide +kernel
  · revert v
    decide +kernel

end Ch3z

end CFSG.Quasithin
