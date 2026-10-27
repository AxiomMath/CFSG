module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11

open CFSG.ComponentClassification.OutcomeLocal

variable {m : ℕ}

variable {m : ℕ}

theorem sym_single_add_single_eq_one {i k j : Fin m} (h : (Pi.single i (1 : ZMod 2) +
    Pi.single k (1 : ZMod 2) : Fin m → ZMod 2) j = 1) : j = i ∨ j = k := by
  by_contra hcon
  push Not at hcon
  simp [hcon.1, hcon.2] at h

theorem sym_perm_eq_one_of_pair_fixed (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (h : ∀ i k : Fin m, i ≠ k → permCoord σ (Pi.single i 1 + Pi.single k 1) =
      Pi.single i 1 + Pi.single k 1) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  have hone : ∀ k : Fin m, k ≠ i → σ i = i ∨ σ i = k := by
    intro k hki
    have := congrFun (h i k hki.symm) (σ i)
    rw [permCoord_apply, show σ⁻¹ (σ i) = i by simp] at this
    apply sym_single_add_single_eq_one (i := i) (k := k)
    rw [← this]
    simp [Pi.single_eq_of_ne hki.symm]
  have hcard : 1 < (Finset.univ.erase i : Finset (Fin m)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have ha' := hone a (Finset.ne_of_mem_erase ha)
  have hb' := hone b (Finset.ne_of_mem_erase hb)
  simp only [Equiv.Perm.coe_one, id_eq]
  rcases ha' with h1 | h1
  · exact h1
  · rcases hb' with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab

theorem sumZeroRep_injective' (hm : 3 ≤ m) : Function.Injective (sumZeroRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine sym_perm_eq_one_of_pair_fixed hm σ fun i k _ => ?_
  have hx := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m) =>
    (g : sumZero m →ₗ[ZMod 2] sumZero m) (pairVec i k)) hσ
  simp only [sumZeroRep_apply, Units.val_one, Module.End.one_apply] at hx
  have := congrArg (fun y : sumZero m => (y : Fin m → ZMod 2)) hx
  simpa only [coe_sumZeroEquiv, coe_pairVec] using this

theorem heartRep_injective' (hm : 5 ≤ m) : Function.Injective (heartRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine sym_perm_eq_one_of_pair_fixed (by omega) σ fun i k hik => ?_
  have hx := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m) =>
    (g : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m ⧸ onesLine m))
      (Submodule.Quotient.mk (pairVec i k))) hσ
  simp only [heartRep_apply_mk, Units.val_one, Module.End.one_apply] at hx
  rw [Submodule.Quotient.eq] at hx
  obtain ⟨c, hc⟩ := mem_onesLine.mp hx
  have hc' : ∀ j, permCoord σ (Pi.single i 1 + Pi.single k 1) j -
      (Pi.single i 1 + Pi.single k 1 : Fin m → ZMod 2) j = c := by
    intro j
    have := congrFun hc j
    simpa only [Submodule.coe_sub, Pi.sub_apply, coe_sumZeroEquiv, coe_pairVec] using this
  have hc0 : c = 0 := by
    classical
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j ∉ ({σ i, σ k, i, k} : Finset (Fin m)) := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ {σ i, σ k, i, k} := fun j _ => hall j
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_le_four (a := σ i) (b := σ k) (c := i) (d := k)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨h1, h2, h3, h4⟩ := hj
    rw [← hc' j, permCoord_apply]
    have e1 : σ⁻¹ j ≠ i := fun h => h1 (by rw [← h]; simp)
    have e2 : σ⁻¹ j ≠ k := fun h => h2 (by rw [← h]; simp)
    simp only [Pi.add_apply, Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2,
      Pi.single_eq_of_ne h3, Pi.single_eq_of_ne h4]
    simp
  funext j
  have := hc' j
  rw [hc0, sub_eq_zero] at this
  exact this

end CFSG.Quasithin.G11
