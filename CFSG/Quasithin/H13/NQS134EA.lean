module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S134V1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv CFSG.Quasithin.H13.A6

@[expose] def wtP (x : P6) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 => Multiplicative.toAdd x i = 1).card

theorem wtP_cases : ∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
    x = 1 ∨ x = G6.allOnes 6 ∨ wtP x = 2 ∨ wtP x = 4 := by
  decide +kernel

theorem wtP_permAct : ∀ σ : Perm (Fin 6), ∀ x : P6, wtP (G6.permAct 6 σ x) = wtP x := by
  intro σ x
  simp only [wtP, G6.permAct_apply]
  refine Finset.card_bij (fun i _ => σ⁻¹ i)
    (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩)
    (fun i _ j _ h => σ⁻¹.injective h)
    (fun j hj => ⟨σ j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩)
  simpa using (Finset.mem_filter.1 hj).2

theorem wtP_e45 : wtP e45 = 2 := by decide

theorem wtP_e0123 : wtP e0123 = 4 := by decide

theorem wtP_allOnes : wtP (G6.allOnes 6) = 6 := by decide

theorem exists_perm_e45 : ∀ x : P6, wtP x = 2 → ∃ σ : Perm (Fin 6), G6.permAct 6 σ e45 = x := by
  decide +kernel

theorem exists_perm_e0123 :
    ∀ x : P6, wtP x = 4 → ∃ σ : Perm (Fin 6), G6.permAct 6 σ e0123 = x := by
  decide +kernel

theorem swap45_facts : Perm.sign (swap (4 : Fin 6) 5) = -1 ∧
    G6.permAct 6 (swap 4 5) e45 = e45 ∧ G6.permAct 6 (swap 4 5) e0123 = e0123 := by
  decide +kernel

@[expose] def wt2List : Finset P6 := Finset.univ.filter fun x : P6 => wtP x = 2

@[expose] def wt4List : Finset P6 := Finset.univ.filter fun x : P6 => wtP x = 4

theorem mem_wt2List {x : P6} : x ∈ wt2List ↔ wtP x = 2 := by
  simp [wt2List]

theorem mem_wt4List {x : P6} : x ∈ wt4List ↔ wtP x = 4 := by
  simp [wt4List]

theorem no_E8_wt_two : ∀ x ∈ wt2List, ∀ y ∈ wt2List, x * y ∈ wt2List → ∀ u ∈ wt2List,
    x * u ∈ wt2List → y * u ∈ wt2List → x * y * u ∉ wt2List := by
  decide +kernel

theorem no_E8_wt_four : ∀ x ∈ wt4List, ∀ y ∈ wt4List, x * y ∈ wt4List → ∀ u ∈ wt4List,
    x * u ∈ wt4List → y * u ∈ wt4List → x * y * u ∉ wt4List := by
  decide +kernel

theorem eq_swap_of_wt_two : ∀ σ : Perm (Fin 6), σ * σ = 1 →
    (∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
      G6.permAct 6 σ x * x = 1 ∨ wtP (G6.permAct 6 σ x * x) = 2) →
    σ = 1 ∨ ∃ i j : Fin 6, i ≠ j ∧ σ = swap i j := by
  decide +kernel

theorem eq_fpf_of_wt_four : ∀ σ : Perm (Fin 6), σ * σ = 1 →
    (∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
      G6.permAct 6 σ x * x = 1 ∨ wtP (G6.permAct 6 σ x * x) = 4) →
    σ = 1 ∨ ∀ i : Fin 6, σ i ≠ i := by
  decide +kernel

@[expose] def fpfList : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun σ : Perm (Fin 6) => σ * σ = 1 ∧ ∀ i : Fin 6, σ i ≠ i

theorem mem_fpfList {σ : Perm (Fin 6)} : σ ∈ fpfList ↔ σ * σ = 1 ∧ ∀ i : Fin 6, σ i ≠ i := by
  simp [fpfList]

theorem fpf_mul_fixed : ∀ σ ∈ fpfList, ∀ τ ∈ fpfList, σ * τ = τ * σ → σ ≠ τ →
    ∃ i : Fin 6, (σ * τ) i = i := by
  decide +kernel

theorem card_fix_fpf : ∀ σ ∈ fpfList,
    (Finset.univ.filter fun x : P6 => ∑ i, Multiplicative.toAdd x i = 0 ∧
      G6.permAct 6 σ x = x).card = 8 := by
  decide +kernel

theorem swap_mul_ne_swap : ∀ i j k l : Fin 6, i ≠ j → k ≠ l → swap i j ≠ swap k l →
    swap i j * swap k l = swap k l * swap i j → ∀ a b : Fin 6, swap i j * swap k l ≠ swap a b := by
  decide +kernel

end CFSG.Quasithin.H13.NQS134
