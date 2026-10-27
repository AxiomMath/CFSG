module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B3Tab
public import CFSG.Quasithin.H13.GoldschmidtC137Concl

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

@[expose] def cT1 : Gp 6 := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def cT2 : Gp 6 := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def sw0 : Gp 6 := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

theorem cT1_even : cT1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem cT2_even : cT2 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sw0_odd : sw0 ∉ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem cT_comm : cT1 * cT2 * cT1⁻¹ * cT2⁻¹ = 1 := by decide +kernel

theorem sw0_conj1 : sw0 * cT1 * sw0⁻¹ = cT2 := by decide +kernel

theorem sw0_conj2 : sw0 * cT2 * sw0⁻¹ = cT1 := by decide +kernel

@[expose] def E9l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,4,5,3], [0,1,2,5,3,4], [1,2,0,3,4,5], [1,2,0,4,5,3], [1,2,0,5,3,4],
    [2,0,1,3,4,5], [2,0,1,4,5,3], [2,0,1,5,3,4]]

set_option maxRecDepth 100000 in
theorem subOK_E9 : subOK 6 E9l = true := by decide +kernel

noncomputable abbrev E9 : Subgroup (Gp 6) := B3.subOf 6 E9l

theorem mem_E9 {σ : Gp 6} : σ ∈ E9 ↔ tab σ ∈ E9l := B3.mem_subOf subOK_E9

theorem card_E9 : Nat.card E9 = 9 := by
  rw [B3.card_subOf subOK_E9]
  decide +kernel

set_option maxRecDepth 100000 in
theorem E9_decomp_list : ∀ σ : Gp 6, tab σ ∈ E9l →
    ∃ i j : Fin 3, σ = cT1 ^ (i : ℕ) * cT2 ^ (j : ℕ) := by decide +kernel

theorem E9_decomp {σ : Gp 6} (h : σ ∈ E9) : ∃ i j : ℕ, σ = cT1 ^ i * cT2 ^ j := by
  obtain ⟨i, j, hij⟩ := E9_decomp_list σ (mem_E9.1 h)
  exact ⟨i, j, hij⟩

theorem E9_le_alt : E9 ≤ alternatingGroup (Fin 6) := by
  intro σ hσ
  obtain ⟨i, j, rfl⟩ := E9_decomp hσ
  exact (alternatingGroup (Fin 6)).mul_mem ((alternatingGroup (Fin 6)).pow_mem cT1_even i)
    ((alternatingGroup (Fin 6)).pow_mem cT2_even j)

theorem relIndex_E9 : E9.relIndex (alternatingGroup (Fin 6)) = 40 := by
  have h1 := Subgroup.relIndex_mul_card E9 (alternatingGroup (Fin 6))
  rw [inf_eq_left.2 E9_le_alt, card_E9, card_alt6] at h1
  omega

end CFSG.Quasithin.H13.U3.GC137
