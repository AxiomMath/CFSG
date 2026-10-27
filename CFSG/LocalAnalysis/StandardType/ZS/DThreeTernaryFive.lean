module

public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zt5_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private def zt5_code : Fin 5 → ℕ := ![81, 120, 27, 49, 1]

private def zt5_init : List ℕ := [81, 120, 27, 49, 1]

private def zt5_vec (i : Fin 5) : Fin 5 → ZMod 3 := ternaryDecode 5 (zt5_code i)

private noncomputable def zt5_refl (i : Fin 5) : R3 (diagF3 5 1) := reflBar (diagF3 5 1) (zt5_vec i)

private theorem zt5_normDot : ∀ i : Fin 5, diagDot 5 1 (zt5_vec i) (zt5_vec i) = 1 := by
  decide +kernel

private theorem zt5_norm (i : Fin 5) : diagF3 5 1 (zt5_vec i) (zt5_vec i) = 1 := by
  rw [diagF3_eq_diagDot]
  exact zt5_normDot i

private theorem zt5_exp : ∀ i j : Fin 5, i ≠ j →
    kFiveExp i j = if diagDot 5 1 (zt5_vec i) (zt5_vec j) = 0 then 2 else 3 := by
  decide +kernel

private theorem zt5_forms :
    diagDot 5 1 (zt5_vec 1) (zt5_vec 2) = 1 ∧
      diagDot 5 1 (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2)
        (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2) = 1 ∧
      diagDot 5 1 (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2)
        (zt5_vec 3) = 2 := by
  decide +kernel

private theorem zt5_init_spec : ∀ k ∈ zt5_init, ∃ i : Fin 5, zt5_vec i = ternaryDecode 5 k := by
  decide +kernel

private def zt5_steps : List (ℕ × ℕ) :=
  [(81, 81), (81, 120), (120, 120), (120, 27), (120, 49), (27, 27), (27, 49), (27, 201),
   (27, 142), (49, 49), (49, 1), (49, 201), (49, 147), (49, 228), (49, 221), (1, 1), (1, 142),
   (1, 76), (1, 221), (1, 223), (1, 226), (1, 145), (1, 155), (81, 228), (81, 221), (81, 223),
   (81, 226), (81, 155), (81, 116), (81, 224), (81, 227), (81, 200), (120, 145), (120, 143),
   (120, 77), (120, 227), (120, 146), (120, 196), (120, 197), (27, 228), (27, 223), (27, 224),
   (49, 116), (49, 200), (49, 197), (49, 235), (49, 185), (49, 178), (1, 77), (1, 224),
   (1, 227), (1, 236), (1, 185), (1, 179), (162, 147), (162, 155), (162, 143), (162, 146),
   (162, 196), (162, 184), (162, 178), (162, 95), (162, 107), (162, 123), (201, 188),
   (201, 95), (201, 204), (240, 76), (240, 200), (240, 107), (240, 176), (240, 123), (240, 52),
   (240, 6), (147, 107), (147, 176), (147, 204), (147, 6), (142, 80), (54, 123), (54, 52),
   (54, 53), (76, 185), (76, 53), (228, 80)]

private theorem zt5_hsFive : HSFiveRel zt5_refl := by
  simp only [HSFiveRel]
  have hf : IsF3Form (diagF3 5 1) := isF3Form_diagF3 (by decide)
  have hdiag : ∀ i : Fin 5, kFiveExp i i = 1 := by decide +kernel
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, pow_one]
      exact reflBar_mul_self (zt5_vec i)
    · rw [zt5_exp i j hij]
      simpa only [zt5_refl, diagF3_eq_diagDot] using
        reflBar_mul_reflBar_pow_eq_one hf (zt5_norm i) (zt5_norm j)
  · obtain ⟨-, hnormA, hpairA3⟩ := zt5_forms
    have hconj : zt5_refl 2 * zt5_refl 1 * zt5_refl 2 =
        reflBar (diagF3 5 1) (F3.act (F3.refl (diagF3 5 1) (zt5_vec 2)) (zt5_vec 1)) := by
      simpa only [zt5_refl] using reflBar_conj hf (zt5_vec 2) (zt5_vec 1)
    have hact : F3.act (F3.refl (diagF3 5 1) (zt5_vec 2)) (zt5_vec 1) =
        zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2 := by
      rw [F3.act_refl (zt5_norm 2), diagF3_eq_diagDot]
    have hA : diagF3 5 1
        (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2)
        (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2) = 1 := by
      rw [diagF3_eq_diagDot]
      exact hnormA
    have hA3 : diagF3 5 1
        (zt5_vec 1 + diagDot 5 1 (zt5_vec 1) (zt5_vec 2) • zt5_vec 2) (zt5_vec 3) ≠ 0 := by
      rw [diagF3_eq_diagDot, hpairA3]
      decide
    have hextra : (zt5_refl 2 * zt5_refl 1 * zt5_refl 2 * zt5_refl 3) ^ 3 = 1 := by
      rw [hconj, hact]
      simpa only [zt5_refl] using reflBar_mul_pow_three hf hA (zt5_norm 3) hA3
    exact hextra

private theorem zt5_closure : Subgroup.closure (Set.range zt5_refl) = ⊤ := by
  refine eq_top_of_diagChain (m := 5) (δ := 1) (by norm_num) one_ne_zero
    (H := Subgroup.closure (Set.range zt5_refl)) (init := zt5_init) (steps := zt5_steps) ?_ ?_ ?_
  · intro k hk
    obtain ⟨i, hi⟩ := zt5_init_spec k hk
    rw [← hi]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  · decide +kernel
  · decide +kernel

theorem exists_hsFiveRel_D3_diagF3_five_one :
    ∃ r : Fin 5 → R3 (diagF3 5 1), (∀ i, r i ∈ D3 (diagF3 5 1)) ∧ HSFiveRel r ∧
      Subgroup.closure (Set.range r) = ⊤ :=
  ⟨zt5_refl, fun i => reflBar_mem_D3 (zt5_norm i), zt5_hsFive, zt5_closure⟩

theorem exists_frame_D3_diagF3_five_one :
    ∃ d : Fin 5 → R3 (diagF3 5 1), (∀ i, d i ∈ D3 (diagF3 5 1)) ∧ Function.Injective d ∧
      (Pairwise fun i j => Commute (d i) (d j)) ∧ (List.ofFn d).prod = 1 :=
  ⟨fun i => reflBar (diagF3 5 1) (Pi.single i 1), frame_reflBar_diagF3_one (by norm_num)⟩

end CFSG.StandardType.ZS
