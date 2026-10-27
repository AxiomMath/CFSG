module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.Three
  TableBExcTwoFusion

namespace TableBExcTwoTB

local instance neZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def rootsE8 : Fin 4 → Fin 2 → Fin 8 → ℤ :=
  ![![Pi.single 0 1, Pi.single 2 1], ![Pi.single 5 1, Pi.single 4 1],
    ![Pi.single 1 1, ![1, 1, 2, 3, 2, 1, 0, 0]], ![![2, 3, 4, 6, 5, 4, 3, 1], Pi.single 7 1]]

@[expose] def lamE8 : Fin 4 → Fin 2 → Fin 8 → ZMod 3 :=
  ![![![2, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0]],
    ![![0, 2, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 2]]]

theorem certE8 : ∀ (i : Fin 4) (k : Fin 2) (b : Fin 8),
    rootPairing .E8 (rootsE8 i k) (Pi.single b 1) =
      ∑ j, lamE8 i k j *
        (torusWord .E8 3 (wordE8G i) (Pi.single b 1) j - if j = b then 1 else 0) := by
  decide +kernel

theorem fix_kernel_E8 (i : Fin 4) (k : Fin 2) {x : Fin Tag.E8.rank → ZMod 3}
    (hx : torusWord .E8 3 (wordE8G i) x = x) : rootPairing .E8 (rootsE8 i k) x = 0 :=
  rootPairing_eq_zero_of_fixed (wordE8G i) (rootsE8 i k) (lamE8 i k) (certE8 i k) hx

@[expose] def uE8G2 : List (Fin Tag.E8.rank) := [3, 2, 0, 4, 3, 1, 2, 3, 4]

@[expose] def uE8G3 : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]

theorem wordE8G2_eq : wordE8G2 = ([] ++ [1] ++ []) ++ (uE8G2 ++ [5] ++ uE8G2.reverse) := by
  decide

theorem wordE8G3_eq : wordE8G3 = (uE8G3 ++ [7] ++ uE8G3.reverse) ++ ([] ++ [7] ++ []) := by
  decide

theorem uE8G2_smul : (coxeterSystem .E8).wordProd uE8G2 • (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) =
    (![1, 1, 2, 3, 2, 1, 0, 0] : Fin Tag.E8.rank → ℤ) := by
  rw [wordProd_smul_foldr]
  funext j
  fin_cases j <;> decide +kernel

theorem uE8G3_smul : (coxeterSystem .E8).wordProd uE8G3 • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) =
    (![2, 3, 4, 6, 5, 4, 3, 1] : Fin Tag.E8.rank → ℤ) := by
  rw [wordProd_smul_foldr]
  funext j
  fin_cases j <;> decide +kernel

private theorem modelHomE8_single_root (i : Fin 4) :
    modelHomE8 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) = gE8 i := by
  rw [modelHomE8, modelHom_inl, modelN_single, ZMod.val_one, pow_one]

private theorem gE8_mem_closure_of_roots {A : Subgroup (WeylGroup .E8)} (i : Fin 4)
    (hpair : ∀ k : Fin 2, ∀ x : Fin Tag.E8.rank → ZMod 3,
      (∀ a ∈ A, torusAct .E8 3 a x = x) → rootPairing .E8 (rootsE8 i k) x = 0) :
    gE8 i ∈ Subgroup.closure {r : WeylGroup .E8 | ∃ (u : WeylGroup .E8) (j : Fin Tag.E8.rank),
      (∀ x : Fin Tag.E8.rank → ZMod 3, (∀ a ∈ A, torusAct .E8 3 a x = x) →
        rootPairing .E8 (u • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) x = 0) ∧
      r = u * simple .E8 j * u⁻¹} := by
  have hp := palindrome_mem_closure (τ := .E8)
    (C := {x : Fin Tag.E8.rank → ZMod 3 | ∀ a ∈ A, torusAct .E8 3 a x = x})
  fin_cases i
  · change (coxeterSystem .E8).wordProd (([] ++ [0] ++ []) ++ ([] ++ [2] ++ [])) ∈ _
    rw [CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 0 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp [] 2 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 1 x hx)
  · change (coxeterSystem .E8).wordProd (([] ++ [5] ++ []) ++ ([] ++ [4] ++ [])) ∈ _
    rw [CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 5 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp [] 4 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 1 x hx)
  · change (coxeterSystem .E8).wordProd wordE8G2 ∈ _
    rw [wordE8G2_eq, CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 1 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp uE8G2 5 fun x hx => by rw [uE8G2_smul]; exact hpair 1 x hx)
  · change (coxeterSystem .E8).wordProd wordE8G3 ∈ _
    rw [wordE8G3_eq, CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp uE8G3 7 fun x hx => by rw [uE8G3_smul]; exact hpair 0 x hx)
      (hp [] 7 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 1 x hx)

theorem halfOffender_E8 : HalfOffender .E8 modelHomE8.range := by
  intro A hAS hA hA1 hcard
  have hkey := card_mul_card_fix_lt_or_zpowers_of_model (torusPerm .E8 3) modelHomE8
    modelHomE8_injective (T := 3 ^ 7)
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_zpowers (T := 3 ^ 7) (B₁ := 3 ^ 4) (B₅ := 3 ^ 3)
      (m := 2) (torusPerm .E8 3) modelHomE8 fix_caseI_E8 card_fixShift_E8 fix_centN_E8 caseII_E8
      (by norm_num) (by norm_num) h3 hc h1) hAS hA hA1
  simp only [torusPerm_apply] at hkey
  rcases hkey with h | ⟨i, h1, _, _⟩
  · exact absurd h (not_lt_of_ge hcard)
  · refine ⟨gE8 i, ?_, ?_⟩
    · rw [h1, modelHomE8_single_root i]
    · refine gE8_mem_closure_of_roots (A := A) i fun k x hx => ?_
      exact fix_kernel_E8 i k (by
        rw [torusWord_eq_torusAct cartan_symm_E8]
        exact hx (gE8 i) (by rw [h1, modelHomE8_single_root i]; exact Subgroup.mem_zpowers _))

end TableBExcTwoTB

end CFSG.StandardType

end
