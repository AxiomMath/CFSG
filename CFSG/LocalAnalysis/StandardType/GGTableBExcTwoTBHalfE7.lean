module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.Three
  TableBExcTwoFusion

namespace TableBExcTwoTB

local instance neZeroRankE7 : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def rootsE7 : Fin 3 → Fin 2 → Fin 7 → ℤ :=
  ![![Pi.single 0 1, Pi.single 2 1], ![Pi.single 5 1, Pi.single 4 1],
    ![Pi.single 1 1, ![1, 1, 2, 3, 2, 1, 0]]]

@[expose] def lamE7 : Fin 3 → Fin 2 → Fin 7 → ZMod 3 :=
  ![![![2, 0, 1, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 2, 0], ![0, 0, 0, 0, 2, 0, 0]],
    ![![0, 2, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 2, 0]]]

theorem certE7 : ∀ (i : Fin 3) (k : Fin 2) (b : Fin 7),
    rootPairing .E7 (rootsE7 i k) (Pi.single b 1) =
      ∑ j, lamE7 i k j *
        (torusWord .E7 3 (wordE7G i) (Pi.single b 1) j - if j = b then 1 else 0) := by
  decide +kernel

theorem fix_kernel_E7 (i : Fin 3) (k : Fin 2) {x : Fin Tag.E7.rank → ZMod 3}
    (hx : torusWord .E7 3 (wordE7G i) x = x) : rootPairing .E7 (rootsE7 i k) x = 0 :=
  rootPairing_eq_zero_of_fixed (wordE7G i) (rootsE7 i k) (lamE7 i k) (certE7 i k) hx

@[expose] def uE7G2 : List (Fin Tag.E7.rank) := [3, 2, 0, 4, 3, 1, 2, 3, 4]

theorem wordE7G2_eq : wordE7G2 = ([] ++ [1] ++ []) ++ (uE7G2 ++ [5] ++ uE7G2.reverse) := by
  decide

theorem uE7G2_smul : (coxeterSystem .E7).wordProd uE7G2 • (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) =
    (![1, 1, 2, 3, 2, 1, 0] : Fin Tag.E7.rank → ℤ) := by
  rw [wordProd_smul_foldr]
  funext j
  fin_cases j <;> decide +kernel

private theorem modelHomE7_single_root (i : Fin 3) :
    modelHomE7 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) = gE7 i := by
  rw [modelHomE7, modelHom_inl, modelN_single, ZMod.val_one, pow_one]

private theorem gE7_mem_closure_of_roots {A : Subgroup (WeylGroup .E7)} (i : Fin 3)
    (hpair : ∀ k : Fin 2, ∀ x : Fin Tag.E7.rank → ZMod 3,
      (∀ a ∈ A, torusAct .E7 3 a x = x) → rootPairing .E7 (rootsE7 i k) x = 0) :
    gE7 i ∈ Subgroup.closure {r : WeylGroup .E7 | ∃ (u : WeylGroup .E7) (j : Fin Tag.E7.rank),
      (∀ x : Fin Tag.E7.rank → ZMod 3, (∀ a ∈ A, torusAct .E7 3 a x = x) →
        rootPairing .E7 (u • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) x = 0) ∧
      r = u * simple .E7 j * u⁻¹} := by
  have hp := palindrome_mem_closure (τ := .E7)
    (C := {x : Fin Tag.E7.rank → ZMod 3 | ∀ a ∈ A, torusAct .E7 3 a x = x})
  fin_cases i
  · change (coxeterSystem .E7).wordProd (([] ++ [0] ++ []) ++ ([] ++ [2] ++ [])) ∈ _
    rw [CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 0 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp [] 2 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 1 x hx)
  · change (coxeterSystem .E7).wordProd (([] ++ [5] ++ []) ++ ([] ++ [4] ++ [])) ∈ _
    rw [CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 5 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp [] 4 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 1 x hx)
  · change (coxeterSystem .E7).wordProd wordE7G2 ∈ _
    rw [wordE7G2_eq, CoxeterSystem.wordProd_append]
    exact mul_mem
      (hp [] 1 fun x hx => by rw [CoxeterSystem.wordProd_nil, one_smul]; exact hpair 0 x hx)
      (hp uE7G2 5 fun x hx => by rw [uE7G2_smul]; exact hpair 1 x hx)

theorem halfOffender_E7 : HalfOffender .E7 modelHomE7.range := by
  intro A hAS hA hA1 hcard
  have hkey := card_mul_card_fix_lt_or_zpowers_of_model (torusPerm .E7 3) modelHomE7
    modelHomE7_injective (T := 3 ^ 6)
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_zpowers (T := 3 ^ 6) (B₁ := 3 ^ 4) (B₅ := 3 ^ 3)
      (m := 1) (torusPerm .E7 3) modelHomE7 fix_caseI_E7 card_fixShift_E7 fix_centN_E7 caseII_E7
      (by norm_num) (by norm_num) h3 hc h1) hAS hA hA1
  simp only [torusPerm_apply] at hkey
  rcases hkey with h | ⟨i, h1, _, _, _⟩
  · exact absurd h (not_lt_of_ge hcard)
  · refine ⟨gE7 i, ?_, ?_⟩
    · rw [h1, modelHomE7_single_root i]
    · refine gE7_mem_closure_of_roots (A := A) i fun k x hx => ?_
      exact fix_kernel_E7 i k (by
        rw [torusWord_eq_torusAct cartan_symm_E7]
        exact hx (gE7 i) (by rw [h1, modelHomE7_single_root i]; exact Subgroup.mem_zpowers _))

end TableBExcTwoTB

end CFSG.StandardType

end
