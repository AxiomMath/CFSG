module

public import CFSG.Quasithin.Recognition.WBN.Weyl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4

import CFSG.GH74.QTGen4.DSGen4.L34Generic
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalBorel
import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie

public section

namespace CFSG.Quasithin.WBN

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Fin257.Sp4
  CFSG.Quasithin.F112R.St84.Sp44
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

theorem sp4_wS_mul_dSp_mul_inv {F : Type} [Field F] [CharP F 2] (s t : Fˣ) :
    (wS : antiSp F) * dSp s t * (wS : antiSp F)⁻¹ = dSp t s := by
  apply antiSp_ext
  rw [wS_inv, glMat_mul, glMat_mul, glMat_wS, glMat_dSp, glMat_dSp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSMat, dSpMat, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four,
      Matrix.diagonal_apply]

theorem sp4_wT_mul_dSp_mul_inv {F : Type} [Field F] [CharP F 2] (s t : Fˣ) :
    (wT : antiSp F) * dSp s t * (wT : antiSp F)⁻¹ = dSp s t⁻¹ := by
  apply antiSp_ext
  rw [wT_inv, glMat_mul, glMat_mul, glMat_wT, glMat_dSp, glMat_dSp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wTMat, dSpMat, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four,
      Matrix.diagonal_apply]

private theorem sp4_wS_wT_mul_dSp_mul_inv {F : Type} [Field F] [CharP F 2] (s t : Fˣ) :
    (wS * wT : antiSp F) * dSp s t * (wS * wT : antiSp F)⁻¹ = dSp t⁻¹ s := by
  have h : (wS * wT : antiSp F) * dSp s t * (wS * wT : antiSp F)⁻¹ =
      wS * (wT * dSp s t * (wT : antiSp F)⁻¹) * (wS : antiSp F)⁻¹ := by group
  rw [h, sp4_wT_mul_dSp_mul_inv, sp4_wS_mul_dSp_mul_inv]

private theorem sp4_wS_wT_sq_mul_dSp_mul_inv {F : Type} [Field F] [CharP F 2] (s t : Fˣ) :
    ((wS * wT) ^ 2 : antiSp F) * dSp s t * (((wS * wT) ^ 2 : antiSp F))⁻¹ = dSp s⁻¹ t⁻¹ := by
  have h : ((wS * wT) ^ 2 : antiSp F) * dSp s t * (((wS * wT) ^ 2 : antiSp F))⁻¹ =
      (wS * wT) * ((wS * wT) * dSp s t * (wS * wT : antiSp F)⁻¹) *
        (wS * wT : antiSp F)⁻¹ := by
    rw [pow_two]
    group
  rw [h, sp4_wS_wT_mul_dSp_mul_inv, sp4_wS_wT_mul_dSp_mul_inv]

private theorem wS_conj_mem_dTor {F : Type} [Field F] [Finite F] [CharP F 2] {x : antiSp F}
    (hx : x ∈ dTor F) : (wS : antiSp F) * x * (wS : antiSp F)⁻¹ ∈ dTor F := by
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
  rw [sp4_wS_mul_dSp_mul_inv]
  exact dSp_mem_dTor t s

private theorem wT_conj_mem_dTor {F : Type} [Field F] [Finite F] [CharP F 2] {x : antiSp F}
    (hx : x ∈ dTor F) : (wT : antiSp F) * x * (wT : antiSp F)⁻¹ ∈ dTor F := by
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
  rw [sp4_wT_mul_dSp_mul_inv]
  exact dSp_mem_dTor s t⁻¹

private theorem wS_mem_normalizer_dTor {F : Type} [Field F] [Finite F] [CharP F 2] :
    (wS : antiSp F) ∈ Subgroup.normalizer (dTor F : Set (antiSp F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨wS_conj_mem_dTor, fun hx => ?_⟩
  have h := wS_conj_mem_dTor hx
  have he : (wS : antiSp F) * (wS * x * wS⁻¹) * wS⁻¹ = x := by
    have h1 : (wS : antiSp F) * (wS * x * wS⁻¹) * wS⁻¹ =
        (wS * wS) * x * (wS⁻¹ * wS⁻¹) := by group
    rw [h1, wS_mul_self, wS_inv, wS_mul_self, one_mul, mul_one]
  rw [he] at h
  exact h

private theorem wT_mem_normalizer_dTor {F : Type} [Field F] [Finite F] [CharP F 2] :
    (wT : antiSp F) ∈ Subgroup.normalizer (dTor F : Set (antiSp F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨wT_conj_mem_dTor, fun hx => ?_⟩
  have h := wT_conj_mem_dTor hx
  have he : (wT : antiSp F) * (wT * x * wT⁻¹) * wT⁻¹ = x := by
    have h1 : (wT : antiSp F) * (wT * x * wT⁻¹) * wT⁻¹ =
        (wT * wT) * x * (wT⁻¹ * wT⁻¹) := by group
    rw [h1, wT_mul_self, wT_inv, wT_mul_self, one_mul, mul_one]
  rw [he] at h
  exact h

theorem invertsByWeyl_antiSp {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {m : ℕ} (hm : Odd m) :
    InvertsByWeyl (Subgroup.normalizer (radA1 F : Set (antiSp F)))
      (Subgroup.normalizer (radA2 F : Set (antiSp F))) m := by
  have hB := CFSG.Quasithin.H13.F431.SpModel.borel_antiSp (F := F) hn hF
  refine InvertsByWeyl.of_torus (U := antiUnipotent F) (H := dTor F) (hm := hm)
    (hU := hB.sylow.2.1) (hUn := ?_) (hUH := ?_) (hH := CFSG.Quasithin.F112R.St84.odd_card_dTor)
    (n₀ := (wS : antiSp F)) (n₁ := (wT : antiSp F)) (h₀ := wS_mem_normalizer_radA1)
    (h₁ := wT_mem_normalizer_radA2) (hn₀ := wS_mem_normalizer_dTor)
    (hn₁ := wT_mem_normalizer_dTor) (k := 2) ?_
  · exact Subgroup.normal_subgroupOf_of_le_normalizer
      (le_of_eq (CFSG.Quasithin.F112R.St84.normalizer_radA1_inf_normalizer_radA2 (F := F) hn hF))
  · exact ((CFSG.Quasithin.F112R.St84.normalizer_radA1_inf_normalizer_radA2 (F := F) hn hF).trans
      (CFSG.Quasithin.F112R.St84.B0_eq_sup_dTor (F := F))).symm
  · intro x hx _
    obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
    rw [sp4_wS_wT_sq_mul_dSp_mul_inv, dSp_inv]

theorem allInvertsByWeyl_sp4 {f : ℕ} (hf : 2 ≤ f) {m : ℕ} (hm : Odd m) :
    AllInvertsByWeyl (CFSG.Quasithin.IsSp4Over f) m := by
  intro Y _ hY T M₁ M₂ hpair
  rcases hY with ⟨hf1, -⟩ | ⟨-, hD⟩
  · omega
  · obtain ⟨-, F, hField, hFin, hChar, hcard, ⟨e⟩⟩ :=
      CFSG.Quasithin.H13.F431.exists_equiv_antiSp hD
    letI : Field F := hField
    letI : Finite F := hFin
    letI : CharP F 2 := hChar
    exact InvertsByWeyl.of_isYAmalgamPair
      (CFSG.GH74.QTGen4.DSGen4.L34.isYAmalgamPair_of_borelData
        (CFSG.Quasithin.H13.F431.SpModel.borel_antiSp (F := F) hf hcard)
        (CFSG.Quasithin.H13.F431.SpModel.O2_antiSp (F := F) hf hcard))
      (invertsByWeyl_antiSp hf hcard hm) e hpair

end CFSG.Quasithin.WBN
