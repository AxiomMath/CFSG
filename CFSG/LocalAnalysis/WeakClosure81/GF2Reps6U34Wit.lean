module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourWith
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6U34Model
import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.U34

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.SeitzGeneration.HeisSmall
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

local notation "β₀" => suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv

private def c1M : M3 GF16 :=
  ⟨GF16.ofNat' 1, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 1,
    GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0⟩

private def c1InvM : M3 GF16 := c1M

private def c2M : M3 GF16 :=
  ⟨GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0,
    GF16.ofNat' 6, GF16.ofNat' 0, GF16.ofNat' 7,
    GF16.ofNat' 7, GF16.ofNat' 0, GF16.ofNat' 6⟩

private def c2InvM : M3 GF16 :=
  ⟨GF16.ofNat' 0, GF16.ofNat' 6, GF16.ofNat' 7,
    GF16.ofNat' 1, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 7, GF16.ofNat' 6⟩

private def xM : M3 GF16 :=
  ⟨GF16.ofNat' 7, GF16.ofNat' 3, GF16.ofNat' 15,
    GF16.ofNat' 4, GF16.ofNat' 12, GF16.ofNat' 9,
    GF16.ofNat' 0, GF16.ofNat' 2, GF16.ofNat' 9⟩

private def xInvM : M3 GF16 :=
  ⟨GF16.ofNat' 7, GF16.ofNat' 5, GF16.ofNat' 0,
    GF16.ofNat' 2, GF16.ofNat' 10, GF16.ofNat' 3,
    GF16.ofNat' 8, GF16.ofNat' 14, GF16.ofNat' 14⟩

private def kM : M3 GF16 :=
  ⟨GF16.ofNat' 5, GF16.ofNat' 0, GF16.ofNat' 2,
    GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0,
    GF16.ofNat' 3, GF16.ofNat' 0, GF16.ofNat' 4⟩

private def kInvM : M3 GF16 :=
  ⟨GF16.ofNat' 4, GF16.ofNat' 0, GF16.ofNat' 2,
    GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0,
    GF16.ofNat' 3, GF16.ofNat' 0, GF16.ofNat' 5⟩

private def k'M : M3 GF16 :=
  ⟨GF16.ofNat' 9, GF16.ofNat' 15, GF16.ofNat' 6,
    GF16.ofNat' 5, GF16.ofNat' 2, GF16.ofNat' 0,
    GF16.ofNat' 10, GF16.ofNat' 11, GF16.ofNat' 7⟩

private def k'InvM : M3 GF16 :=
  ⟨GF16.ofNat' 14, GF16.ofNat' 4, GF16.ofNat' 12,
    GF16.ofNat' 8, GF16.ofNat' 3, GF16.ofNat' 13,
    GF16.ofNat' 6, GF16.ofNat' 0, GF16.ofNat' 7⟩

private def wM : M3 GF16 :=
  ⟨GF16.ofNat' 14, GF16.ofNat' 6, GF16.ofNat' 15,
    GF16.ofNat' 6, GF16.ofNat' 1, GF16.ofNat' 6,
    GF16.ofNat' 15, GF16.ofNat' 6, GF16.ofNat' 14⟩

private def w2M : M3 GF16 :=
  ⟨GF16.ofNat' 6, GF16.ofNat' 0, GF16.ofNat' 7,
    GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0,
    GF16.ofNat' 7, GF16.ofNat' 0, GF16.ofNat' 6⟩

private def w'M : M3 GF16 :=
  ⟨GF16.ofNat' 5, GF16.ofNat' 12, GF16.ofNat' 9,
    GF16.ofNat' 12, GF16.ofNat' 14, GF16.ofNat' 5,
    GF16.ofNat' 9, GF16.ofNat' 5, GF16.ofNat' 10⟩

private def w'2M : M3 GF16 :=
  ⟨GF16.ofNat' 0, GF16.ofNat' 6, GF16.ofNat' 7,
    GF16.ofNat' 6, GF16.ofNat' 6, GF16.ofNat' 1,
    GF16.ofNat' 7, GF16.ofNat' 1, GF16.ofNat' 7⟩

private def conjKC1M : M3 GF16 :=
  ⟨GF16.ofNat' 7, GF16.ofNat' 2, GF16.ofNat' 10,
    GF16.ofNat' 3, GF16.ofNat' 0, GF16.ofNat' 5,
    GF16.ofNat' 12, GF16.ofNat' 4, GF16.ofNat' 6⟩

private def conjKC2M : M3 GF16 :=
  ⟨GF16.ofNat' 10, GF16.ofNat' 5, GF16.ofNat' 6,
    GF16.ofNat' 2, GF16.ofNat' 0, GF16.ofNat' 4,
    GF16.ofNat' 7, GF16.ofNat' 3, GF16.ofNat' 12⟩

private def conjKC2InvM : M3 GF16 :=
  ⟨GF16.ofNat' 12, GF16.ofNat' 3, GF16.ofNat' 7,
    GF16.ofNat' 4, GF16.ofNat' 0, GF16.ofNat' 2,
    GF16.ofNat' 6, GF16.ofNat' 5, GF16.ofNat' 10⟩

private def conjK'C1M : M3 GF16 :=
  ⟨GF16.ofNat' 6, GF16.ofNat' 8, GF16.ofNat' 5,
    GF16.ofNat' 15, GF16.ofNat' 7, GF16.ofNat' 7,
    GF16.ofNat' 4, GF16.ofNat' 7, GF16.ofNat' 0⟩

private def conjK'C2InvM : M3 GF16 :=
  ⟨GF16.ofNat' 14, GF16.ofNat' 15, GF16.ofNat' 4,
    GF16.ofNat' 8, GF16.ofNat' 12, GF16.ofNat' 8,
    GF16.ofNat' 5, GF16.ofNat' 8, GF16.ofNat' 4⟩

private theorem c1_mul : c1M * c1InvM = 1 := by ext <;> decide
private theorem c1_inv_mul : c1InvM * c1M = 1 := by ext <;> decide
private theorem c1_det : c1M.det = 1 := by decide
private theorem c1_uni : (c1M.map (· ^ (2 ^ 2))).transpose * c1M = 1 := by ext <;> decide

private theorem c2_mul : c2M * c2InvM = 1 := by ext <;> decide
private theorem c2_inv_mul : c2InvM * c2M = 1 := by ext <;> decide
private theorem c2_det : c2M.det = 1 := by decide
private theorem c2_uni : (c2M.map (· ^ (2 ^ 2))).transpose * c2M = 1 := by ext <;> decide

private theorem x_mul : xM * xInvM = 1 := by ext <;> decide
private theorem x_inv_mul : xInvM * xM = 1 := by ext <;> decide
private theorem x_det : xM.det = 1 := by decide
private theorem x_uni : (xM.map (· ^ (2 ^ 2))).transpose * xM = 1 := by ext <;> decide

private theorem k_mul : kM * kInvM = 1 := by ext <;> decide
private theorem k_inv_mul : kInvM * kM = 1 := by ext <;> decide
private theorem k_det : kM.det = 1 := by decide
private theorem k_uni : (kM.map (· ^ (2 ^ 2))).transpose * kM = 1 := by ext <;> decide

private theorem k'_mul : k'M * k'InvM = 1 := by ext <;> decide
private theorem k'_inv_mul : k'InvM * k'M = 1 := by ext <;> decide
private theorem k'_det : k'M.det = 1 := by decide
private theorem k'_uni : (k'M.map (· ^ (2 ^ 2))).transpose * k'M = 1 := by ext <;> decide

private def c1U : unitarySU 2 2 GF16 3 := mk c1M c1InvM c1_mul c1_inv_mul c1_det c1_uni

private def c2U : unitarySU 2 2 GF16 3 := mk c2M c2InvM c2_mul c2_inv_mul c2_det c2_uni

private def xU : unitarySU 2 2 GF16 3 := mk xM xInvM x_mul x_inv_mul x_det x_uni

private def kU : unitarySU 2 2 GF16 3 := mk kM kInvM k_mul k_inv_mul k_det k_uni

private def k'U : unitarySU 2 2 GF16 3 := mk k'M k'InvM k'_mul k'_inv_mul k'_det k'_uni

private theorem toM3_c1 : toM3 c1U = c1M :=
  toM3_mk c1M c1InvM c1_mul c1_inv_mul c1_det c1_uni

private theorem toM3_c2 : toM3 c2U = c2M :=
  toM3_mk c2M c2InvM c2_mul c2_inv_mul c2_det c2_uni

private theorem toM3_c2_inv : toM3 c2U⁻¹ = c2InvM :=
  toM3_mk_inv c2M c2InvM c2_mul c2_inv_mul c2_det c2_uni

private theorem toM3_x : toM3 xU = xM :=
  toM3_mk xM xInvM x_mul x_inv_mul x_det x_uni

private theorem toM3_x_inv : toM3 xU⁻¹ = xInvM :=
  toM3_mk_inv xM xInvM x_mul x_inv_mul x_det x_uni

private theorem toM3_k : toM3 kU = kM :=
  toM3_mk kM kInvM k_mul k_inv_mul k_det k_uni

private theorem toM3_k_inv : toM3 kU⁻¹ = kInvM :=
  toM3_mk_inv kM kInvM k_mul k_inv_mul k_det k_uni

private theorem toM3_k' : toM3 k'U = k'M :=
  toM3_mk k'M k'InvM k'_mul k'_inv_mul k'_det k'_uni

private theorem toM3_k'_inv : toM3 k'U⁻¹ = k'InvM :=
  toM3_mk_inv k'M k'InvM k'_mul k'_inv_mul k'_det k'_uni

private noncomputable def w : unitarySU 2 2 GF16 3 := β₀ xU * xU⁻¹
private noncomputable def w' : unitarySU 2 2 GF16 3 := β₀ (xU⁻¹) * (xU⁻¹)⁻¹

private theorem toM3_w : toM3 w = wM := by
  rw [show w = β₀ xU * xU⁻¹ from rfl, toM3_mul, toM3_suField, toM3_x, toM3_x_inv]
  ext <;> decide

private theorem toM3_w' : toM3 w' = w'M := by
  rw [show w' = β₀ (xU⁻¹) * (xU⁻¹)⁻¹ from rfl, inv_inv, toM3_mul,
    toM3_suField, toM3_x_inv, toM3_x]
  ext <;> decide

private theorem toM3_w2 : toM3 (w ^ 2) = w2M := by
  rw [pow_two, toM3_mul, toM3_w]
  ext <;> decide

private theorem toM3_w'2 : toM3 (w' ^ 2) = w'2M := by
  rw [pow_two, toM3_mul, toM3_w']
  ext <;> decide

private theorem w4 : w ^ 4 = 1 := by
  apply toM3_injective
  rw [toM3_one, show w ^ 4 = w ^ 2 * w ^ 2 by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
    toM3_mul, toM3_w2]
  ext <;> decide

private theorem w'4 : w' ^ 4 = 1 := by
  apply toM3_injective
  rw [toM3_one,
    show w' ^ 4 = w' ^ 2 * w' ^ 2 by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
    toM3_mul, toM3_w'2]
  ext <;> decide

private theorem w2M_ne_one : w2M ≠ 1 := by
  intro h
  have h00 : w2M.a00 = (1 : M3 GF16).a00 := congrArg (fun A : M3 GF16 => A.a00) h
  exact absurd h00 (by decide)

private theorem w'2M_ne_one : w'2M ≠ 1 := by
  intro h
  have h00 : w'2M.a00 = (1 : M3 GF16).a00 := congrArg (fun A : M3 GF16 => A.a00) h
  exact absurd h00 (by decide)

private theorem w2_ne_one : w ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg toM3 h
  rw [toM3_w2, toM3_one] at h'
  exact w2M_ne_one h'

private theorem w'2_ne_one : w' ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg toM3 h
  rw [toM3_w'2, toM3_one] at h'
  exact w'2M_ne_one h'

private theorem orderOf_w : orderOf w = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hnot : ¬ w ^ 2 ^ 1 = 1 := by simpa using w2_ne_one
  have hfin : w ^ 2 ^ (1 + 1) = 1 := by simpa using w4
  simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin

private theorem orderOf_w' : orderOf w' = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hnot : ¬ w' ^ 2 ^ 1 = 1 := by simpa using w'2_ne_one
  have hfin : w' ^ 2 ^ (1 + 1) = 1 := by simpa using w'4
  simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin

private theorem c1_mem_autFixed : c1U ∈ autFixed β₀ := by
  rw [mem_autFixed_iff]
  apply toM3_injective
  rw [toM3_suField, toM3_c1]
  ext <;> decide

private theorem c2_mem_autFixed : c2U ∈ autFixed β₀ := by
  rw [mem_autFixed_iff]
  apply toM3_injective
  rw [toM3_suField, toM3_c2]
  ext <;> decide

private theorem toM3_conj (κ g : unitarySU 2 2 GF16 3) :
    toM3 (MulAut.conj κ g) = toM3 κ * toM3 g * toM3 κ⁻¹ := by
  rw [MulAut.conj_apply, toM3_mul, toM3_mul]

private theorem toM3_conj_inv (κ g : unitarySU 2 2 GF16 3) :
    toM3 ((MulAut.conj κ g)⁻¹) = toM3 κ * toM3 g⁻¹ * toM3 κ⁻¹ := by
  have h : (MulAut.conj κ g)⁻¹ = MulAut.conj κ (g⁻¹) :=
    (map_inv (MulAut.conj κ).toMonoidHom g).symm
  rw [h, toM3_conj]

private theorem toM3_conj_k_c1 : toM3 (MulAut.conj kU c1U) = conjKC1M := by
  rw [toM3_conj, toM3_k, toM3_c1, toM3_k_inv]
  ext <;> decide

private theorem toM3_conj_k_c2 : toM3 (MulAut.conj kU c2U) = conjKC2M := by
  rw [toM3_conj, toM3_k, toM3_c2, toM3_k_inv]
  ext <;> decide

private theorem toM3_conj_k_c2_inv : toM3 ((MulAut.conj kU c2U)⁻¹) = conjKC2InvM := by
  rw [toM3_conj_inv, toM3_k, toM3_c2_inv, toM3_k_inv]
  ext <;> decide

private theorem toM3_conj_k'_c1 : toM3 (MulAut.conj k'U c1U) = conjK'C1M := by
  rw [toM3_conj, toM3_k', toM3_c1, toM3_k'_inv]
  ext <;> decide

private theorem toM3_conj_k'_c2_inv : toM3 ((MulAut.conj k'U c2U)⁻¹) = conjK'C2InvM := by
  rw [toM3_conj_inv, toM3_k', toM3_c2_inv, toM3_k'_inv]
  ext <;> decide

private theorem hk_k : kU * (β₀ kU)⁻¹ = β₀ (w ^ 2) := by
  apply toM3_injective
  rw [toM3_mul, ← map_inv β₀ kU]
  conv_lhs => rw [toM3_suField, toM3_k_inv, toM3_k]
  conv_rhs => rw [toM3_suField, toM3_w2]
  ext <;> decide

private theorem hk_k' : k'U * (β₀ k'U)⁻¹ = β₀ (w' ^ 2) := by
  apply toM3_injective
  rw [toM3_mul, ← map_inv β₀ k'U]
  conv_lhs => rw [toM3_suField, toM3_k'_inv, toM3_k']
  conv_rhs => rw [toM3_suField, toM3_w'2]
  ext <;> decide

private theorem hgen_k :
    autFixed β₀ ⊔ (autFixed β₀).map (MulAut.conj kU).toMonoidHom = ⊤ := by
  let H : Subgroup (unitarySU 2 2 GF16 3) :=
    autFixed β₀ ⊔ (autFixed β₀).map (MulAut.conj kU).toMonoidHom
  change H = ⊤
  let X1 : unitarySU 2 2 GF16 3 := c1U
  let X2 : unitarySU 2 2 GF16 3 := c2U
  let X3 : unitarySU 2 2 GF16 3 := MulAut.conj kU c1U
  let X4 : unitarySU 2 2 GF16 3 := MulAut.conj kU c2U
  have hX1 : X1 ∈ H := Subgroup.mem_sup_left c1_mem_autFixed
  have hX2 : X2 ∈ H := Subgroup.mem_sup_left c2_mem_autFixed
  have hX3 : X3 ∈ H := Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ c1_mem_autFixed)
  have hX4 : X4 ∈ H := Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ c2_mem_autFixed)
  have hX4i : X4⁻¹ ∈ H := Subgroup.inv_mem H hX4
  have hT3 : toM3 X3 = conjKC1M := toM3_conj_k_c1
  have hT4 : toM3 X4 = conjKC2M := toM3_conj_k_c2
  have hT4i : toM3 X4⁻¹ = conjKC2InvM := toM3_conj_k_c2_inv
  have hword1 : X2 * X3 * X1 * X4 * X4 * X2 * X4 ∈ H :=
    Subgroup.mul_mem H
      (Subgroup.mul_mem H
        (Subgroup.mul_mem H
          (Subgroup.mul_mem H
            (Subgroup.mul_mem H (Subgroup.mul_mem H hX2 hX3) hX1) hX4) hX4) hX2) hX4
  have hword2 : X1 * X4⁻¹ * X1 ∈ H :=
    Subgroup.mul_mem H (Subgroup.mul_mem H hX1 hX4i) hX1
  refine eq_top_of_toM3 ⟨X2 * X3 * X1 * X4 * X4 * X2 * X4, hword1, ?_⟩
    ⟨X1 * X4⁻¹ * X1, hword2, ?_⟩
  · rw [toM3_mul, toM3_mul, toM3_mul, toM3_mul, toM3_mul, toM3_mul, hT3, hT4,
      toM3_c1, toM3_c2]
    ext <;> decide
  · rw [toM3_mul, toM3_mul, toM3_c1, hT4i]
    ext <;> decide

private theorem hgen_k' :
    autFixed β₀ ⊔ (autFixed β₀).map (MulAut.conj k'U).toMonoidHom = ⊤ := by
  let H : Subgroup (unitarySU 2 2 GF16 3) :=
    autFixed β₀ ⊔ (autFixed β₀).map (MulAut.conj k'U).toMonoidHom
  change H = ⊤
  let X1 : unitarySU 2 2 GF16 3 := c1U
  let X2 : unitarySU 2 2 GF16 3 := c2U
  let X3 : unitarySU 2 2 GF16 3 := MulAut.conj k'U c1U
  let X4 : unitarySU 2 2 GF16 3 := MulAut.conj k'U c2U
  let Y : unitarySU 2 2 GF16 3 := X3 * X4⁻¹
  have hX1 : X1 ∈ H := Subgroup.mem_sup_left c1_mem_autFixed
  have hX2 : X2 ∈ H := Subgroup.mem_sup_left c2_mem_autFixed
  have hX2i : X2⁻¹ ∈ H := Subgroup.inv_mem H hX2
  have hX3 : X3 ∈ H := Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ c1_mem_autFixed)
  have hX4 : X4 ∈ H := Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ c2_mem_autFixed)
  have hX4i : X4⁻¹ ∈ H := Subgroup.inv_mem H hX4
  have hY : Y ∈ H := by
    change X3 * X4⁻¹ ∈ H
    exact Subgroup.mul_mem H hX3 hX4i
  have hT3 : toM3 X3 = conjK'C1M := toM3_conj_k'_c1
  have hT4i : toM3 X4⁻¹ = conjK'C2InvM := toM3_conj_k'_c2_inv
  have hTY : toM3 Y = conjK'C1M * conjK'C2InvM := by
    change toM3 (X3 * X4⁻¹) = conjK'C1M * conjK'C2InvM
    rw [toM3_mul, hT3, hT4i]
  have hword1 : X2⁻¹ * Y * Y * X2 ∈ H :=
    Subgroup.mul_mem H (Subgroup.mul_mem H (Subgroup.mul_mem H hX2i hY) hY) hX2
  have hword2 : X1 * X2 * X3 * X4⁻¹ * X3 * X2⁻¹ * X1 ∈ H :=
    Subgroup.mul_mem H
      (Subgroup.mul_mem H
        (Subgroup.mul_mem H
          (Subgroup.mul_mem H
            (Subgroup.mul_mem H
              (Subgroup.mul_mem H hX1 hX2) hX3) hX4i) hX3) hX2i) hX1
  refine eq_top_of_toM3 ⟨X2⁻¹ * Y * Y * X2, hword1, ?_⟩
    ⟨X1 * X2 * X3 * X4⁻¹ * X3 * X2⁻¹ * X1, hword2, ?_⟩
  · rw [toM3_mul, toM3_mul, toM3_mul, toM3_c2_inv, hTY, toM3_c2]
    ext <;> decide
  · rw [toM3_mul, toM3_mul, toM3_mul, toM3_mul, toM3_mul, toM3_mul, toM3_c1, toM3_c2,
      hT3, hT4i, toM3_c2_inv]
    ext <;> decide

theorem exists_fourGenWith :
    ∃ x : unitarySU 2 2 GF16 3,
      orderOf (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv *
        (MulAut.conj x * suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv *
          (MulAut.conj x)⁻¹)) = 4 ∧
      FourGenWith (autFixed (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv))
        (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv) x ∧
      FourGenWith (autFixed (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv))
        (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv) x⁻¹ := by
  have hker : (MulAut.conj : unitarySU 2 2 GF16 3 →* MulAut (unitarySU 2 2 GF16 3)).ker =
      ⊥ := by
    rw [CFSG.GroupTheory.ker_conj_eq_center, center_eq_bot]
  have hinj : Function.Injective
      (MulAut.conj : unitarySU 2 2 GF16 3 →* MulAut (unitarySU 2 2 GF16 3)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hk : kU * (β₀ kU)⁻¹ =
      β₀ ((β₀ xU * xU⁻¹) ^ (orderOf (β₀ xU * xU⁻¹) / 2)) := by
    rw [show β₀ xU * xU⁻¹ = w from rfl, orderOf_w, show 4 / 2 = 2 by norm_num]
    exact hk_k
  have hk' : k'U * (β₀ k'U)⁻¹ =
      β₀ ((β₀ (xU⁻¹) * (xU⁻¹)⁻¹) ^ (orderOf (β₀ (xU⁻¹) * (xU⁻¹)⁻¹) / 2)) := by
    rw [show β₀ (xU⁻¹) * (xU⁻¹)⁻¹ = w' from rfl, orderOf_w',
      show 4 / 2 = 2 by norm_num]
    exact hk_k'
  refine ⟨xU, ?_, ?_, ?_⟩
  · have hconj : β₀ * (MulAut.conj xU * β₀ * (MulAut.conj xU)⁻¹) = MulAut.conj w :=
      mul_conj_mul_conj_inv suField_mul_self xU
    rw [hconj]
    exact (orderOf_injective (MulAut.conj : unitarySU 2 2 GF16 3 →* _) hinj w).trans orderOf_w
  · exact fourGenWith_of center_eq_bot suField_mul_self hk hgen_k
  · exact fourGenWith_of center_eq_bot suField_mul_self hk' hgen_k'

end CFSG.LocalAnalysis.WeakClosure81.Asch6.U34

end
