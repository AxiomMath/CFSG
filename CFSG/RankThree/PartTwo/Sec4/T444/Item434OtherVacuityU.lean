module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OtherVacuity
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix

@[expose] def uQ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 1, 1, 1; 0, 1, 1]

@[expose] def uQi : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 1, 0; 1, 1, 1]

theorem uQ_mul_uQi : uQ * uQi = 1 := by decide

theorem uQi_mul_uQ : uQi * uQ = 1 := by decide

theorem uQ_transpose_mul_uQ : uQᵀ * uQ = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by decide

section Lift

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def uCast : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

theorem uCast_fixed (bar : K →+* K) : bar.comp uCast = uCast :=
  RingHom.ext_zmod _ _

@[expose] noncomputable def uQK : Matrix (Fin 3) (Fin 3) K := uQ.map uCast

@[expose] noncomputable def uQiK : Matrix (Fin 3) (Fin 3) K := uQi.map uCast

theorem uQK_mul_uQiK : (uQK : Matrix (Fin 3) (Fin 3) K) * uQiK = 1 := by
  rw [uQK, uQiK, ← Matrix.map_mul, uQ_mul_uQi, Matrix.map_one uCast (map_zero uCast) (map_one uCast)]

theorem uQiK_mul_uQK : (uQiK : Matrix (Fin 3) (Fin 3) K) * uQK = 1 := by
  rw [uQK, uQiK, ← Matrix.map_mul, uQi_mul_uQ, Matrix.map_one uCast (map_zero uCast) (map_one uCast)]

theorem uQK_transpose_mul :
    uQKᵀ * uQK = (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  rw [uQK, ← Matrix.transpose_map, ← Matrix.map_mul, uQ_transpose_mul_uQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Lift

section Order9

variable {K : Type} [Field K] [Finite K]

theorem exists_unit_orderOf_nine (hK : Nat.card K = 2 ^ 12) : ∃ α : Kˣ, orderOf α = 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = 4095 := by
    rw [Nat.card_units, hK]
    norm_num
  refine ⟨g ^ 455, ?_⟩
  have hdvd : (455 : ℕ) ∣ orderOf g := by
    rw [hg, hcard]
    norm_num
  rw [orderOf_pow_of_dvd (by norm_num) hdvd, hg, hcard]

theorem pow_nine_eq_one_of_orderOf {α : Kˣ} (hα : orderOf α = 9) : (α : K) ^ 9 = 1 := by
  have h9 : α ^ 9 = 1 := hα ▸ pow_orderOf_eq_one α
  have := congrArg Units.val h9
  simpa [Units.val_pow_eq_pow_val] using this

theorem pow_three_ne_one_of_orderOf {α : Kˣ} (hα : orderOf α = 9) : (α : K) ^ 3 ≠ 1 := by
  intro h3
  have hu : α ^ 3 = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h3)
  have hd := orderOf_dvd_of_pow_eq_one hu
  rw [hα] at hd
  norm_num at hd

end Order9

section Unitary9

variable {K : Type} [Field K] [CharP K 2]

@[expose] def uDiag (a : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![a, a ^ 4031, 1]

@[expose] def uDiagInv (a : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![a⁻¹, (a⁻¹) ^ 4031, 1]

theorem uDiag_mul_uDiagInv {a : K} (ha : a ≠ 0) : uDiag a * uDiagInv a = 1 := by
  rw [uDiag, uDiagInv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha, ← mul_pow]

theorem uDiagInv_mul_uDiag {a : K} (ha : a ≠ 0) : uDiagInv a * uDiag a = 1 := by
  rw [uDiag, uDiagInv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha, ← mul_pow]

@[expose] noncomputable def uQu : GL (Fin 3) K := ⟨uQK, uQiK, uQK_mul_uQiK, uQiK_mul_uQK⟩

@[expose] noncomputable def uDu {a : K} (ha : a ≠ 0) : GL (Fin 3) K :=
  ⟨uDiag a, uDiagInv a, uDiag_mul_uDiagInv ha, uDiagInv_mul_uDiag ha⟩

@[expose] noncomputable def uMu {a : K} (ha : a ≠ 0) : GL (Fin 3) K := uQu * uDu ha * uQu⁻¹

theorem uMu_val {a : K} (ha : a ≠ 0) :
    ((uMu ha : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uQK * uDiag a * uQiK := by
  simp [uMu, uQu, uDu, Units.val_mul]

theorem uDiag_J_uDiag {a b : K} (h1 : b * a ^ 4031 = 1) (h2 : b ^ 4031 * a = 1) :
    (uDiag b)ᵀ * (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * uDiag a =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uDiag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, h1, h2]

end Unitary9

section Twist

variable {K : Type} [Field K] [CharP K 2]

theorem map_uQK (bar : K →+* K) : (uQK : Matrix (Fin 3) (Fin 3) K).map bar = uQK := by
  rw [uQK, Matrix.map_map, ← RingHom.coe_comp, uCast_fixed]

theorem map_uQiK (bar : K →+* K) : (uQiK : Matrix (Fin 3) (Fin 3) K).map bar = uQiK := by
  rw [uQiK, Matrix.map_map, ← RingHom.coe_comp, uCast_fixed]

theorem map_uDiag (bar : K →+* K) (a : K) :
    (uDiag a : Matrix (Fin 3) (Fin 3) K).map bar = uDiag (bar a) := by
  unfold uDiag
  rw [Matrix.diagonal_map (map_zero bar)]
  congr 1
  funext i
  fin_cases i <;> simp [map_pow]

theorem map_uQDQi (bar : K →+* K) (a : K) :
    (uQK * uDiag a * uQiK : Matrix (Fin 3) (Fin 3) K).map bar = uQK * uDiag (bar a) * uQiK := by
  rw [Matrix.map_mul, Matrix.map_mul, map_uQK, map_uDiag, map_uQiK]

theorem uQDQi_transpose_mul {a b : K} (h1 : b * a ^ 4031 = 1) (h2 : b ^ 4031 * a = 1) :
    (uQK * uDiag b * uQiK : Matrix (Fin 3) (Fin 3) K)ᵀ * (uQK * uDiag a * uQiK) = 1 := by
  have hJ : (uDiag b)ᵀ * (uQKᵀ * uQK) * uDiag a =
      (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
    rw [uQK_transpose_mul]
    exact uDiag_J_uDiag h1 h2
  have hfin : (uQiK : Matrix (Fin 3) (Fin 3) K)ᵀ * ((uQK : Matrix (Fin 3) (Fin 3) K)ᵀ * uQK) *
      uQiK = 1 := by
    have e : (uQiK : Matrix (Fin 3) (Fin 3) K)ᵀ * ((uQK : Matrix (Fin 3) (Fin 3) K)ᵀ * uQK) *
        uQiK = (uQK * uQiK)ᵀ * (uQK * uQiK) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, uQK_mul_uQiK, Matrix.transpose_one, Matrix.one_mul]
  have e2 : (uQK * uDiag b * uQiK : Matrix (Fin 3) (Fin 3) K)ᵀ * (uQK * uDiag a * uQiK) =
      uQiKᵀ * ((uDiag b)ᵀ * (uQKᵀ * uQK) * uDiag a) * uQiK := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e2, hJ, ← uQK_transpose_mul, hfin]

end Twist

section TwistGL

variable {K : Type} [Field K] [CharP K 2]

theorem bar_eq_pow_sixtyfour (h : UnitaryFieldData 2 6 K) (c : K) : h.bar c = c ^ 64 := by
  rw [h.bar_apply]
  norm_num

theorem uMu_mem (h : UnitaryFieldData 2 6 K) {a : K} (ha : a ≠ 0) (h9 : a ^ 9 = 1) :
    uMu ha ∈ unitaryIsom3 h := by
  have h1 : a ^ 64 * a ^ 4031 = 1 := by
    rw [← pow_add, show 64 + 4031 = 9 * 455 by norm_num, pow_mul, h9, one_pow]
  have h2 : (a ^ 64) ^ 4031 * a = 1 := by
    rw [← pow_mul, mul_comm, ← pow_succ', show 64 * 4031 + 1 = 9 * 28665 by norm_num,
      pow_mul, h9, one_pow]
  rw [mem_unitaryIsom3, uMu_val, map_uQDQi, bar_eq_pow_sixtyfour h]
  exact uQDQi_transpose_mul h1 h2

theorem uDiag_pow_nine {a : K} (h9 : a ^ 9 = 1) : uDiag a ^ 9 = 1 := by
  have h9' : (a ^ 4031) ^ 9 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h9, one_pow]
  unfold uDiag
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [h9, h9']

theorem uMu_pow_nine {a : K} (ha : a ≠ 0) (h9 : a ^ 9 = 1) : uMu ha ^ 9 = 1 := by
  have hD : uDu ha ^ 9 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact uDiag_pow_nine h9)
  rw [uMu, conj_pow, hD, mul_one, mul_inv_cancel]

end TwistGL

section Order9Element

variable {K : Type} [Field K] [CharP K 2]

theorem uMu_pow_three_val {a : K} (ha : a ≠ 0) :
    ((uMu ha ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uQK * (uDiag a) ^ 3 * uQiK := by
  rw [uMu, conj_pow, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

theorem uDiag_pow_three (a : K) :
    uDiag a ^ 3 = Matrix.diagonal ![a ^ 3, (a ^ 4031) ^ 3, 1] := by
  unfold uDiag
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem uQDQi_apply_zero_one (x y z : K) :
    (uQK * Matrix.diagonal ![x, y, z] * uQiK : Matrix (Fin 3) (Fin 3) K) 0 1 = x + z := by
  simp [uQK, uQiK, uQ, uQi, uCast, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem uMu_pow_three_ne_scalar {a : K} (ha : a ≠ 0) (h3 : a ^ 3 ≠ 1) (c : Kˣ) :
    (uMu ha ^ 3 : GL (Fin 3) K) ≠ GeneralLinearGroup.scalar (Fin 3) c := by
  intro hc
  have hm : ((uMu ha ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 =
      ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 := by
    rw [hc]
  have hs : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [uMu_pow_three_val, uDiag_pow_three, uQDQi_apply_zero_one, hs] at hm
  apply h3
  linear_combination hm - h2

theorem orderOf_psuConj_uMu (hU : UnitaryFieldData 2 6 K) {a : K} (ha : a ≠ 0) (h9 : a ^ 9 = 1)
    (h3 : a ^ 3 ≠ 1) : orderOf (psuConj hU ⟨uMu ha, uMu_mem hU ha h9⟩) = 9 := by
  have hpow9 : (⟨uMu ha, uMu_mem hU ha h9⟩ : unitaryIsom3 hU) ^ 9 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact uMu_pow_nine ha h9)
  have hnot : ¬ (psuConj hU ⟨uMu ha, uMu_mem hU ha h9⟩) ^ 3 ^ 1 = 1 := by
    intro h1
    rw [pow_one, ← map_pow] at h1
    have h2 : psuConj hU (⟨uMu ha, uMu_mem hU ha h9⟩ ^ 3) * psuField hU 1 = 1 := by
      rw [map_one, mul_one]
      exact h1
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ 1 h2
    apply uMu_pow_three_ne_scalar ha h3 c
    rw [Subgroup.coe_pow] at hc
    exact hc
  have hfin : (psuConj hU ⟨uMu ha, uMu_mem hU ha h9⟩) ^ 3 ^ (1 + 1) = 1 := by
    rw [show (3 : ℕ) ^ (1 + 1) = 9 by norm_num, ← map_pow, hpow9, map_one]
  exact (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)

end Order9Element

section SUInj

variable {K : Type} [Field K] [CharP K 2]

theorem unit_eq_one_of_pow_three {c : Kˣ} (h3 : c ^ 3 = 1) (h65 : c ^ 65 = 1) : c = 1 := by
  have h : c ^ Nat.gcd 3 65 = 1 := pow_gcd_eq_one.2 ⟨h3, h65⟩
  rw [show Nat.gcd 3 65 = 1 by norm_num, pow_one] at h
  exact h

theorem det_scalar_val (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]

theorem su_eq_one_of_psuConj_eq_one (hU : UnitaryFieldData 2 6 K) (x : unitarySU 2 6 K 3)
    (hx : psuConj hU ⟨(x : GL (Fin 3) K), unitarySU_le_unitaryIsom3 (h := hU) x.2⟩ = 1) : x = 1 := by
  have h2 : psuConj hU ⟨(x : GL (Fin 3) K), unitarySU_le_unitaryIsom3 (h := hU) x.2⟩ *
      psuField hU 1 = 1 := by
    rw [map_one, mul_one]
    exact hx
  obtain ⟨-, c, hn, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ 1 h2
  have hc' : (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := hc
  have hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_unitarySU_iff hU).1 x.2).1
  rw [hc', det_scalar_val] at hdet
  have hn' : (c : K) ^ 65 = 1 := by
    rw [UnitaryFieldData.norm_eq_pow] at hn
    norm_num at hn
    exact hn
  have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
  have hc65 : c ^ 65 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hn')
  have hc1 : c = 1 := unit_eq_one_of_pow_three hc3 hc65
  apply Subtype.ext
  rw [hc', hc1, map_one, Subgroup.coe_one]

@[expose] noncomputable def psuConjSU (hU : UnitaryFieldData 2 6 K) :
    unitarySU 2 6 K 3 →* MulAut (unitaryPSU hU 3) :=
  (psuConj hU).comp (Subgroup.inclusion (unitarySU_le_unitaryIsom3 (h := hU)))

theorem psuConjSU_apply (hU : UnitaryFieldData 2 6 K) (x : unitarySU 2 6 K 3) :
    psuConjSU hU x = psuConj hU ⟨(x : GL (Fin 3) K), unitarySU_le_unitaryIsom3 (h := hU) x.2⟩ := rfl

theorem psuConjSU_injective (hU : UnitaryFieldData 2 6 K) : Function.Injective (psuConjSU hU) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact su_eq_one_of_psuConj_eq_one hU x ((psuConjSU_apply hU x).symm.trans hx)

end SUInj

section Surj

variable {K : Type} [Field K] [CharP K 2]

theorem exists_cube_unit {δ : Kˣ} (hδ : δ ^ 65 = 1) :
    ∃ c : Kˣ, c ^ 3 * δ = 1 ∧ c ^ 65 = 1 := by
  refine ⟨(δ ^ 22)⁻¹, ?_, ?_⟩
  · have h66 : δ ^ 66 = δ := by
      rw [show (66 : ℕ) = 65 + 1 from rfl, pow_succ, hδ, one_mul]
    rw [inv_pow, ← pow_mul, show 22 * 3 = 66 by norm_num, h66, inv_mul_cancel]
  · rw [inv_pow, ← pow_mul, pow_mul', hδ, one_pow, inv_one]

theorem exists_psuConjSU_eq (hU : UnitaryFieldData 2 6 K) {A : GL (Fin 3) K}
    (hA : A ∈ unitaryIsom3 hU) :
    ∃ x : unitarySU 2 6 K 3, psuConjSU hU x = psuConj hU ⟨A, hA⟩ := by
  have hδ : GeneralLinearGroup.det A ^ 65 = 1 := by
    simpa using det_pow_succ_eq_one_of_mem_unitaryIsom3 hU hA
  obtain ⟨c, hc3, hc65⟩ := exists_cube_unit hδ
  have hK : (c : K) ^ 65 = 1 := by rw [← Units.val_pow_eq_pow_val, hc65, Units.val_one]
  have hnorm : hU.norm (c : K) = 1 := by
    rw [UnitaryFieldData.norm_eq_pow]
    simpa using hK
  have hs : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 hU :=
    scalar_mem_unitaryIsom3_of_norm (h := hU) hnorm
  have hBU : GeneralLinearGroup.scalar (Fin 3) c * A ∈ unitaryIsom3 hU := mul_mem hs hA
  have hdet : ((GeneralLinearGroup.scalar (Fin 3) c * A : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, det_scalar_val]
    have h1 := congrArg Units.val hc3
    rw [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply,
      Units.val_one] at h1
    exact h1
  have hBSU : GeneralLinearGroup.scalar (Fin 3) c * A ∈ unitarySU 2 6 K 3 :=
    (mem_unitarySU_iff hU).2 ⟨hdet, (mem_unitaryIsom3 (h := hU)).1 hBU⟩
  refine ⟨⟨_, hBSU⟩, ?_⟩
  rw [psuConjSU_apply]
  have hfac : psuConj hU ⟨GeneralLinearGroup.scalar (Fin 3) c * A, hBU⟩ =
      psuConj hU ⟨A, hA⟩ := by
    rw [show (⟨GeneralLinearGroup.scalar (Fin 3) c * A, hBU⟩ : unitaryIsom3 hU) =
      ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ * ⟨A, hA⟩ from rfl, map_mul,
      psuConj_eq_one_of_coe_eq_scalar (h := hU) (A := ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩)
        (c := c) rfl, one_mul]
  exact hfac

theorem range_psuConj_eq (hU : UnitaryFieldData 2 6 K) :
    (psuConj hU).range = (psuConjSU hU).range := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    obtain ⟨x, hx⟩ := exists_psuConjSU_eq hU A.2
    exact ⟨x, hx⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, unitarySU_le_unitaryIsom3 (h := hU) x.2⟩, (psuConjSU_apply hU x).symm⟩

theorem card_psuConj_range (hU : UnitaryFieldData 2 6 K) :
    Nat.card (psuConj hU).range = 9 * (262144 * 455 * 262145) := by
  rw [range_psuConj_eq hU,
    Nat.card_congr (MonoidHom.ofInjective (psuConjSU_injective hU)).toEquiv.symm,
    card_unitarySU_three hU]
  norm_num

theorem not_three_dvd_m : ¬ 3 ∣ 262144 * 455 * 262145 := by norm_num

end Surj

section Sylow

variable {K : Type} [Field K] [CharP K 2]

theorem card_field_eq_two_pow_twelve (hU : UnitaryFieldData 2 6 K) : Nat.card K = 2 ^ 12 :=
  hU.card.trans (by norm_num)

theorem uFiniteMulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G))
    (fun _ _ hfg => MulEquiv.ext (fun x => congrFun hfg x))

theorem finite_mulAut_unitaryPSU (hU : UnitaryFieldData 2 6 K) :
    Finite (MulAut (unitaryPSU hU 3)) := by
  haveI : Finite (unitarySU 2 6 K 3) :=
    Nat.finite_of_card_ne_zero (by rw [card_unitarySU_three hU]; norm_num)
  haveI : Finite (unitaryPSU hU 3) := Quotient.finite _
  exact uFiniteMulAut _

theorem card_inf_psuConj_le_three (hU : UnitaryFieldData 2 6 K)
    {B : Subgroup (MulAut (unitaryPSU hU 3))} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card (B ⊓ (psuConj hU).range : Subgroup (MulAut (unitaryPSU hU 3))) ≤ 3 := by
  haveI := finite_mulAut_unitaryPSU hU
  haveI := hU.finite
  obtain ⟨α, hα⟩ := exists_unit_orderOf_nine (card_field_eq_two_pow_twelve hU)
  have ha : (α : K) ≠ 0 := Units.ne_zero α
  have h9 : (α : K) ^ 9 = 1 := pow_nine_eq_one_of_orderOf hα
  have h3 : (α : K) ^ 3 ≠ 1 := pow_three_ne_one_of_orderOf hα
  have hmem : psuConj hU ⟨uMu ha, uMu_mem hU ha h9⟩ ∈ (psuConj hU).range :=
    MonoidHom.mem_range.2 ⟨_, rfl⟩
  let g : (psuConj hU).range := ⟨_, hmem⟩
  have hg : orderOf g = 9 :=
    (Subgroup.orderOf_coe g).symm.trans (orderOf_psuConj_uMu hU ha h9 h3)
  have hE : ∀ x ∈ (B ⊓ (psuConj hU).range).subgroupOf (psuConj hU).range, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1
  have hcard : Nat.card ((B ⊓ (psuConj hU).range).subgroupOf (psuConj hU).range) =
      Nat.card (B ⊓ (psuConj hU).range : Subgroup (MulAut (unitaryPSU hU 3))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show B ⊓ (psuConj hU).range ≤ (psuConj hU).range from inf_le_right)).toEquiv
  rw [← hcard]
  exact card_le_three_of_exp_three_of_nine (card_psuConj_range hU) not_three_dvd_m g hg hE

end Sylow

section Final

variable {K : Type} [Field K] [CharP K 2]

theorem card_le_nine_mulAut_psuPSU (hU : UnitaryFieldData 2 6 K)
    (B : Subgroup (MulAut (unitaryPSU hU 3))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  haveI := finite_mulAut_unitaryPSU hU
  haveI := hU.finite
  have hK : Nat.card K = 2 ^ 12 := card_field_eq_two_pow_twelve hU
  haveI : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic Nat.prime_two K hK).2
  have hcyc : IsCyclic (psuField hU).range :=
    isCyclic_of_surjective (psuField hU).rangeRestrict (psuField hU).rangeRestrict_surjective
  have hfwd : ∀ (σ : K ≃+* K) (x : MulAut (unitaryPSU hU 3)), x ∈ (psuConj hU).range →
      psuField hU σ * x * (psuField hU σ)⁻¹ ∈ (psuConj hU).range := by
    intro σ x hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [psuField_mul_psuConj_mul_inv (h := hU)]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  have hCN : (psuField hU).range ≤
      Subgroup.normalizer (((psuConj hU).range : Subgroup (MulAut (unitaryPSU hU 3))) :
        Set (MulAut (unitaryPSU hU 3))) := by
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hfwd σ n hn
    · intro hn
      have e : psuField hU σ⁻¹ * (psuField hU σ * n * (psuField hU σ)⁻¹) *
          (psuField hU σ⁻¹)⁻¹ = n := by
        rw [map_inv]
        group
      have h' := hfwd σ⁻¹ (psuField hU σ * n * (psuField hU σ)⁻¹) hn
      rw [e] at h'
      exact h'
  have hBNC : ∀ b ∈ B, ∃ n ∈ (psuConj hU).range, ∃ c ∈ (psuField hU).range, b = n * c := by
    intro b _
    obtain ⟨A, σ, hb⟩ := exists_psuConj_mul_psuField (h := hU) (by norm_num) b
    exact ⟨psuConj hU A, MonoidHom.mem_range.2 ⟨A, rfl⟩, psuField hU σ,
      MonoidHom.mem_range.2 ⟨σ, rfl⟩, hb⟩
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  have h2 := card_inf_psuConj_le_three hU hB
  omega

end Final

theorem pRank_three_mulAut_projSU_three_sixtyFour_le_two :
    CFSG.pRank 3 (MulAut (projSU 3 2 6)) ≤ 2 := by
  have hU : UnitaryFieldData 2 6 (GaloisField 2 (2 * 6)) :=
    unitaryFieldData_galoisField 2 6 (by norm_num)
  exact vacPRank_le_two_of_card_le
    (vacCard_le_nine_of_mulEquiv (projSUEquivUnitaryPSU 2 6 hU) (card_le_nine_mulAut_psuPSU hU))

end CFSG.RankThree.PartTwo.Sec4
