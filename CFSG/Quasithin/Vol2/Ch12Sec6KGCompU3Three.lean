module

import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompDescend
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompL3Small

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LinearGroups.UnitaryThreeOverNine Matrix

variable {F : Type} [Field F]

theorem card_centralizer_su33 (hF : Nat.card F = 9) {a : ↥(StatedSU 3 3 F)}
    (ha : orderOf a = 2) :
    Nat.card (Subgroup.centralizer ({a} : Set ↥(StatedSU 3 3 F))) = 96 := by
  have h := unitaryFieldData_of_card hF
  have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
    rw [gramForm_e0_left]
    exact one_ne_zero
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two hF ha
    (tauLine h hF (lineOf _ hv)).2)
  rw [← card_centralizer_tauLine (h := h) (hF := hF) (L₀ := lineOf _ hv) rfl, ← hc]
  refine Nat.card_congr
    { toFun := fun x => ⟨c * x * c⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      invFun := fun y => ⟨c⁻¹ * y * c, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    calc c * x * c⁻¹ * (c * a * c⁻¹) = c * (x * a) * c⁻¹ := by group
      _ = c * (a * x) * c⁻¹ := by rw [hx]
      _ = c * a * c⁻¹ * (c * x * c⁻¹) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    calc c⁻¹ * y * c * a = c⁻¹ * (y * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹ * y) * c := by rw [hy]
      _ = a * (c⁻¹ * y * c) := by group

omit [Field F] in
theorem charP_three_of_card_nine [Field F] (hF : Nat.card F = 9) : CharP F 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem exists_elemAbelian_nine_su33 (hF : Nat.card F = 9) :
    ∃ E : Subgroup ↥(StatedSU 3 3 F), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : CharP F 3 := charP_three_of_card_nine hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hF
  set ζ : F := ((i : Fˣ) : F) with hζdef
  have hζ : ζ ^ 2 = -1 := sq_eq_neg_one_of_orderOf hi
  have hζ0 : ζ ≠ 0 := i.ne_zero
  have hw : (fun _ : Fin 3 => (1 : F)) ⬝ᵥ (fun _ => ζ) = 0 := by
    simp only [dotProduct, Fin.sum_univ_three, one_mul]
    linear_combination ζ * h3
  set Z := rankOneSL (fun _ => ζ) (fun _ => (1 : F)) hw with hZdef
  have hZm : (Z : Matrix (Fin 3) (Fin 3) F) = !![1 + ζ, ζ, ζ; ζ, 1 + ζ, ζ; ζ, ζ, 1 + ζ] := by
    rw [hZdef, coe_rankOneSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [vecMulVec_apply]
  set P : Matrix.SpecialLinearGroup (Fin 3) F := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    simp [Matrix.det_fin_three]⟩ with hPdef
  have hmem : ∀ A : Matrix.SpecialLinearGroup (Fin 3) F,
      ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 →
      Matrix.SpecialLinearGroup.toGL A ∈ StatedSU 3 3 F := fun A hA =>
    Subgroup.subset_closure ⟨A.2, hA⟩
  have hZu : ((Z : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * (Z : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    have hc : (1 + ζ) ^ 3 = 1 - ζ := by
      rw [add_pow_char, one_pow]
      linear_combination ζ * hζ
    have hc' : ζ ^ 3 = -ζ := by linear_combination ζ * hζ
    rw [hZm]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hc, hc'] <;>
      linear_combination (-ζ ^ 2) * h3
  have hPu : ((P : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * (P : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hPdef, Matrix.mul_apply, Fin.sum_univ_three]
  set a : ↥(StatedSU 3 3 F) := ⟨_, hmem P hPu⟩ with ha
  set b : ↥(StatedSU 3 3 F) := ⟨_, hmem Z hZu⟩ with hb
  have hcoe : ∀ x : ↥(StatedSU 3 3 F), ∀ n : ℕ,
      (((x ^ n : ↥(StatedSU 3 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) ^ n := fun x n => by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hext : ∀ x y : ↥(StatedSU 3 3 F), (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      (((y : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) → x = y := fun x y hxy =>
    Subtype.ext (Units.ext hxy)
  have haM : (((a : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl
  have hbM : (((b : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      !![1 + ζ, ζ, ζ; ζ, 1 + ζ, ζ; ζ, ζ, 1 + ζ] := hZm
  have hbpow : ∀ n : ℕ,
      (((b ^ n : ↥(StatedSU 3 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![1 + n * ζ, n * ζ, n * ζ; n * ζ, 1 + n * ζ, n * ζ; n * ζ, n * ζ, 1 + n * ζ] := fun n => by
    have h1 : (((b ^ n : ↥(StatedSU 3 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((Z ^ n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hcoe, Matrix.SpecialLinearGroup.coe_pow]
      rfl
    rw [h1, coe_rankOneSL_pow]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [vecMulVec_apply]
  refine exists_elemAbelian_nine (a := a) (b := b) (hext _ _ ?_) (hext _ _ ?_) (hext _ _ ?_) ?_
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, haM, hbM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hcoe, haM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hbpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h3]
  · intro i j hij
    have hM := congrArg (fun x : ↥(StatedSU 3 3 F) =>
      (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)) hij
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at hM
    rw [hcoe, hbpow, haM, ← Matrix.ext_iff] at hM
    have h2 : (2 : F) ≠ 0 := by
      intro h0
      have : (3 : F) - 2 = 1 := by ring
      rw [h3, h0, sub_zero] at this
      exact zero_ne_one this
    fin_cases i <;> fin_cases j
    · exact ⟨rfl, rfl⟩
    all_goals
      exfalso
      simp [Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_three, pow_succ, hζ0, h2] at hM

theorem unitaryScalars_three_eq_bot (h : UnitaryFieldData 3 1 F) : unitaryScalars h 3 = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (by rw [card_unitaryScalars h (by norm_num)]; norm_num)

theorem nonempty_su33_mulEquiv (hF : Nat.card F = 9) :
    Nonempty (↥(StatedSU 3 3 F) ≃* StatedProj (StatedSU 3 (3 ^ 1) F)) := by
  have h := unitaryFieldData_of_card hF
  have hbot : (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (3 ^ 1) F) = ⊥ := by
    rw [← unitaryScalars_eq h (by norm_num)]
    exact unitaryScalars_three_eq_bot h
  exact ⟨(MulEquiv.subgroupCongr (show StatedSU 3 3 F = StatedSU 3 (3 ^ 1) F by
    rw [pow_one])).trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm))⟩

theorem center_su33_eq_bot (hF : Nat.card F = 9) : Subgroup.center ↥(StatedSU 3 3 F) = ⊥ := by
  have h := unitaryFieldData_of_card hF
  have : Finite F := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, hYZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hq le_rfl (by decide)
  rw [← unitaryScalars_eq h (by norm_num), unitaryScalars_three_eq_bot h] at hYZ
  exact hYZ

theorem mem_range_conj_su33 (hF : Nat.card F = 9) {α : MulAut ↥(StatedSU 3 3 F)}
    (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : ↥(StatedSU 3 3 F) →* MulAut ↥(StatedSU 3 3 F)).range := by
  have h := unitaryFieldData_of_card hF
  have : Finite F := h.finite
  set φ : ↥(StatedSU 3 3 F) ≃* unitaryPSU h 3 :=
    (MulEquiv.subgroupCongr (show StatedSU 3 3 F = StatedSU 3 (3 ^ 1) F by
      rw [pow_one])).trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (unitaryScalars_three_eq_bot h).symm)) with hφ
  set α' := MulAut.congr φ α with hα'def
  have hα' : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, hα, map_one]
  have hin : α' ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    by_cases hD : α' ∈ (CFSG.RankThree.PartTwo.KFacts.psuConj h).range
    · exact CFSG.RankThree.PartTwo.Sec4.psu3_inndiag_cube (h := h) (by norm_num) α' hD hα'
    · exfalso
      obtain ⟨σ, hσ, -⟩ := CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent
        (h := h) (by norm_num) α' hα' hD
      obtain ⟨-, -, -, -, hcard, -⟩ :=
        finite_field_automorphism_fixed_field_cardinality (F := F) Nat.prime_three (n := 2)
          (by norm_num) (by rw [hF]; norm_num)
      have := orderOf_dvd_natCard σ
      rw [hσ, hcard] at this
      norm_num at this
  obtain ⟨y, hy⟩ := hin
  refine ⟨φ.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 := DFunLike.congr_fun hy (φ x)
  rw [MulAut.conj_apply] at h1
  have h2 : α' (φ x) = φ (α x) := by
    rw [hα'def, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1, h2]

theorem not_autConf_su33 (hF : Nat.card F = 9) {ν : MulAut ↥(StatedSU 3 3 F)}
    {Lb Pb : Subgroup (MulAut ↥(StatedSU 3 3 F))} (h : AutConf ↥(StatedSU 3 3 F) ν Lb Pb)
    (h9 : Nat.card Pb = 9) : False := by
  have hU := unitaryFieldData_of_card hF
  have : Finite F := hU.finite
  have hq : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hZ := center_su33_eq_bot hF
  obtain ⟨φ'⟩ := nonempty_su33_mulEquiv hF
  have hm : StatedClassicalModel ↥(StatedSU 3 3 F) .PSU 3 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, F, inferInstance, inferInstance, hq, ⟨φ'⟩⟩
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.oddAutInner_psu3 Nat.prime_three (by norm_num) hm ν
    (apply_apply_of_sq h.sq) h.exists_sylow_fixed
  obtain ⟨hl2, hfix⟩ := h.involution_of_inner hZ hl
  have hinj := conj_injective_of_center_eq_bot hZ
  have hPin : Pb ≤ (MulAut.conj : ↥(StatedSU 3 3 F) →* MulAut ↥(StatedSU 3 3 F)).range :=
    fun π hπ => mem_range_conj_su33 hF (h.elem.2 π hπ)
  have hE9 : Nat.card (Pb.comap
      (MulAut.conj : ↥(StatedSU 3 3 F) →* MulAut ↥(StatedSU 3 3 F))) = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hPin, h9]
  have hEC : Pb.comap (MulAut.conj : ↥(StatedSU 3 3 F) →* MulAut ↥(StatedSU 3 3 F)) ≤
      Subgroup.centralizer ({l} : Set ↥(StatedSU 3 3 F)) := fun e he =>
    (hfix e).mp (h.fix_of_mem_innerPart hZ (h.le he))
  have hdvd := Subgroup.card_dvd_of_le hEC
  rw [hE9, card_centralizer_su33 hF hl2] at hdvd
  norm_num at hdvd

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_su3_three (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hSU : IsSLEps3 false 3 ↥K) : False := by
  have := hQ.finite
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hSU
  have hF : Nat.card F = 9 := by rw [hFc]; norm_num
  obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine_su33 hF
  exact not_autConf_su33 hF (h.autConf.map e) (h.card_map_rhoP_eq_nine hQ e
    (fun z hz => by rw [center_su33_eq_bot hF] at hz; exact hz) hE hE9)

theorem Conf12626.not_psu3_three (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hK : StatedClassicalModel ↥K .PSU 3 3 1) : False := by
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hK
  have hF : Nat.card F = 9 := by rw [hFc]; norm_num
  obtain ⟨φ'⟩ := nonempty_su33_mulEquiv hF
  exact h.not_su3_three hQ ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num,
    ⟨e.trans φ'.symm⟩⟩

end CFSG.Quasithin.H13.S126C
