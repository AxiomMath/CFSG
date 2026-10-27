module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

section Entries

variable {F : Type} [Field F]

private theorem conj_one_zero_of_unip (M u : SL(2, F)) (hu0 : u 0 0 = 1) (hu1 : u 1 1 = 1)
    (hu10 : u 1 0 = 0) : (M * u * M⁻¹) 1 0 = -(M 1 0) ^ 2 * u 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    hu0, hu1, hu10]
  ring

private theorem conj_zero_zero_of_upper (M z : SL(2, F)) (hM : M 1 0 = 0) (hz : z 1 0 = 0) :
    (M * z * M⁻¹) 0 0 = z 0 0 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two, hM] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    hM, hz]
  linear_combination (z 0 0) * hdet

private theorem pow_upper_entries {y : SL(2, F)} (hy : y 1 0 = 0) (k : ℕ) :
    (y ^ k) 1 0 = 0 ∧ (y ^ k) 0 0 = y 0 0 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pow_succ y k, pow_succ (y 0 0) k, Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h1, hy, h2]
    simp

private theorem sq_eq_one_of_unitri [CharP F 2] {u : SL(2, F)} (h00 : u 0 0 = 1)
    (h11 : u 1 1 = 1) (h10 : u 1 0 = 0) : u ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10]
  linear_combination (u 0 1) * CharTwo.two_eq_zero (R := F)

private theorem diag_cube_root_of_upper [CharP F 2] {y : SL(2, F)} (hy : y 1 0 = 0)
    (h3 : orderOf y = 3) : y 0 0 ^ 3 = 1 ∧ y 0 0 ≠ 1 ∧ y 0 0 ≠ y 1 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe y
  rw [Matrix.det_fin_two, hy, mul_zero, sub_zero] at hdet
  have hy3 : y ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one y
  have h1 : y 0 0 ^ 3 = 1 := by
    rw [← (pow_upper_entries hy 3).2, hy3]
    simp
  have h2 : y 0 0 ≠ 1 := by
    intro h
    have h11 : y 1 1 = 1 := by rw [h, one_mul] at hdet; exact hdet
    have := orderOf_dvd_of_pow_eq_one (sq_eq_one_of_unitri h h11 hy)
    rw [h3] at this
    norm_num at this
  refine ⟨h1, h2, fun h => h2 ?_⟩
  rw [← h] at hdet
  have h4 : (y 0 0 + 1) ^ 2 = 0 := by
    linear_combination hdet + (y 0 0 + 1) * CharTwo.two_eq_zero (R := F)
  have h5 : y 0 0 + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h4
  linear_combination h5 - CharTwo.two_eq_zero (R := F)

private theorem eq_one_of_conj_eq_one_sl2 [CharP F 2] {z : SL(2, F)}
    (h : MulAut.conj z = 1) : z = 1 := by
  have hz : z ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : z * g * z⁻¹ = g := by
      simpa [MulAut.conj_apply] using DFunLike.congr_fun h g
    calc g * z = (z * g * z⁻¹) * z := by rw [hg]
      _ = z * g := by group
  rwa [sl2_center_eq_bot, Subgroup.mem_bot] at hz

end Entries

section FieldAut

variable {F : Type} [Field F] [Finite F]

private theorem ringAut_eq_one_of_fix_cube_root {n : ℕ} (hn : n % 4 = 2)
    (hcard : Nat.card F = 2 ^ n) {σ : RingAut F} {a : ℕ} (ha : σ ^ 2 ^ a = 1) {w : F}
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hσw : σ w = w) : σ = 1 := by
  by_contra hne
  have hord : Nat.card (RingAut F) = n := (ringAut_card_and_cyclic hcard).1
  have hσn : σ ^ n = 1 := by rw [← hord]; exact pow_card_eq_one'
  have h2 : σ ^ 2 = 1 := by
    have hd1 : orderOf σ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
    have hd2 : orderOf σ ∣ n := orderOf_dvd_of_pow_eq_one hσn
    obtain ⟨j, -, hjd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    have hj2 : j ≤ 1 := by
      by_contra hj
      have h4 : 2 ^ 2 ∣ n := (pow_dvd_pow 2 (by omega : 2 ≤ j)).trans (hjd ▸ hd2)
      norm_num at h4
      omega
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hjd]
    exact (pow_dvd_pow 2 hj2).trans (by norm_num)
  obtain ⟨s, -, hns, hσc, -⟩ := finite_field_involution_exact (by omega) hcard σ h2 hne
  obtain ⟨i, rfl⟩ : ∃ i, s = 2 * i + 1 := ⟨s / 2, by omega⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hw3
  have h43 : 2 ^ (2 * i + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2' : w ^ 2 ^ (2 * i + 1) = w ^ 2 := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ (2 * i + 1)) 3, h43]
    rw [pow_add, pow_mul, hw3, one_pow, one_mul]
  rw [hσc w] at hσw
  rw [hσw] at h2'
  have h3 : w * (w - 1) = 0 := by linear_combination -h2'
  rcases mul_eq_zero.mp h3 with h | h
  · exact hw0 h
  · exact hw1 (sub_eq_zero.mp h)

private theorem exists_conj_fieldAction {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (α : MulAut SL(2, F)) :
    ∃ M : SL(2, F), ∀ g, α g = M * sl2FieldAction (mulAutToRingAut hcard α) g * M⁻¹ := by
  obtain ⟨a, rfl⟩ := (gammaToMulAut_bijective_of_card hcard).2 α
  refine ⟨a.left, fun g => ?_⟩
  rw [mulAutToRingAut_gammaToMulAut]
  rfl

end FieldAut

section Main

variable {F : Type} [Field F] [Finite F] {n : ℕ}

private theorem eq_one_of_fix_unitri (hn : n % 4 = 2) (hcard : Nat.card F = 2 ^ n)
    (β : MulAut SL(2, F)) {a : ℕ} (ha : β ^ 2 ^ a = 1) {u : SL(2, F)} (hu00 : u 0 0 = 1)
    (hu10 : u 1 0 = 0) (hu1 : u ≠ 1) (hβu : (β u) 1 0 = 0) {y : SL(2, F)}
    (hy3 : orderOf y = 3) (hyu : (y * u * y⁻¹) 1 0 = 0) (hβy : β y = y) : β = 1 := by
  haveI : CharP F 2 := char_two_of_card hcard
  obtain ⟨M, hM⟩ := exists_conj_fieldAction hcard β
  set σ := mulAutToRingAut hcard β with hσdef
  have hσpow : σ ^ 2 ^ a = 1 := by rw [hσdef, ← map_pow, ha, map_one]
  have hent : ∀ (g : SL(2, F)) (i j : Fin 2), sl2FieldAction σ g i j = σ (g i j) :=
    fun _ _ _ => rfl
  have hudet := Matrix.SpecialLinearGroup.det_coe u
  rw [Matrix.det_fin_two, hu00, hu10, one_mul, mul_zero, sub_zero] at hudet
  have hu01 : u 0 1 ≠ 0 := by
    intro h01
    apply hu1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hu00, hu10, hudet, h01]
  have hy10 : y 1 0 = 0 := by
    rw [conj_one_zero_of_unip y u hu00 hudet hu10] at hyu
    have h := (mul_eq_zero.mp hyu).resolve_right hu01
    exact pow_eq_zero_iff two_ne_zero |>.mp (neg_eq_zero.mp h)
  have hM10 : M 1 0 = 0 := by
    have h := hβu
    rw [hM u, conj_one_zero_of_unip M _ (by rw [hent, hu00, map_one])
      (by rw [hent, hudet, map_one]) (by rw [hent, hu10, map_zero]), hent] at h
    have hσ : σ (u 0 1) ≠ 0 := by rwa [map_ne_zero]
    have h' := (mul_eq_zero.mp h).resolve_right hσ
    exact pow_eq_zero_iff two_ne_zero |>.mp (neg_eq_zero.mp h')
  obtain ⟨hw3, hw1, hw11⟩ := diag_cube_root_of_upper hy10 hy3
  have hσw : σ (y 0 0) = y 0 0 := by
    have h : (β y) 0 0 = y 0 0 := by rw [hβy]
    rw [hM y, conj_zero_zero_of_upper M _ hM10 (by rw [hent, hy10, map_zero])] at h
    exact h
  have hσ1 : σ = 1 := ringAut_eq_one_of_fix_cube_root hn hcard hσpow hw3 hw1 hσw
  have hM' : ∀ g, β g = M * g * M⁻¹ := fun g => by
    rw [hM g, hσ1, map_one, MulAut.one_apply]
  have hβconj : β = MulAut.conj M := MulEquiv.ext fun g => by rw [hM' g, MulAut.conj_apply]
  have hM2 : M ^ 2 ^ a = 1 := by
    apply eq_one_of_conj_eq_one_sl2
    rw [map_pow, ← hβconj]
    exact ha
  have hMdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two, hM10, mul_zero, sub_zero] at hMdet
  have hM00 : M 0 0 = 1 := by
    have h1 : M 0 0 ^ 2 ^ a = 1 := by
      rw [← (pow_upper_entries hM10 (2 ^ a)).2, hM2]
      simp
    have hM0 : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hMdet
    have : Fintype F := Fintype.ofFinite F
    have h2 : M 0 0 ^ (Nat.card F - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ hM0
    have hcop : Nat.Coprime (2 ^ a) (Nat.card F - 1) := by
      rw [hcard]
      refine Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ?_)
      have h2n : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨r, hr⟩ := h2n
      exact ⟨r - 1, by omega⟩
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h3
  have hM11 : M 1 1 = 1 := by rw [hM00, one_mul] at hMdet; exact hMdet
  have hMy : M * y = y * M := by
    have h := hβy
    rw [hM' y] at h
    calc M * y = M * y * M⁻¹ * M := by group
      _ = y * M := by rw [h]
  have hM01 : M 0 1 = 0 := by
    have h := congrArg (fun z : SL(2, F) => z 0 1) hMy
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM00,
      hM11, one_mul, mul_one] at h
    have h' : M 0 1 * (y 1 1 - y 0 0) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr (Ne.symm hw11))
  have hM1 : M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM00, hM01, hM10, hM11]
  rw [hβconj, hM1, map_one]

private theorem res1AutFix_sl2 (hn : n % 4 = 2) (hcard : Nat.card F = 2 ^ n) :
    Res1AutFix SL(2, F) := by
  haveI : CharP F 2 := char_two_of_card hcard
  intro y hy R₀ hR₀ hR₂ hyR X hX hXy hXR
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ := hX ⟨α, hα⟩
  have hαa : α ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent R₀ hR₂
  have hxu : ∀ z ∈ R₀, (x⁻¹ * z * x) 0 0 = 1 ∧ (x⁻¹ * z * x) 1 0 = 0 := by
    intro z hz
    have hmem := hx ⟨z, hz, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
    have hh := (sl2_fixes_first_iff _).mpr hmem
    change Matrix.mulVec ((x⁻¹ * z * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) =
      Pi.single 0 1 at hh
    rw [Matrix.mulVec_single_one] at hh
    exact ⟨by simpa using congrFun hh 0, by simpa using congrFun hh 1⟩
  obtain ⟨u, huR, hu1⟩ := (Subgroup.bot_or_exists_ne_one R₀).resolve_left hR₀
  set c := MulAut.conj x with hc
  set β := c⁻¹ * α * c with hβ
  have hβapp : ∀ g, β g = x⁻¹ * α (x * g * x⁻¹) * x := fun g => rfl
  have hβpow : β ^ 2 ^ a = 1 := by
    have h := conj_pow (a := c⁻¹) (b := α) (i := 2 ^ a)
    rw [inv_inv, hαa, mul_one, inv_mul_cancel] at h
    rw [hβ]
    exact h
  have hβ1 : β = 1 := by
    refine eq_one_of_fix_unitri hn hcard β (a := a) hβpow
      (u := x⁻¹ * u * x) (hxu u huR).1 (hxu u huR).2 ?_ ?_ (y := x⁻¹ * y * x) ?_ ?_ ?_
    · intro h1
      apply hu1
      calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · rw [hβapp, show x * (x⁻¹ * u * x) * x⁻¹ = u by group]
      exact (hxu _ (hXR α hα u huR)).2
    · have h := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) y
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, hy]
    · have h1 : x⁻¹ * y * x * (x⁻¹ * u * x) * (x⁻¹ * y * x)⁻¹ = x⁻¹ * (y * u * y⁻¹) * x := by
        group
      rw [h1]
      exact (hxu _ (hyR u huR)).2
    · rw [hβapp, show x * (x⁻¹ * y * x) * x⁻¹ = y by group, hXy α hα]
  calc α = c * β * c⁻¹ := by rw [hβ]; group
    _ = 1 := by rw [hβ1]; group

end Main

theorem res1AutFix_projSL_two {n : ℕ} (hn : n % 4 = 2) :
    Res1AutFix ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)) :=
  Res1AutFix.of_mulEquiv
    ((CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n)).trans
      sl2EquivPSL2.symm)
    (res1AutFix_sl2 hn (GaloisField.card 2 n (by omega)))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
