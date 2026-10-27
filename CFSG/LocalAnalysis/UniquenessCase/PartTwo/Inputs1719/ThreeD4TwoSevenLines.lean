module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLineChecksA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLineChecksB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42

theorem lineW_check (i : Fin 8) : chunkArr (lineChunks i) = lineW i := by
  fin_cases i
  exacts [lineW_check_0, lineW_check_1, lineW_check_2, lineW_check_3, lineW_check_4,
    lineW_check_5, lineW_check_6, lineW_check_7]

theorem lineRel_check (i : Fin 8) : mulArr (lineW i) (lineQ i) =
      mulArr (powArr (lineQ i) (lineExp i)) (lineW i) ∧
    mulArr (lineW i) (mulArr (lineW i) (lineW i)) = oneArr ∧ lineW i ≠ oneArr ∧
    (lineW i).size = 64 := by
  fin_cases i
  exacts [lineRel_check_0, lineRel_check_1, lineRel_check_2, lineRel_check_3, lineRel_check_4,
    lineRel_check_5, lineRel_check_6, lineRel_check_7]

theorem lineQ_check (i : Fin 8) (hi : i.val < 7) :
    mulArr e49ArrH (powArr e49ArrZ i.val) = lineQ i := by
  fin_cases i
  exacts [lineQ_check_0, lineQ_check_1, lineQ_check_2, lineQ_check_3, lineQ_check_4,
    lineQ_check_5, lineQ_check_6, absurd hi (by decide)]

@[expose] def matOf (a : ↥trialityGroup8) : Matrix (Fin 8) (Fin 8) GF8 :=
  ((a : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8)

theorem matOf_mul (a b : ↥trialityGroup8) : matOf (a * b) = matOf a * matOf b := rfl

theorem matOf_one : matOf 1 = 1 := rfl

theorem matOf_pow (a : ↥trialityGroup8) (n : ℕ) : matOf (a ^ n) = matOf a ^ n := by
  rw [matOf, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rfl

theorem matOf_injective : Function.Injective matOf := fun _ _ h => Subtype.ext (Units.ext h)

noncomputable def hD : ↥trialityGroup8 := ⟨wordGL e49WordH, wordGL_mem _⟩

noncomputable def zD : ↥trialityGroup8 := ⟨wordGL e49WordZ, wordGL_mem _⟩

noncomputable def qD (i : Fin 8) : ↥trialityGroup8 := if i.val < 7 then hD * zD ^ i.val else zD

noncomputable def wD (i : Fin 8) : ↥trialityGroup8 :=
  ⟨((lineChunks i).map wordGL).prod, Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact wordGL_mem c)⟩

theorem matOf_hD : matOf hD = toMat e49ArrH := by
  show ((wordGL e49WordH : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
  rw [coe_wordGL, e49_check_h]

theorem matOf_zD : matOf zD = toMat e49ArrZ := by
  show ((wordGL e49WordZ : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
  rw [coe_wordGL, e49_check_z]

theorem coe_prod_wordGL (cs : List (List ℕ)) :
    (((cs.map wordGL).prod : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      toMat (chunkArr cs) := by
  rw [toMat_chunkArr]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.prod_cons, Units.val_mul, ih, coe_wordGL]

theorem matOf_wD (i : Fin 8) : matOf (wD i) = toMat (lineW i) := by
  rw [← lineW_check i]
  exact coe_prod_wordGL _

theorem matOf_qD (i : Fin 8) : matOf (qD i) = toMat (lineQ i) := by
  unfold qD
  split_ifs with hi
  · rw [matOf_mul, matOf_pow, matOf_hD, matOf_zD, ← toMat_powArr, ← toMat_mulArr,
      lineQ_check i hi]
  · obtain ⟨iv, hiv⟩ := i
    have h7 : iv = 7 := by simp only at hi; omega
    subst h7
    rw [matOf_zD]
    rfl

theorem wD_conj (i : Fin 8) : wD i * qD i * (wD i)⁻¹ = qD i ^ lineExp i := by
  have h : wD i * qD i = qD i ^ lineExp i * wD i := matOf_injective (by
    rw [matOf_mul, matOf_mul, matOf_pow, matOf_wD, matOf_qD, ← toMat_powArr, ← toMat_mulArr,
      ← toMat_mulArr, (lineRel_check i).1])
  rw [h, mul_inv_cancel_right]

theorem wD_pow_three (i : Fin 8) : wD i ^ 3 = 1 := matOf_injective (by
  rw [matOf_pow, matOf_wD, matOf_one, pow_succ', pow_succ', pow_one, ← toMat_mulArr,
    ← toMat_mulArr, (lineRel_check i).2.1, oneArr, toMat_ofMat])

theorem wD_ne_one (i : Fin 8) : wD i ≠ 1 := by
  intro h
  have h1 : toMat (lineW i) = toMat oneArr := by
    rw [← matOf_wD, h, matOf_one, oneArr, toMat_ofMat]
  exact (lineRel_check i).2.2.1 (eq_of_toMat_eq (lineRel_check i).2.2.2 size_oneArr h1)

theorem matOf_hD_pow (n : ℕ) : matOf (hD ^ n) = Matrix.diagonal (e49DiagH ^ n) := by
  rw [matOf_pow, matOf_hD, e49_check_diag.1, Matrix.diagonal_pow]

theorem hD_pow_seven : hD ^ 7 = 1 := matOf_injective (by
  rw [matOf_hD_pow, e49_check_diag.2.1, matOf_one]
  simp)

theorem hD_ne_one : hD ≠ 1 := fun h1 => e49_check_diag.2.2.1 (by
  have h2 := congrArg (fun a => matOf a 0 0) h1
  simpa [matOf_hD, e49_check_diag.1, matOf_one] using h2)

theorem zD_pow_seven : zD ^ 7 = 1 := matOf_injective (by
  obtain ⟨h2, h4, h7⟩ := e49_check_z7
  have e2 : toMat e49ArrZ2 = toMat e49ArrZ ^ 2 := by rw [← h2, toMat_mulArr, sq]
  have e4 : toMat e49ArrZ4 = toMat e49ArrZ ^ 4 := by
    rw [← h4, toMat_mulArr, e2, ← pow_add]
  rw [matOf_pow, matOf_zD, matOf_one, show (7 : ℕ) = 4 + (2 + 1) from rfl, pow_add, pow_add,
    pow_one, ← e4, ← e2, ← toMat_mulArr, ← toMat_mulArr, h7, oneArr, toMat_ofMat])

theorem hD_mul_zD : hD * zD = zD * hD := matOf_injective (by
  rw [matOf_mul, matOf_mul, matOf_hD, matOf_zD, ← toMat_mulArr, ← toMat_mulArr, e49_check_comm])

theorem zD_not_mem : zD ∉ Subgroup.zpowers hD := by
  intro hz
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have h2 := congrArg (fun a => matOf a 0 5) hn
  simp only [matOf_hD_pow, matOf_zD] at h2
  rw [Matrix.diagonal_apply_ne _ (by decide)] at h2
  exact e49_check_diag.2.2.2 h2.symm

theorem card_P : Nat.card ↥(Subgroup.zpowers hD ⊔ Subgroup.zpowers zD) = 49 :=
  (elemAbelian_sup_of_commute hD_pow_seven hD_ne_one zD_pow_seven hD_mul_zD zD_not_mem).2

theorem exists_pow_mul_pow {y : ↥trialityGroup8}
    (hy : y ∈ Subgroup.zpowers hD ⊔ Subgroup.zpowers zD) : ∃ a b : ℕ, y = hD ^ a * zD ^ b := by
  have hcomm : ∀ x ∈ Subgroup.zpowers hD, ∀ y ∈ Subgroup.zpowers zD, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute hD zD from hD_mul_zD) i j).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hy' : y ∈ ((Subgroup.zpowers hD ⊔ Subgroup.zpowers zD : Subgroup _) : Set _) := hy
  rw [hset] at hy'
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  obtain ⟨a, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hu)
  obtain ⟨b, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hv)
  exact ⟨a, b, rfl⟩

theorem mod_seven_key : ∀ a < 7, ∀ b < 7, 0 < a → (b * a ^ 5 % 7 * a) % 7 = b := by
  decide

theorem exists_line {y : ↥trialityGroup8} (hy : y ∈ Subgroup.zpowers hD ⊔ Subgroup.zpowers zD) :
    ∃ (i : Fin 8) (k : ℕ), y = qD i ^ k := by
  obtain ⟨a, b, rfl⟩ := exists_pow_mul_pow hy
  rw [pow_eq_pow_mod a hD_pow_seven, pow_eq_pow_mod b zD_pow_seven]
  have ha : a % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hb : b % 7 < 7 := Nat.mod_lt _ (by norm_num)
  generalize a % 7 = a' at ha ⊢
  generalize b % 7 = b' at hb ⊢
  rcases Nat.eq_zero_or_pos a' with rfl | ha0
  · refine ⟨7, b', ?_⟩
    rw [pow_zero, one_mul, qD, if_neg (by decide)]
  · have hc : b' * a' ^ 5 % 7 < 7 := Nat.mod_lt _ (by norm_num)
    refine ⟨⟨b' * a' ^ 5 % 7, by omega⟩, a', ?_⟩
    rw [qD, if_pos hc, ((show Commute hD zD from hD_mul_zD).pow_right _).mul_pow, ← pow_mul]
    congr 1
    rw [pow_eq_pow_mod (_ * a') zD_pow_seven]
    show zD ^ b' = zD ^ ((b' * a' ^ 5 % 7 * a') % 7)
    rw [mod_seven_key a' ha b' hb ha0]

theorem exists_conj_pow_of_mem {y : ↥trialityGroup8}
    (hy : y ∈ Subgroup.zpowers hD ⊔ Subgroup.zpowers zD) :
    ∃ (w : ↥trialityGroup8) (m : ℕ), w * y * w⁻¹ = y ^ m ∧ w ^ 3 = 1 ∧ w ≠ 1 := by
  obtain ⟨i, k, rfl⟩ := exists_line hy
  refine ⟨wD i, lineExp i, ?_, wD_pow_three i, wD_ne_one i⟩
  rw [← conj_pow, wD_conj, ← pow_mul, ← pow_mul, Nat.mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines
