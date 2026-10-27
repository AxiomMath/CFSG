module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAlpha
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAlphaChk4
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAlphaChk5
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnHolds

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix Hering214 CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem sl_pow_of_coprime {n m : ℕ}
    (hcard : Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) = 9 * m)
    {s : SpecialLinearGroup (Fin n) (ZMod 2)} (h : Nat.Coprime 3 (orderOf s)) : s ^ m = 1 := by
  have h1 : orderOf s ∣ 9 * m := hcard ▸ orderOf_dvd_natCard s
  have h2 : Nat.Coprime (orderOf s) 9 := by
    have := Nat.Coprime.pow_right 2 h.symm
    simpa using this
  exact orderOf_dvd_iff_pow_eq_one.mp (Nat.Coprime.dvd_of_dvd_mul_left h2 h1)

theorem hbad_of_chk {n m : ℕ} (hcard : Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) = 9 * m)
    (a : SpecialLinearGroup (Fin n) (ZMod 2)) (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (ha : (a : Matrix (Fin n) (Fin n) (ZMod 2)) = A) (bs : List Bool) (hbs : bsVal 1 bs = m)
    (W : List (List ℕ × List ℕ))
    (hW : ∀ p ∈ W, Bd n p.1 ∧ Bd n p.2 ∧ toM n p.1 * toM n p.2 = 1 ∧
      toM n p.1 * A = A * toM n p.1)
    (hcode : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M * A = A * M →
      ∃ X, Bd n X ∧ toM n X = M ∧ chk n bs W X = true) : HBad a := by
  intro s hs hs1 hcop
  have hM : (s : Matrix (Fin n) (Fin n) (ZMod 2)) * A =
      A * (s : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← ha]; exact sl_comm_coe hs
  obtain ⟨X, hBd, hX, hchk⟩ := hcode _ hM
  have hpow : (s : Matrix (Fin n) (Fin n) (ZMod 2)) ^ m = 1 := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) (sl_pow_of_coprime hcard hcop)
    simpa [Matrix.SpecialLinearGroup.coe_pow] using h
  rw [← hX, ← hbs] at hpow
  rcases chk_sound (fun p hp => ⟨(hW p hp).1, (hW p hp).2.1⟩) hBd hpow hchk with
    h | ⟨p, hp, hp1, hp2, hne⟩
  · exact absurd (Subtype.ext (hX.symm.trans h)) hs1
  · obtain ⟨-, -, hinv, hcomm⟩ := hW p hp
    have hinv' : toM n p.2 * toM n p.1 = 1 := mul_eq_one_comm.mp hinv
    let w : SpecialLinearGroup (Fin n) (ZMod 2) :=
      ⟨toM n p.1, det_eq_one_of_mul_eq_one_two _ _ hinv⟩
    let w' : SpecialLinearGroup (Fin n) (ZMod 2) :=
      ⟨toM n p.2, det_eq_one_of_mul_eq_one_two _ _ hinv'⟩
    have hww : w * w' = 1 := Subtype.ext (by simpa using hinv)
    have hw' : w⁻¹ = w' := inv_eq_of_mul_eq_one_right hww
    refine ⟨w, Subtype.ext ?_, fun hcop' => ?_⟩
    · show toM n p.1 * (a : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (a : Matrix (Fin n) (Fin n) (ZMod 2)) * toM n p.1
      rw [ha]; exact hcomm
    · apply hne
      have h3 := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
        (g : Matrix (Fin n) (Fin n) (ZMod 2))) (sl_pow_of_coprime hcard hcop')
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, hw', w, w',
        Matrix.SpecialLinearGroup.coe_one] at h3
      rw [hbs, hX]
      exact h3

theorem hbad_4a : HBad sA4 :=
  hbad_of_chk (m := 2240) ((card_specialLinearGroup_four (Nat.card_zmod 2)).trans (by norm_num))
    sA4 A4 rfl bits4 bsVal_bits4 W4a W_ok_4a fun _ hM => hcode_4a hM

theorem coe_sAB4 : ((sA4 * sB4 : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = AB4 := by
  exact (Matrix.SpecialLinearGroup.coe_mul sA4 sB4).trans A4_mul_B4

theorem coe_sAB5 : ((sA5 * sB5 : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2)) = AB5 := by
  exact (Matrix.SpecialLinearGroup.coe_mul sA5 sB5).trans A5_mul_B5

theorem hbad_4ab : HBad (sA4 * sB4) :=
  hbad_of_chk (m := 2240) ((card_specialLinearGroup_four (Nat.card_zmod 2)).trans (by norm_num))
    _ AB4 coe_sAB4 bits4 bsVal_bits4 W4ab W_ok_4ab fun _ hM => hcode_4ab hM

theorem hbad_5a : HBad sA5 :=
  hbad_of_chk (m := 1111040) ((card_specialLinearGroup_five (Nat.card_zmod 2)).trans (by norm_num))
    sA5 A5 rfl bits5 bsVal_bits5 W5a W_ok_5a fun _ hM => hcode_5a hM

theorem hbad_5ab : HBad (sA5 * sB5) :=
  hbad_of_chk (m := 1111040) ((card_specialLinearGroup_five (Nat.card_zmod 2)).trans (by norm_num))
    _ AB5 coe_sAB5 bits5 bsVal_bits5 W5ab W_ok_5ab fun _ hM => hcode_5ab hM

theorem hx5 {a₀ : SpecialLinearGroup (Fin 5) (ZMod 2)} {A Cm Ci : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (ha : (a₀ : Matrix (Fin 5) (Fin 5) (ZMod 2)) = A) (hC : Cm * Ci = 1)
    (hcomm : Cm * A = A * Cm)
    (hchk : ∀ i j : Fin 3, Cm * (A5 ^ (i : ℕ) * B5 ^ (j : ℕ) * (R1M5 * R2M5)) * Cmᵀ ≠
      A5 ^ (i : ℕ) * B5 ^ (j : ℕ) * (R1M5 * R2M5)) :
    HX (R sA5 sB5) (deltaS (Or.inr rfl)) a₀ := by
  refine hx_of_tau tModel5 _ (τ := sR1_5 * sR2_5) (fun x hx => normData5.tau_inv hx) ?_
  intro p hp
  obtain ⟨i, j, rfl⟩ := normData5.toE9Data.mem_R_iff.mp hp
  have hCi : Ci * Cm = 1 := mul_eq_one_comm.mp hC
  let c : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨Cm, det_eq_one_of_mul_eq_one_two _ _ hC⟩
  let c' : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨Ci, det_eq_one_of_mul_eq_one_two _ _ hCi⟩
  have hcc : c * c' = 1 := Subtype.ext (by simpa using hC)
  have hc' : c⁻¹ = c' := inv_eq_of_mul_eq_one_right hcc
  refine ⟨c, Subtype.ext ?_, fun heq => ?_⟩
  · show Cm * (a₀ : Matrix (Fin 5) (Fin 5) (ZMod 2)) = (a₀ : Matrix (Fin 5) (Fin 5) (ZMod 2)) * Cm
    rw [ha]; exact hcomm
  · set T : SpecialLinearGroup (Fin 5) (ZMod 2) :=
      sA5 ^ (i : ℕ) * sB5 ^ (j : ℕ) * (sR1_5 * sR2_5) with hT
    have hP : (T : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        A5 ^ (i : ℕ) * B5 ^ (j : ℕ) * (R1M5 * R2M5) := by
      simp only [hT, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]; rfl
    have hD : ((deltaS (Or.inr rfl) c : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = Ciᵀ := by
      rw [deltaS_coe, hc']
    have hTT : ((T⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        (T : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) heq
    simp only [Matrix.SpecialLinearGroup.coe_mul, hD] at h1
    generalize (T : Matrix (Fin 5) (Fin 5) (ZMod 2)) = P at hP hTT h1
    generalize ((T⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = Pi at hTT h1
    have e1 : P * Ciᵀ = Cm * P := by
      calc P * Ciᵀ = P * Ciᵀ * (Pi * P) := by rw [hTT, mul_one]
        _ = (P * Ciᵀ * Pi) * P := by simp only [mul_assoc]
        _ = Cm * P := by rw [h1]
    have e2 : Ciᵀ * Cmᵀ = 1 := by rw [← Matrix.transpose_mul, hC, Matrix.transpose_one]
    have e3 : P = Cm * P * Cmᵀ := by
      calc P = P * (Ciᵀ * Cmᵀ) := by rw [e2, mul_one]
        _ = P * Ciᵀ * Cmᵀ := by rw [mul_assoc]
        _ = _ := by rw [e1]
    exact hchk i j (by rw [← hP]; exact e3.symm)

@[expose] def Cm5a : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0]

@[expose] def Cm5ab : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def Ci5ab : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1]

theorem hx_5a : HX (R sA5 sB5) (deltaS (Or.inr rfl)) sA5 :=
  hx5 (A := A5) (Cm := Cm5a) (Ci := Cm5a) rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem hx_5ab : HX (R sA5 sB5) (deltaS (Or.inr rfl)) (sA5 * sB5) :=
  hx5 (A := AB5) (Cm := Cm5ab) (Ci := Ci5ab) coe_sAB5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem centAlphaS4 : CentAlphaS (SpecialLinearGroup (Fin 4) (ZMod 2)) (R sA4 sB4) 4 := by
  have hδ : ∀ x ∈ R sA4 sB4, deltaS (Or.inl rfl) x = x⁻¹ := fun x hx =>
    deltaS_apply _ (sym_R normData4.toE9Data sym4 (inv_mem hx))
  have E := normData4.toE9Data
  exact centAlphaS_of_reps normData4
    (qa_of_checks tModel4 _ hδ (autForm (Or.inl rfl)) E.a_mem hbad_4a
      fun h => absurd h (by norm_num))
    (qa_of_checks tModel4 _ hδ (autForm (Or.inl rfl)) (mul_mem E.a_mem E.b_mem) hbad_4ab
      fun h => absurd h (by norm_num))

theorem centAlphaS5 : CentAlphaS (SpecialLinearGroup (Fin 5) (ZMod 2)) (R sA5 sB5) 5 := by
  have hδ : ∀ x ∈ R sA5 sB5, deltaS (Or.inr rfl) x = x⁻¹ := fun x hx =>
    deltaS_apply _ (sym_R normData5.toE9Data sym5 (inv_mem hx))
  have E := normData5.toE9Data
  exact centAlphaS_of_reps normData5
    (qa_of_checks tModel5 _ hδ (autForm (Or.inr rfl)) E.a_mem hbad_5a fun _ => hx_5a)
    (qa_of_checks tModel5 _ hδ (autForm (Or.inr rfl)) (mul_mem E.a_mem E.b_mem) hbad_5ab
      fun _ => hx_5ab)

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn

namespace CFSG.RankThree.PartTwo.Sec21.FF79

theorem ff79KCentAlpha_holds :
    FF79KCentAlpha :=
  ff79KCentAlpha_of_finite TLn.centAlphaS4 TLn.centAlphaS5

end CFSG.RankThree.PartTwo.Sec21.FF79
