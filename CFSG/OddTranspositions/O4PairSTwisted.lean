module

public import CFSG.OddTranspositions.O4PairTenInvolutions

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

open scoped MatrixGroups

local instance factPrimeFiveSTwisted : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def t25 : F25t := ⟨0, 1⟩

theorem t25_sq : t25 ^ 2 = (3 : F25t) := by
  have h3 : (3 : F25t) = ⟨3, 0⟩ := rfl
  rw [h3, pow_two]
  apply F25t.ext <;> simp [t25, mul25_def]

theorem t25_mul_self : t25 * t25 = (3 : F25t) := by
  rw [← pow_two]
  exact t25_sq

private theorem two_ne_zero_f25t : (2 : F25t) ≠ 0 := by
  have h2 : (2 : F25t) = ⟨2, 0⟩ := rfl
  rw [h2]
  intro h
  have h' : (2 : ZMod 5) = 0 := congrArg F25t.a h
  exact absurd h' (by decide)

private theorem three_mul_two : (3 : F25t) * 2 = 1 := by
  have h3 : (3 : F25t) = ⟨3, 0⟩ := rfl
  have h2 : (2 : F25t) = ⟨2, 0⟩ := rfl
  rw [h3, h2]
  apply F25t.ext <;> decide

private theorem three_ne_zero : (3 : F25t) ≠ 0 := by
  have h3 : (3 : F25t) = ⟨3, 0⟩ := rfl
  rw [h3]
  intro h
  have h' : (3 : ZMod 5) = 0 := congrArg F25t.a h
  exact absurd h' (by decide)

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

noncomputable def langMap (p : Matrix.SpecialLinearGroup (Fin 2) F25t) : PSL2 F25t :=
  CFSG.PSL2Table.mk (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹)

def St : Set (PSL2 F25t) := Set.range langMap

theorem mem_St_iff {q : PSL2 F25t} :
    q ∈ St ↔ ∃ p : Matrix.SpecialLinearGroup (Fin 2) F25t,
      q = CFSG.PSL2Table.mk p *
        (CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map frob25t.toRingHom p))⁻¹ := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, by simp only [langMap, map_mul, map_inv]⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, by simp only [langMap, hp, map_mul, map_inv]⟩

private theorem map_frob25t_map_frob25t (p : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    Matrix.SpecialLinearGroup.map frob25t.toRingHom
      (Matrix.SpecialLinearGroup.map frob25t.toRingHom p) = p := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, frob25t]

private theorem psl2FieldAut_mk (e : F25t ≃+* F25t)
    (A : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    CFSG.GorensteinWalter.psl2FieldAut F25t e (CFSG.PSL2Table.mk A) =
      CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map e.toRingHom A) := by
  show CFSG.GorensteinWalter.psl2RingEquiv e
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F25t)) A) = _
  rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
  rfl

theorem St_aut_inv {q : PSL2 F25t} (hq : q ∈ St) :
    CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q = q⁻¹ := by
  obtain ⟨p, rfl⟩ := hq
  rw [langMap, psl2FieldAut_mk]
  have hAA :
      Matrix.SpecialLinearGroup.map frob25t.toRingHom
          (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) =
        (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹)⁻¹ := by
    rw [map_mul, map_inv, map_frob25t_map_frob25t, mul_inv_rev, inv_inv]
  rw [hAA, map_inv]

theorem St_fixed_iff_sq {q : PSL2 F25t} (hq : q ∈ St) :
    CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q = q ↔ q * q = 1 := by
  rw [St_aut_inv hq, inv_eq_iff_mul_eq_one]

theorem eq_one_or_neg_one_of_sq_eq_one {A : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (h : A * A = 1) : A = 1 ∨ A = -1 := by
  have hinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right h
  have hcoe : ((A : Matrix.SpecialLinearGroup (Fin 2) F25t) : Matrix (Fin 2) (Fin 2) F25t) =
      !![(A : Matrix (Fin 2) (Fin 2) F25t) 1 1, -((A : Matrix (Fin 2) (Fin 2) F25t) 0 1);
        -((A : Matrix (Fin 2) (Fin 2) F25t) 1 0), (A : Matrix (Fin 2) (Fin 2) F25t) 0 0] := by
    refine (show (A : Matrix (Fin 2) (Fin 2) F25t) =
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F25t) : Matrix (Fin 2) (Fin 2) F25t) from by
      rw [hinv]).trans (CFSG.PSL2Table.coe_inv_SL A)
  have e01 : (A : Matrix (Fin 2) (Fin 2) F25t) 0 1 = -((A : Matrix (Fin 2) (Fin 2) F25t) 0 1) := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F25t => M 0 1) hcoe
    simpa using h'
  have e10 : (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = -((A : Matrix (Fin 2) (Fin 2) F25t) 1 0) := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F25t => M 1 0) hcoe
    simpa using h'
  have e11 : (A : Matrix (Fin 2) (Fin 2) F25t) 1 1 = (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F25t => M 1 1) hcoe
    simpa using h'
  have hb : (A : Matrix (Fin 2) (Fin 2) F25t) 0 1 = 0 := by
    have h2 : (2 : F25t) * (A : Matrix (Fin 2) (Fin 2) F25t) 0 1 = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp e01
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_f25t
  have hc : (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 0 := by
    have h2 : (2 : F25t) * (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp e10
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_f25t
  have hdet : (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 * (A : Matrix (Fin 2) (Fin 2) F25t) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F25t) 0 1 * (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 1 := by
    have h' := A.2
    rwa [Matrix.det_fin_two] at h'
  have hsq : (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 * (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 = 1 := by
    rw [e11, hb, hc, mul_zero, sub_zero] at hdet
    exact hdet
  have hfac : ((A : Matrix (Fin 2) (Fin 2) F25t) 0 0 - 1) *
      ((A : Matrix (Fin 2) (Fin 2) F25t) 0 0 + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    have ha : (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 = 1 := sub_eq_zero.mp h1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simp [ha, Matrix.SpecialLinearGroup.coe_one]
    · simp [hb, Matrix.SpecialLinearGroup.coe_one]
    · simp [hc, Matrix.SpecialLinearGroup.coe_one]
    · simp [e11, ha, Matrix.SpecialLinearGroup.coe_one]
  · right
    have ha : (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 = -1 := by linear_combination h1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simp [ha, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    · simp [hb, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      rfl
    · simp [hc, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      rfl
    · simp [e11, ha, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

private theorem t25_mul_zmodToF25t (b : ZMod 5) : (t25 : F25t) * zmodToF25t b = ⟨0, b⟩ := by
  have hz : zmodToF25t b = ⟨b, 0⟩ := rfl
  rw [hz]
  apply F25t.ext
  · simp only [t25, mul25_def, mul_zero, zero_mul, add_zero, zero_add]
  · simp only [t25, mul25_def, mul_zero, zero_mul, add_zero, zero_add, one_mul]

theorem minus_decomposition {A : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (hσ : Matrix.SpecialLinearGroup.map frob25t.toRingHom A = -A) :
    ∃ B : Matrix (Fin 2) (Fin 2) (ZMod 5),
      (A : Matrix (Fin 2) (Fin 2) F25t) = (t25 : F25t) • B.map zmodToF25t := by
  have hcoe : (((Matrix.SpecialLinearGroup.map frob25t.toRingHom A) :
        Matrix.SpecialLinearGroup (Fin 2) F25t) : Matrix (Fin 2) (Fin 2) F25t) =
      -(((A : Matrix.SpecialLinearGroup (Fin 2) F25t)) : Matrix (Fin 2) (Fin 2) F25t) := by
    rw [hσ, Matrix.SpecialLinearGroup.coe_neg]
  have hentry : ∀ i j, (A : Matrix (Fin 2) (Fin 2) F25t) i j =
      (t25 : F25t) * zmodToF25t ((A : Matrix (Fin 2) (Fin 2) F25t) i j).b := by
    intro i j
    have happ : frob25t ((A : Matrix (Fin 2) (Fin 2) F25t) i j) =
        -((A : Matrix (Fin 2) (Fin 2) F25t) i j) := by
      have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F25t => M i j) hcoe
      rwa [Matrix.SpecialLinearGroup.map_apply_coe] at h'
    have ha : ((A : Matrix (Fin 2) (Fin 2) F25t) i j).a = 0 := by
      have h' := congrArg F25t.a happ
      simp [frob25t] at h'
      have h2 : (2 : ZMod 5) * ((A : Matrix (Fin 2) (Fin 2) F25t) i j).a = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp h'
      exact (mul_eq_zero.mp h2).resolve_left (by decide)
    rw [t25_mul_zmodToF25t]
    exact F25t.ext ha rfl
  refine ⟨fun i j => ((A : Matrix (Fin 2) (Fin 2) F25t) i j).b, ?_⟩
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hentry i j

private theorem five_eq_zero_f25t : (5 : F25t) = 0 := by
  have h5 : (5 : F25t) = ⟨5, 0⟩ := rfl
  rw [h5, zero25_def]
  apply F25t.ext <;> decide

private theorem three_mul_three : (3 : F25t) * 3 = -1 := by
  have h3 : (3 : F25t) = ⟨3, 0⟩ := rfl
  have hm : (-1 : F25t) = ⟨-1, 0⟩ := rfl
  rw [h3, hm]
  apply F25t.ext <;> decide

theorem minus_data {A : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (hσ : Matrix.SpecialLinearGroup.map frob25t.toRingHom A = -A) (h2 : A * A = -1)
    {B : Matrix (Fin 2) (Fin 2) (ZMod 5)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F25t) = (t25 : F25t) • B.map zmodToF25t) :
    B.trace = 0 ∧ B.det = (2 : ZMod 5) := by
  have h2m : (A : Matrix (Fin 2) (Fin 2) F25t) * (A : Matrix (Fin 2) (Fin 2) F25t) =
      -(1 : Matrix (Fin 2) (Fin 2) F25t) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
  rw [hA] at h2m
  have hmul : ((t25 : F25t) • B.map zmodToF25t) * ((t25 : F25t) • B.map zmodToF25t) =
      (t25 * t25 : F25t) • ((B.map zmodToF25t) * (B.map zmodToF25t)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h3 : (3 : F25t) • ((B.map zmodToF25t) * (B.map zmodToF25t)) = -1 := by
    have h := h2m
    rw [hmul, t25_mul_self] at h
    exact h
  have h3' : (3 : F25t) • ((3 : F25t) • (1 : Matrix (Fin 2) (Fin 2) F25t)) = -1 := by
    rw [smul_smul, three_mul_three, neg_smul, one_smul]
  have hMM : (B.map zmodToF25t) * (B.map zmodToF25t) =
      (3 : F25t) • (1 : Matrix (Fin 2) (Fin 2) F25t) := by
    refine (smul_right_inj three_ne_zero).mp ?_
    rw [h3, h3']
  have hz : zmodToF25t B.det = (2 : F25t) := by
    have h1 : ((t25 : F25t) • B.map zmodToF25t).det = 1 := by
      rw [← hA]
      exact A.2
    rw [Matrix.det_smul, Fintype.card_fin, t25_sq,
      show B.map zmodToF25t = zmodToF25t.mapMatrix B from rfl,
      ← RingHom.map_det] at h1
    calc zmodToF25t B.det = 1 * zmodToF25t B.det := (one_mul _).symm
      _ = ((3 : F25t) * 2) * zmodToF25t B.det := by rw [three_mul_two]
      _ = 2 * ((3 : F25t) * zmodToF25t B.det) := by ring
      _ = 2 * 1 := by rw [h1]
      _ = 2 := mul_one 2
  have hdetM : (B.map zmodToF25t).det = (2 : F25t) := by
    rw [show B.map zmodToF25t = zmodToF25t.mapMatrix B from rfl, ← RingHom.map_det]
    exact hz
  have hdetM' : (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 1 1 -
      (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 = (2 : F25t) := by
    rw [Matrix.det_fin_two] at hdetM
    exact hdetM
  have h00 : (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 0 0 +
      (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 = (3 : F25t) := by
    have h' := congrArg (fun N : Matrix (Fin 2) (Fin 2) F25t => N 0 0) hMM
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] at h'
    simpa only [Matrix.one_apply_eq, smul_eq_mul, mul_one] using h'
  have h11 : (B.map zmodToF25t) 1 0 * (B.map zmodToF25t) 0 1 +
      (B.map zmodToF25t) 1 1 * (B.map zmodToF25t) 1 1 = (3 : F25t) := by
    have h' := congrArg (fun N : Matrix (Fin 2) (Fin 2) F25t => N 1 1) hMM
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] at h'
    simpa only [Matrix.one_apply_eq, smul_eq_mul, mul_one] using h'
  have ha : (B.map zmodToF25t) 0 0 *
      ((B.map zmodToF25t) 0 0 + (B.map zmodToF25t) 1 1) = 0 := by
    have h1 : (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 0 0 =
        (3 : F25t) - (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 := by
      linear_combination h00
    have h2 : (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 1 1 =
        (2 : F25t) + (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 := by
      linear_combination hdetM'
    calc (B.map zmodToF25t) 0 0 *
          ((B.map zmodToF25t) 0 0 + (B.map zmodToF25t) 1 1)
        = (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 0 0 +
            (B.map zmodToF25t) 0 0 * (B.map zmodToF25t) 1 1 := by ring
      _ = ((3 : F25t) - (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0) +
            ((2 : F25t) + (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0) := by
          rw [h1, h2]
      _ = (5 : F25t) := by ring
      _ = 0 := five_eq_zero_f25t
  have hb : (B.map zmodToF25t) 1 1 *
      ((B.map zmodToF25t) 0 0 + (B.map zmodToF25t) 1 1) = 0 := by
    have h1 : (B.map zmodToF25t) 1 1 * (B.map zmodToF25t) 1 1 =
        (3 : F25t) - (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 := by
      linear_combination h11
    have h2 : (B.map zmodToF25t) 1 1 * (B.map zmodToF25t) 0 0 =
        (2 : F25t) + (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0 := by
      linear_combination hdetM'
    calc (B.map zmodToF25t) 1 1 *
          ((B.map zmodToF25t) 0 0 + (B.map zmodToF25t) 1 1)
        = (B.map zmodToF25t) 1 1 * (B.map zmodToF25t) 0 0 +
            (B.map zmodToF25t) 1 1 * (B.map zmodToF25t) 1 1 := by ring
      _ = ((2 : F25t) + (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0) +
            ((3 : F25t) - (B.map zmodToF25t) 0 1 * (B.map zmodToF25t) 1 0) := by
          rw [h1, h2]
      _ = (5 : F25t) := by ring
      _ = 0 := five_eq_zero_f25t
  have htrM : (B.map zmodToF25t).trace = 0 := by
    rw [Matrix.trace_fin_two]
    by_contra hne
    have h0 : (B.map zmodToF25t) 0 0 = 0 := (mul_eq_zero.mp ha).resolve_right hne
    have h1 : (B.map zmodToF25t) 1 1 = 0 := (mul_eq_zero.mp hb).resolve_right hne
    exact hne (by rw [h0, h1, add_zero])
  have htrz : zmodToF25t B.trace = 0 := by
    rw [← htrM]
    exact (AddMonoidHom.map_trace zmodToF25t B).symm
  refine ⟨?_, ?_⟩
  · refine RingHom.injective zmodToF25t ?_
    rw [htrz, map_zero]
  ·
    refine RingHom.injective zmodToF25t ?_
    rw [hz]
    rfl

theorem exists_x_of_trace_det {B : Matrix (Fin 2) (Fin 2) (ZMod 5)}
    (htr : B.trace = 0) (hdet : B.det = (2 : ZMod 5)) :
    ∃ i : Fin 10,
      (t25 : F25t) • B.map zmodToF25t = (X i : Matrix (Fin 2) (Fin 2) F25t) ∨
        (t25 : F25t) • B.map zmodToF25t = -((X i : Matrix (Fin 2) (Fin 2) F25t)) := by
  letI : DecidableEq F25t := f25tDecEq
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ZMod 5, B = !![a, b; c, d] :=
    ⟨B 0 0, B 0 1, B 1 0, B 1 1, Matrix.eta_fin_two B⟩
  rw [Matrix.trace_fin_two_of] at htr
  rw [Matrix.det_fin_two_of] at hdet
  have hd : d = -a := eq_neg_of_add_eq_zero_right htr
  subst hd
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
      | exact absurd hdet (by decide)
      | decide

theorem minus_class_mem_range_x {A : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (hσ : Matrix.SpecialLinearGroup.map frob25t.toRingHom A = -A) (h2 : A * A = -1) :
    CFSG.PSL2Table.mk A ∈ Set.range x := by
  obtain ⟨B, hB⟩ := minus_decomposition hσ
  obtain ⟨htr, hdet⟩ := minus_data hσ h2 hB
  obtain ⟨i, hi | hi⟩ := exists_x_of_trace_det htr hdet
  · refine ⟨i, ?_⟩
    have hXA : A = X i := Subtype.ext (by rw [hB, hi])
    rw [hXA]
    rfl
  · refine ⟨i, ?_⟩
    have hXA : A = -X i := Subtype.ext (by
      rw [hB, hi]
      exact (Matrix.SpecialLinearGroup.coe_neg (X i)).symm)
    rw [hXA, CFSG.PSL2Table.mk_neg]
    rfl

private theorem X_mul_self (i : Fin 10) : X i * X i = -1 := by
  letI : DecidableEq F25t := f25tDecEq
  fin_cases i <;> decide

private theorem X_ne_pm_one (i : Fin 10) : X i ≠ 1 ∧ X i ≠ -1 := by
  letI : DecidableEq F25t := f25tDecEq
  fin_cases i <;> decide

private theorem x_ne_one (i : Fin 10) : x i ≠ 1 := by
  intro h
  rcases (CFSG.PSL2Table.mk_eq_one_iff (X i)).mp h with h1 | h1
  · exact (X_ne_pm_one i).1 h1
  · exact (X_ne_pm_one i).2 h1

private theorem mul_map_frob_self {p : Matrix.SpecialLinearGroup (Fin 2) F25t} :
    (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) *
        Matrix.SpecialLinearGroup.map frob25t.toRingHom
          (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) = 1 := by
  rw [map_mul, map_inv, map_frob25t_map_frob25t]
  group

private theorem map_frob_eq_neg_of_mk_eq {A : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (h2 : A * A = -1)
    (hAσ : A * Matrix.SpecialLinearGroup.map frob25t.toRingHom A = 1)
    (h : CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map frob25t.toRingHom A) =
      CFSG.PSL2Table.mk A) :
    Matrix.SpecialLinearGroup.map frob25t.toRingHom A = -A := by
  rcases (CFSG.PSL2Table.mk_eq_mk_iff (Matrix.SpecialLinearGroup.map frob25t.toRingHom A) A).mp h
    with h' | h'
  · exfalso
    have h1 : A * A = 1 := by
      have hh := hAσ
      rw [← h'] at hh
      exact hh
    rw [h2] at h1
    exact (CFSG.PSL2Table.neg_one_ne_one_SL two_ne_zero_f25t) h1
  · have h3 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F25t => -X) h'
    rw [neg_neg] at h3
    exact h3.symm

theorem St_involutions_eq :
    {q : PSL2 F25t | q ∈ St ∧ q * q = 1} = insert 1 (Set.range x) := by
  ext q
  constructor
  · rintro ⟨hq, hqq⟩
    obtain ⟨p, hp⟩ := mem_St_iff.mp hq
    have hqA : q = CFSG.PSL2Table.mk
        (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) := by
      rw [hp]
      simp only [map_mul, map_inv]
    have hAA : CFSG.PSL2Table.mk
        ((p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) *
          (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹)) = 1 := by
      rw [map_mul, ← hqA]
      exact hqq
    have hfix : CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q = q := by
      rw [St_aut_inv hq]
      exact (inv_eq_iff_mul_eq_one).mpr hqq
    have hfixA : CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map frob25t.toRingHom
          (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹)) =
        CFSG.PSL2Table.mk (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) := by
      have h := hfix
      rw [hqA] at h
      rwa [psl2FieldAut_mk] at h
    rcases (CFSG.PSL2Table.mk_eq_one_iff
      ((p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹) *
        (p * (Matrix.SpecialLinearGroup.map frob25t.toRingHom p)⁻¹))).mp hAA with h1 | h1
    · left
      rcases eq_one_or_neg_one_of_sq_eq_one h1 with hA | hA
      · rw [hqA, hA, map_one]
      · rw [hqA, hA, CFSG.PSL2Table.mk_neg, map_one]
    · right
      rw [hqA]
      exact minus_class_mem_range_x
        (map_frob_eq_neg_of_mk_eq h1 mul_map_frob_self hfixA) h1
  · rintro (rfl | ⟨i, rfl⟩)
    · refine ⟨?_, one_mul 1⟩
      refine ⟨1, ?_⟩
      rw [langMap]
      simp
    · refine ⟨?_, ?_⟩
      · refine mem_St_iff.mpr ⟨P i, ?_⟩
        rw [x, x_in_twisted_class i]
        simp only [map_mul, map_inv]
      · have h : x i * x i = CFSG.PSL2Table.mk (X i * X i) := by
          rw [x, ← map_mul]
        rw [h, X_mul_self i, CFSG.PSL2Table.mk_neg, map_one]

theorem card_St_involutions :
    Nat.card {q : PSL2 F25t // q ∈ St ∧ q * q = 1} = 11 := by
  have himg : {q : PSL2 F25t | q ∈ St ∧ q * q = 1} =
      Set.range (fun o : Option (Fin 10) => o.elim (1 : PSL2 F25t) x) := by
    rw [St_involutions_eq]
    ext q
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inl rfl
      | some i => exact Or.inr ⟨i, rfl⟩
  have hinj : Function.Injective (fun o : Option (Fin 10) => o.elim (1 : PSL2 F25t) x) := by
    intro o1 o2 h
    cases o1 with
    | none =>
      cases o2 with
      | none => rfl
      | some j =>
        simp only [Option.elim_none, Option.elim_some] at h
        exact absurd h.symm (x_ne_one j)
    | some i =>
      cases o2 with
      | none =>
        simp only [Option.elim_some] at h
        exact absurd h (x_ne_one i)
      | some j =>
        simp only [Option.elim_some] at h
        rw [x_injective h]
  calc Nat.card {q : PSL2 F25t // q ∈ St ∧ q * q = 1}
      = Nat.card (Set.range (fun o : Option (Fin 10) => o.elim (1 : PSL2 F25t) x)) :=
        Nat.card_congr (Set.equivOfEq himg)
    _ = Nat.card (Option (Fin 10)) := Nat.card_congr (Equiv.ofInjective _ hinj).symm
    _ = 11 := by rw [Finite.card_option, Nat.card_fin]

theorem St_involutions_nontrivial :
    {q : PSL2 F25t | q ∈ St ∧ q * q = 1 ∧ q ≠ 1} = Set.range x := by
  ext q
  have hiff : (q ∈ St ∧ q * q = 1) ↔ q ∈ insert (1 : PSL2 F25t) (Set.range x) := by
    rw [← Set.mem_setOf_eq (p := fun q : PSL2 F25t => q ∈ St ∧ q * q = 1),
      St_involutions_eq]
  constructor
  · rintro ⟨hq, hqq, hne⟩
    rcases hiff.mp ⟨hq, hqq⟩ with rfl | h
    · exact absurd rfl hne
    · exact h
  · rintro ⟨i, rfl⟩
    exact ⟨(hiff.mpr (Or.inr ⟨i, rfl⟩)).1, (hiff.mpr (Or.inr ⟨i, rfl⟩)).2, x_ne_one i⟩

end CFSG.OddTranspositions.QZ
