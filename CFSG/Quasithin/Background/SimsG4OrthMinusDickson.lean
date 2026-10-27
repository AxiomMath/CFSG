module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.PGroup
import CFSG.Dihedral.Glauberman.DicksonMaxCases
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Witness
import CFSG.Quasithin.Background.SimsG46SL2
import CFSG.Quasithin.Background.SimsG4OrthURefl
import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.Quasithin.SimsG4.OrthMinus

open Matrix

section Conj

variable {F : Type} [Field F] [CharP F 2]

@[expose] def uMat : Matrix (Fin 2) (Fin 2) F := !![1, 1; 0, 1]

theorem trace_eq_zero_of_mul_self {a : Matrix (Fin 2) (Fin 2) F} (hdet : a.det = 1)
    (ha : a * a = 1) : a.trace = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F, a = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two a⟩
  rw [Matrix.mul_fin_two] at ha
  have e00 := congrFun (congrFun ha 0) 0
  have e01 := congrFun (congrFun ha 0) 1
  have e10 := congrFun (congrFun ha 1) 0
  have e11 := congrFun (congrFun ha 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true] at e00 e01 e10 e11
  rw [Matrix.trace_fin_two_of]
  by_contra ht
  have hq : q = 0 := by
    have : q * (p + s) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right ht
  have hr : r = 0 := by
    have : r * (p + s) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right ht
  subst hq hr
  have hp : (p + 1) ^ 2 = 0 := by linear_combination e00 + (p + 1) * h2
  have hs : (s + 1) ^ 2 = 0 := by linear_combination e11 + (s + 1) * h2
  apply ht
  have h0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hp
  have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hs
  linear_combination h0 + h1 - h2

theorem exists_conj_eq_uMat {a : Matrix (Fin 2) (Fin 2) F} (hdet : a.det = 1) (ha : a * a = 1)
    (ha1 : a ≠ 1) :
    ∃ P P' : Matrix (Fin 2) (Fin 2) F, P * P' = 1 ∧ P' * P = 1 ∧ P * a * P' = uMat := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr := trace_eq_zero_of_mul_self hdet ha
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F, a = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two a⟩
  rw [Matrix.trace_fin_two_of] at htr
  rw [Matrix.det_fin_two_of] at hdet
  have hs : s = p := by linear_combination htr - p * h2
  subst s
  by_cases hr : r = 0
  · subst hr
    have hp : p = 1 := by
      have hsq : (p + 1) ^ 2 = 0 := by linear_combination hdet + (p + 1) * h2
      linear_combination (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq) - h2
    subst hp
    have hq : q ≠ 0 := by
      rintro rfl
      apply ha1
      rw [← Matrix.one_fin_two]
    refine ⟨!![1, 0; 0, q], !![1, 0; 0, q⁻¹], ?_, ?_, ?_⟩
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      simp [hq]
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      simp [hq]
    · rw [uMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
      simp [hq]
  · refine ⟨!![0, r⁻¹; 1, (p + 1) * r⁻¹], !![p + 1, 1; r, 0], ?_, ?_, ?_⟩
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hr]
      linear_combination (p + 1) * h2
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hr]
      linear_combination (p + 1) * r⁻¹ * h2
    · rw [uMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hr]
      · field_simp
        linear_combination p * h2
      · field_simp
        linear_combination hdet + (1 + 2 * p + p ^ 2 + q * r) * h2
      · field_simp
        linear_combination p * h2

theorem entries_mem_of_traces (K₀ : Subfield F) {c : F} (hc : c ≠ 0) (hcK : c ∈ K₀)
    (y : Matrix (Fin 2) (Fin 2) F) (h0 : y.trace ∈ K₀) (h1 : (uMat * y).trace ∈ K₀)
    (h2 : (!![0, c⁻¹; c, 0] * y).trace ∈ K₀) (h3 : (uMat * !![0, c⁻¹; c, 0] * y).trace ∈ K₀)
    (i j : Fin 2) : y i j ∈ K₀ := by
  rw [Matrix.trace_fin_two] at h0
  rw [uMat, Matrix.trace_fin_two] at h1 h3
  rw [Matrix.trace_fin_two] at h2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const] at h1 h2 h3
  have hci : c⁻¹ ∈ K₀ := K₀.inv_mem hcK
  have e10 : y 1 0 ∈ K₀ := by
    have : y 1 0 = (1 * y 0 0 + 1 * y 1 0 + (0 * y 0 1 + 1 * y 1 1)) - (y 0 0 + y 1 1) := by ring
    rw [this]
    exact K₀.sub_mem h1 h0
  have e00 : y 0 0 ∈ K₀ := by
    have : y 0 0 = c⁻¹ * (((1 * 0 + 1 * c) * y 0 0 + (1 * c⁻¹ + 1 * 0) * y 1 0 +
        ((0 * 0 + 1 * c) * y 0 1 + (0 * c⁻¹ + 1 * 0) * y 1 1)) -
        (0 * y 0 0 + c⁻¹ * y 1 0 + (c * y 0 1 + 0 * y 1 1))) := by
      field_simp
      ring
    rw [this]
    exact K₀.mul_mem hci (K₀.sub_mem h3 h2)
  have e11 : y 1 1 ∈ K₀ := by
    have : y 1 1 = (y 0 0 + y 1 1) - y 0 0 := by ring
    rw [this]
    exact K₀.sub_mem h0 e00
  have e01 : y 0 1 ∈ K₀ := by
    have : y 0 1 = c⁻¹ * ((0 * y 0 0 + c⁻¹ * y 1 0 + (c * y 0 1 + 0 * y 1 1)) -
        c⁻¹ * y 1 0) := by
      field_simp
      ring
    rw [this]
    exact K₀.mul_mem hci (K₀.sub_mem h2 (K₀.mul_mem hci e10))
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

theorem exists_conj_entries_of_uMat (K₀ : Subfield F) (S : Set (Matrix (Fin 2) (Fin 2) F))
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (htr : ∀ x ∈ S, x.trace ∈ K₀) (hu : uMat ∈ S)
    {b : Matrix (Fin 2) (Fin 2) F} (hb : b ∈ S) (hbdet : b.det = 1) (hb2 : b * b = 1)
    (hub : uMat * b ≠ b * uMat) :
    ∃ P P' : Matrix (Fin 2) (Fin 2) F, P * P' = 1 ∧ P' * P = 1 ∧
      ∀ x ∈ S, ∀ i j, (P * x * P') i j ∈ K₀ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htrb := trace_eq_zero_of_mul_self hbdet hb2
  obtain ⟨d, e, c, d', rfl⟩ : ∃ d e c d' : F, b = !![d, e; c, d'] :=
    ⟨_, _, _, _, Matrix.eta_fin_two b⟩
  rw [Matrix.trace_fin_two_of] at htrb
  have hdetb := hbdet
  rw [Matrix.det_fin_two_of] at hdetb
  have hs : d' = d := by linear_combination htrb - d * h2
  subst d'
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hd : d = 1 := by
      have hsq : (d + 1) ^ 2 = 0 := by linear_combination hdetb + (d + 1) * h2
      linear_combination (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq) - h2
    subst hd
    apply hub
    rw [uMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  set v : Matrix (Fin 2) (Fin 2) F := !![1, d / c; 0, 1] with hv
  have hvv : v * v = 1 := by
    rw [hv, Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination (d / c) * h2
  have hvu : v * uMat = uMat * v := by
    rw [hv, uMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  have hvb : v * !![d, e; c, d] * v = !![0, c⁻¹; c, 0] := by
    rw [hv, Matrix.mul_fin_two, Matrix.mul_fin_two]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
      linear_combination d * h2
    · field_simp
      linear_combination hdetb + (d ^ 2 + e * c) * h2
    · field_simp
      linear_combination d * h2
  have hcK : c ∈ K₀ := by
    have h := K₀.sub_mem (htr _ (hS _ hu _ hb)) (htr _ hb)
    have : (uMat * !![d, e; c, d]).trace - (!![d, e; c, d] : Matrix (Fin 2) (Fin 2) F).trace =
        c := by
      rw [uMat, Matrix.mul_fin_two, Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
      ring
    rwa [this] at h
  have htrv : ∀ x : Matrix (Fin 2) (Fin 2) F, (v * x * v).trace = x.trace := by
    intro x
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvv, Matrix.one_mul]
  refine ⟨v, v, hvv, hvv, fun x hx i j => ?_⟩
  refine entries_mem_of_traces K₀ hc0 hcK (v * x * v) ?_ ?_ ?_ ?_ i j
  · rw [htrv]
    exact htr x hx
  · have : uMat * (v * x * v) = v * (uMat * x) * v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hvu, Matrix.mul_assoc v uMat x]
    rw [this, htrv]
    exact htr _ (hS _ hu _ hx)
  · have : !![0, c⁻¹; c, 0] * (v * x * v) = v * (!![d, e; c, d] * x) * v := by
      rw [← hvb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc v v, hvv, Matrix.one_mul]
    rw [this, htrv]
    exact htr _ (hS _ hb _ hx)
  · have : uMat * !![0, c⁻¹; c, 0] * (v * x * v) = v * (uMat * !![d, e; c, d] * x) * v := by
      rw [← hvb]
      have e' : uMat * (v * !![d, e; c, d] * v) * (v * x * v) =
          (uMat * v) * !![d, e; c, d] * (v * v) * x * v := by
        simp only [Matrix.mul_assoc]
      rw [e', hvv, ← hvu]
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [this, htrv]
    exact htr _ (hS _ (hS _ hu _ hb) _ hx)

theorem exists_conj_entries_mem_subfield (K₀ : Subfield F) (S : Set (Matrix (Fin 2) (Fin 2) F))
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (htr : ∀ x ∈ S, x.trace ∈ K₀)
    {a b : Matrix (Fin 2) (Fin 2) F} (ha : a ∈ S) (hb : b ∈ S) (hadet : a.det = 1)
    (hbdet : b.det = 1) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b ≠ b * a) :
    ∃ P P' : Matrix (Fin 2) (Fin 2) F, P * P' = 1 ∧ P' * P = 1 ∧
      ∀ x ∈ S, ∀ i j, (P * x * P') i j ∈ K₀ := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hab (by rw [Matrix.one_mul, Matrix.mul_one])
  obtain ⟨P₁, P₁', h11, h12, hPa⟩ := exists_conj_eq_uMat hadet ha2 ha1
  set S₁ : Set (Matrix (Fin 2) (Fin 2) F) := (fun x => P₁ * x * P₁') '' S with hS₁
  have hconj_mul : ∀ x y : Matrix (Fin 2) (Fin 2) F,
      P₁ * x * P₁' * (P₁ * y * P₁') = P₁ * (x * y) * P₁' := by
    intro x y
    have : P₁ * x * P₁' * (P₁ * y * P₁') = P₁ * x * (P₁' * P₁) * y * P₁' := by
      simp only [Matrix.mul_assoc]
    rw [this, h12, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hS₁mul : ∀ x ∈ S₁, ∀ y ∈ S₁, x * y ∈ S₁ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hS x hx y hy, (hconj_mul x y).symm⟩
  have hS₁tr : ∀ x ∈ S₁, x.trace ∈ K₀ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h12, Matrix.one_mul]
    exact htr x hx
  have hb₁det : (P₁ * b * P₁').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P₁.det), mul_assoc, ← Matrix.det_mul, h11,
      Matrix.det_one, mul_one, hbdet]
  have hb₁2 : P₁ * b * P₁' * (P₁ * b * P₁') = 1 := by
    rw [hconj_mul, hb2, Matrix.mul_one, h11]
  have hub : uMat * (P₁ * b * P₁') ≠ P₁ * b * P₁' * uMat := by
    rw [← hPa, hconj_mul, hconj_mul]
    intro h
    apply hab
    have h' := congrArg (fun x => P₁' * x * P₁) h
    have e : ∀ x : Matrix (Fin 2) (Fin 2) F, P₁' * (P₁ * x * P₁') * P₁ = x := by
      intro x
      have : P₁' * (P₁ * x * P₁') * P₁ = (P₁' * P₁) * x * (P₁' * P₁) := by
        simp only [Matrix.mul_assoc]
      rw [this, h12, Matrix.one_mul, Matrix.mul_one]
    rwa [e, e] at h'
  obtain ⟨P₂, P₂', h21, h22, hP₂⟩ := exists_conj_entries_of_uMat K₀ S₁ hS₁mul hS₁tr
    ⟨a, ha, hPa⟩ ⟨b, hb, rfl⟩ hb₁det hb₁2 hub
  refine ⟨P₂ * P₁, P₁' * P₂', ?_, ?_, fun x hx i j => ?_⟩
  · rw [show P₂ * P₁ * (P₁' * P₂') = P₂ * (P₁ * P₁') * P₂' by simp only [Matrix.mul_assoc], h11,
      Matrix.mul_one, h21]
  · rw [show P₁' * P₂' * (P₂ * P₁) = P₁' * (P₂' * P₂) * P₁ by simp only [Matrix.mul_assoc], h22,
      Matrix.mul_one, h12]
  · have h := hP₂ _ ⟨x, hx, rfl⟩ i j
    rwa [show P₂ * (P₁ * x * P₁') * P₂' = P₂ * P₁ * x * (P₁' * P₂') by
      simp only [Matrix.mul_assoc]] at h

end Conj

section Dickson

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def powOneSet (M : Subgroup (SpecialLinearGroup (Fin 2) F)) (n : ℕ) :
    Set (SpecialLinearGroup (Fin 2) F) :=
  {m | m ∈ M ∧ m ^ n = 1}

theorem closure_powOneSet_eq (M : Subgroup (SpecialLinearGroup (Fin 2) F)) {n : ℕ}
    (hn : ∀ m ∈ M, m ^ n = 1) : Subgroup.closure (powOneSet M n) = M := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun m hm => hm.1
  · intro m hm
    exact Subgroup.subset_closure ⟨hm, hn m hm⟩

theorem pow_natCard_eq_one (M : Subgroup (SpecialLinearGroup (Fin 2) F)) {m}
    (hm : m ∈ M) : m ^ Nat.card M = 1 := by
  have h := pow_card_eq_one' (G := M) (x := ⟨m, hm⟩)
  exact congrArg Subtype.val h


open CFSG.Glauberman.Dickson in
theorem eq_top_of_dickson (M : Subgroup (SpecialLinearGroup (Fin 2) F)) (hM : M ≠ ⊥)
    (h2 : ∀ n : ℕ, IsPGroup 2 (Subgroup.closure (powOneSet M n)) →
      Subgroup.closure (powOneSet M n) = ⊥)
    (hodd : ∀ n : ℕ, Odd n →
      (∀ x ∈ Subgroup.closure (powOneSet M n), ∀ y ∈ Subgroup.closure (powOneSet M n),
        x * y = y * x) → Subgroup.closure (powOneSet M n) = ⊥)
    (htr : ∀ K₀ : Subfield F, (∀ m ∈ M, (m : Matrix (Fin 2) (Fin 2) F).trace ∈ K₀) →
      (∃ a ∈ M, ∃ b ∈ M, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a) → K₀ = ⊤) :
    M = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f', -, hf'⟩ := FiniteField.card F 2
  set f : ℕ := (f' : ℕ) with hfdef
  have hF : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hf']
  have hf1 : 1 ≤ f := f'.pos
  have hodd1 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_sub_one f hf1
  have hodd2 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_add_one f hf1
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd1.not_two_dvd_nat)
  let ε : SpecialLinearGroup (Fin 2) F →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center _)
  have hε : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact CFSG.Timmesfeld.RankOne.center_SL2_eq_bot F
  set H := M.map ε with hH
  let eM : M ≃* H := Subgroup.equivMapOfInjective M ε hε
  have hcardM : Nat.card H = Nat.card M := (Nat.card_congr eM.toEquiv).symm
  have hfullM := closure_powOneSet_eq M (fun m hm => pow_natCard_eq_one M hm)
  have hcommM : (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) → ¬ Odd (Nat.card M) := by
    intro hc hoddM
    apply hM
    have hc' : ∀ x ∈ Subgroup.closure (powOneSet M (Nat.card M)),
        ∀ y ∈ Subgroup.closure (powOneSet M (Nat.card M)), x * y = y * x := by
      rw [hfullM]
      exact hc
    have h := hodd _ hoddM hc'
    rwa [hfullM] at h
  have hsqM : (∀ m ∈ M, m ^ 2 = 1) → False := by
    intro hsq
    apply hM
    have hP : IsPGroup 2 (Subgroup.closure (powOneSet M 2)) := by
      rw [closure_powOneSet_eq M hsq]
      exact fun x => ⟨1, Subtype.ext (by simpa using hsq x.1 x.2)⟩
    have h := h2 2 hP
    rwa [closure_powOneSet_eq M hsq] at h
  have hinv : 2 ∣ Nat.card M → ∃ a ∈ M, ∃ b ∈ M, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
    intro hev
    by_contra hcon
    push Not at hcon
    have hT : ∀ x ∈ Subgroup.closure (powOneSet M 2), x ∈ M ∧ x * x = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact ⟨hx.1, by rw [← pow_two]; exact hx.2⟩
      | one => exact ⟨M.one_mem, mul_one 1⟩
      | mul x y _ _ hx hy =>
        refine ⟨M.mul_mem hx.1 hy.1, ?_⟩
        have hxy := hcon x hx.1 y hy.1 hx.2 hy.2
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, mul_one]
      | inv x _ hx => exact ⟨M.inv_mem hx.1, by rw [← _root_.mul_inv_rev, hx.2, inv_one]⟩
    have hP : IsPGroup 2 (Subgroup.closure (powOneSet M 2)) := fun x =>
      ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using (hT x.1 x.2).2)⟩
    have hbot := h2 2 hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 hev
    have hx2 : (x : SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      exact congrArg Subtype.val h
    have hxT : (x : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.closure (powOneSet M 2) :=
      Subgroup.subset_closure ⟨x.2, hx2⟩
    rw [hbot, Subgroup.mem_bot] at hxT
    have hx1 : x = 1 := Subtype.ext hxT
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hsqrt : ∀ (K₀ : Subfield F) (z : F), z ^ 2 ∈ K₀ → z ∈ K₀ := fun K₀ z hz =>
    CFSG.Quasithin.SimsG4.mem_of_sq_mem_subfield K₀ hz
  have htop : ∀ q : ℕ, Nat.card F = q → Nat.card M = q * (q ^ 2 - 1) → M = ⊤ := by
    intro q hq hMq
    apply Subgroup.eq_top_of_card_eq
    rw [hMq, CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hq]
  have hcard_top : ∀ K₀ : Subfield F, K₀ = ⊤ → Nat.card K₀ = Nat.card F := by
    rintro K₀ rfl
    exact Nat.card_congr Subfield.topEquiv.toEquiv
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := 2) (f := f) hF
      H with
    hEl | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz, hcard, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨eA5⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨Wt⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨Wt⟩⟩
  ·
    exfalso
    apply hsqM
    intro x hx
    haveI := hEl
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := H) (ε x) ⟨x, hx, rfl⟩
    apply hε
    rw [map_pow, h, map_one]
  ·
    exfalso
    rw [hF, hg, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z :=
      hz.elim (fun h => Odd.of_dvd_nat hodd1 h) (fun h => Odd.of_dvd_nat hodd2 h)
    have : IsCyclic H := hcyc
    refine hcommM (fun x hx y hy => ?_) (by rw [← hcardM, hcard]; exact hzodd)
    have h := (IsCyclic.isMulCommutative (α := H)).is_comm.comm (eM ⟨x, hx⟩) (eM ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (eM.injective h)
  ·
    exfalso
    rw [hF, hg, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z :=
      hz.elim (fun h => Odd.of_dvd_nat hodd1 h) (fun h => Odd.of_dvd_nat hodd2 h)
    by_cases hz1 : z = 1
    · apply hsqM
      intro x hx
      have h2M : Nat.card M = 2 := by rw [← hcardM, hcard, hz1]
      have := pow_natCard_eq_one M hx
      rwa [h2M] at this
    · let ψ : M ≃* DihedralGroup z := eM.trans eD
      have hrot : ∀ x ∈ Subgroup.closure (powOneSet M z), ∃ hx : x ∈ M, ∃ i : ZMod z,
          ψ ⟨x, hx⟩ = DihedralGroup.r i := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          refine ⟨hx.1, ?_⟩
          have hpow : ψ ⟨x, hx.1⟩ ^ z = 1 := by
            rw [← map_pow]
            have : (⟨x, hx.1⟩ : M) ^ z = 1 := Subtype.ext hx.2
            rw [this, map_one]
          rcases h : ψ ⟨x, hx.1⟩ with i | i
          · exact ⟨i, rfl⟩
          · exfalso
            rw [h] at hpow
            have hdvd := orderOf_dvd_of_pow_eq_one hpow
            rw [DihedralGroup.orderOf_sr] at hdvd
            exact (Nat.not_even_iff_odd.mpr hzodd) (even_iff_two_dvd.mpr hdvd)
        | one => exact ⟨M.one_mem, 0, by rw [show (⟨1, M.one_mem⟩ : M) = 1 from rfl, map_one,
            DihedralGroup.one_def]⟩
        | mul x y _ _ hx hy =>
          obtain ⟨hxM, i, hi⟩ := hx
          obtain ⟨hyM, j, hj⟩ := hy
          refine ⟨M.mul_mem hxM hyM, i + j, ?_⟩
          rw [show (⟨x * y, M.mul_mem hxM hyM⟩ : M) = ⟨x, hxM⟩ * ⟨y, hyM⟩ from rfl, map_mul, hi,
            hj, DihedralGroup.r_mul_r]
        | inv x _ hx =>
          obtain ⟨hxM, i, hi⟩ := hx
          refine ⟨M.inv_mem hxM, -i, ?_⟩
          rw [show (⟨x⁻¹, M.inv_mem hxM⟩ : M) = (⟨x, hxM⟩)⁻¹ from rfl, map_inv, hi,
            DihedralGroup.inv_r]
      have hcl := hodd z hzodd (fun x hx y hy => by
        obtain ⟨hxM, i, hi⟩ := hrot x hx
        obtain ⟨hyM, j, hj⟩ := hrot y hy
        have h : ψ (⟨x, hxM⟩ * ⟨y, hyM⟩) = ψ (⟨y, hyM⟩ * ⟨x, hxM⟩) := by
          rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
        exact congrArg Subtype.val (ψ.injective h))
      set m₁ : M := ψ.symm (DihedralGroup.r 1) with hm₁
      have hm₁z : (m₁ : SpecialLinearGroup (Fin 2) F) ^ z = 1 := by
        have h : m₁ ^ z = 1 := by
          rw [hm₁, ← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_self, ← DihedralGroup.one_def,
            map_one]
        exact congrArg Subtype.val h
      have hmem : (m₁ : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.closure (powOneSet M z) :=
        Subgroup.subset_closure ⟨m₁.2, hm₁z⟩
      rw [hcl, Subgroup.mem_bot] at hmem
      have h1 : m₁ = 1 := Subtype.ext hmem
      have h2' : (DihedralGroup.r 1 : DihedralGroup z) = 1 := by
        rw [← ψ.apply_symm_apply (DihedralGroup.r 1), ← hm₁, h1, map_one]
      have hord := DihedralGroup.orderOf_r_one (n := z)
      rw [h2', orderOf_one] at hord
      exact hz1 hord.symm
  ·
    exfalso
    have h12 : Nat.card M = 12 := by
      rw [← hcardM, Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := hinv (by rw [h12]; norm_num)
    apply hab
    let ψ : M ≃* alternatingGroup (Fin 4) := eM.trans eA4
    have h := CFSG.GH74.Uniqueness.Bender.A4_involutions_commute (ψ ⟨a, ha⟩) (ψ ⟨b, hb⟩)
      (by rw [← map_mul, show (⟨a, ha⟩ : M) * ⟨a, ha⟩ = 1 from Subtype.ext ha2, map_one])
      (by rw [← map_mul, show (⟨b, hb⟩ : M) * ⟨b, hb⟩ = 1 from Subtype.ext hb2, map_one])
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (ψ.injective h)
  ·
    exact absurd h16 (CFSG.GH74.Uniqueness.Bender.not_sixteen_dvd f hf1)
  ·
    have h60 : Nat.card M = 60 := by
      rw [← hcardM, Nat.card_congr eA5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have htr4 : ∀ x ∈ M, (x : Matrix (Fin 2) (Fin 2) F).trace ∈
        CFSG.Glauberman.Dickson.MaxSubfield.fixField F 2 2 := by
      intro x hx
      have hmk : ∀ n : ℕ, x ^ n = 1 → CFSG.PSL2Table.mk x ^ n = 1 := fun n h => by
        rw [← map_pow, h, map_one]
      rcases CFSG.Glauberman.Dickson.MaxCases.pow_of_mulEquiv_alternatingFive (eM.trans eA5) hx
        with h | h | h
      · exact CFSG.Glauberman.Dickson.MaxTrace.trace_mem_of_pow_two _ (hmk 2 h)
      · exact CFSG.Glauberman.Dickson.MaxTrace.trace_mem_of_pow_three _ (hmk 3 h)
      · exact CFSG.Glauberman.Dickson.MaxTrace.trace_mem_fixField_two_of_pow_five (hmk 5 h)
    have hK := htr _ htr4 (hinv (by rw [h60]; norm_num))
    have hfe : Even f := CFSG.GH74.Uniqueness.Bender.even_of_five_dvd f
      (h5.resolve_left (by norm_num))
    have h4 := CFSG.Glauberman.Dickson.MaxSubfield.card_fixField hF (k := 2)
      (even_iff_two_dvd.mp hfe) (by norm_num)
    rw [hcard_top _ hK] at h4
    exact htop 4 (by rw [h4]; norm_num) (by rw [h60]; norm_num)
  ·
    exfalso
    have htodd : Odd t :=
      Odd.of_dvd_nat hodd1 (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have hCodd : Odd (Nat.card C) := hCcard ▸ htodd
    have hnc : ¬ ∃ a ∈ M, ∃ b ∈ M, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
      rintro ⟨a, ha, b, hb, ha2, hb2, hab⟩
      apply hab
      have haN := CFSG.Quasithin.SimsG4.mem_of_mul_self_eq_one_of_sup hN hdisj hsup hCodd
        (g := eM ⟨a, ha⟩) (by rw [← map_mul, show (⟨a, ha⟩ : M) * ⟨a, ha⟩ = 1 from
          Subtype.ext ha2, map_one])
      have hbN := CFSG.Quasithin.SimsG4.mem_of_mul_self_eq_one_of_sup hN hdisj hsup hCodd
        (g := eM ⟨b, hb⟩) (by rw [← map_mul, show (⟨b, hb⟩ : M) * ⟨b, hb⟩ = 1 from
          Subtype.ext hb2, map_one])
      have h := congrArg Subtype.val
        (hNel.toIsMulCommutative.is_comm.comm (⟨_, haN⟩ : N) ⟨_, hbN⟩)
      simp only [Subgroup.coe_mul] at h
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (eM.injective h)
    have hModd : ¬ 2 ∣ Nat.card M := fun h => hnc (hinv h)
    have hNbot : N = ⊥ := by
      have hdvd : Nat.card N ∣ Nat.card H := Subgroup.card_subgroup_dvd_card N
      rw [hNcard, hcardM] at hdvd
      rcases m' with _ | m'
      · rw [pow_zero] at hNcard
        exact Subgroup.eq_bot_of_card_eq N hNcard
      · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero m')).trans hdvd) hModd
    rw [hNbot, bot_sup_eq] at hsup
    have : IsCyclic H := by
      have hCH : IsCyclic (⊤ : Subgroup H) := hsup ▸ hCcyc
      exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective
    refine hcommM (fun x hx y hy => ?_) (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hModd))
    have h := (IsCyclic.isMulCommutative (α := H)).is_comm.comm (eM ⟨x, hx⟩) (eM ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (eM.injective h)
  ·
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hcardP : Nat.card M = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [← hcardM, Nat.card_congr eP.toEquiv, CFSG.GH74.Uniqueness.Bender.card_psl2_even m hm1]
    have htrW : ∀ x ∈ M, (x : Matrix (Fin 2) (Fin 2) F).trace ∈ Wt.K := fun x hx =>
      hsqrt _ _ (CFSG.HardMathSupport.Solomon.Coordinator.BGL.trace_sq_mem_of_witness H Wt x
        ⟨x, hx, rfl⟩)
    have hK := htr _ htrW (hinv (by
      rw [hcardP]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 hm0) _))
    have hWc := Wt.card_eq
    rw [hcard_top _ hK] at hWc
    exact htop (2 ^ m) hWc hcardP
  ·
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hcardP : Nat.card M = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [← hcardM, Nat.card_congr eP.toEquiv, CFSG.BenderSuzuki.External.huppertXI13_card_pgl2,
        GaloisField.card 2 m hm0]
    have htrW : ∀ x ∈ M, (x : Matrix (Fin 2) (Fin 2) F).trace ∈ Wt.K := fun x hx =>
      hsqrt _ _ (CFSG.HardMathSupport.Solomon.Coordinator.BGL.trace_sq_mem_of_witness H Wt x
        ⟨x, hx, rfl⟩)
    have hK := htr _ htrW (hinv (by
      rw [hcardP]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 hm0) _))
    have hWc := Wt.card_eq
    rw [hcard_top _ hK] at hWc
    exact htop (2 ^ m) hWc hcardP

end Dickson

end CFSG.Quasithin.SimsG4.OrthMinus
