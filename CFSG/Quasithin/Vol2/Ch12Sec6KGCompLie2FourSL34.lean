module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigCov
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.FiveTransitive.CharacteristicAutomorphism (quotient quotient_apply_mk)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

section Mat

open Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem exists_commute_of_commute_wM (hF : Nat.card F = 4) {A : Matrix (Fin 3) (Fin 3) F}
    (hT : A * LinearFieldFour.wM (1 : F) = LinearFieldFour.wM (1 : F) * A)
    (h3 : ∃ s : F, A ^ 3 = Matrix.scalar (Fin 3) s) (hdet0 : A.det ≠ 0) (hdet : A.det ≠ 1) :
    ∃ y : Matrix (Fin 3) (Fin 3) F, y.det = 1 ∧ y ^ 3 = 1 ∧ y * A = A * y ∧ y 0 0 ≠ y 1 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have := LinearFieldFour.finite_of_card_eq_four hF
  have hE : ∀ i j, (A * LinearFieldFour.wM (1 : F)) i j = (LinearFieldFour.wM (1 : F) * A) i j :=
    fun i j => by rw [hT]
  have e02 := hE 0 2
  have e12 := hE 1 2
  have e22 := hE 2 2
  have e01 := hE 0 1
  simp [LinearFieldFour.wM, Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e22 e01
  set l := A 0 0 with hl
  set m := A 1 1 with hm
  set a := A 0 1 with ha
  set b := A 0 2 with hb
  set d := A 1 2 with hd
  have hA : A = !![l, a, b; 0, m, d; 0, 0, l] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hl, hm, ha, hb, hd] <;>
      first
        | rfl
        | linear_combination e12
        | linear_combination e22
        | linear_combination e01
        | linear_combination -e02
  obtain ⟨s, hs⟩ := h3
  have hc : ∀ i j, (A * A * A) i j = Matrix.scalar (Fin 3) s i j := fun i j => by
    rw [show A * A * A = A ^ 3 by rw [pow_succ, sq], hs]
  have c00 := hc 0 0
  have c11 := hc 1 1
  have c02 := hc 0 2
  rw [hA] at c00 c11 c02 hdet hdet0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at c00 c11 c02
  rw [Matrix.det_fin_three] at hdet hdet0
  simp at hdet hdet0
  have hl0 : l ≠ 0 := hdet0.2
  have hl3 : l ^ 3 = 1 := LinearFieldFour.pow_three_eq_one hF hl0
  have hs1 : s = 1 := by rw [← c00, ← hl3]; ring
  rw [hs1] at c00 c11
  have hlm : l ≠ m := by
    intro h
    exact hdet (by rw [← h]; linear_combination c00)
  have hlm' : l + m ≠ 0 := by
    intro h
    apply hlm
    linear_combination h - m * h2
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at c11
    simp at c11
  have hq : l * l + l * m + m * m = 0 := by
    have h1 : (l + m) * (l * l + l * m + m * m) = 0 := by
      linear_combination c00 + c11 + (1 + l * l * m + l * m * m) * h2
    exact (mul_eq_zero.mp h1).resolve_left hlm'
  have hrel : a * d + b * (l + m) = 0 := by
    have h1 : m * (a * d + b * (l + m)) = 0 := by
      linear_combination c02 + b * hq - (2 * l * l * b + l * a * d) * h2
    exact (mul_eq_zero.mp h1).resolve_left hm0
  obtain ⟨ω, hω1⟩ : ∃ ω : Fˣ, ω ≠ 1 := by
    have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [LinearThreeFourOuter.card_units_eq_three hF]; norm_num)
    exact exists_ne 1
  have hω3 := LinearThreeFourOuter.units_pow_three hF ω
  have hw3 : (ω : F) * ((ω : F) * ω) = 1 := by
    have := congrArg Units.val hω3
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    linear_combination this
  obtain ⟨u, hu'⟩ : ∃ u, u * (l + m) = a := ⟨a / (l + m), by field_simp⟩
  obtain ⟨t, ht'⟩ : ∃ t, t * (l + m) = d := ⟨d / (l + m), by field_simp⟩
  set P : Matrix (Fin 3) (Fin 3) F := !![1, u, 0; 0, 1, t; 0, 0, 1] with hP
  set Pi : Matrix (Fin 3) (Fin 3) F := !![1, u, u * t; 0, 1, t; 0, 0, 1] with hPi
  set D : Matrix (Fin 3) (Fin 3) F := !![(ω : F), 0, 0; 0, ω * ω, 0; 0, 0, 1] with hD
  set Λ : Matrix (Fin 3) (Fin 3) F := !![l, 0, 0; 0, m, 0; 0, 0, l] with hΛ
  have hPPi : P * Pi = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination u * h2
        | linear_combination (u * t) * h2
        | linear_combination t * h2
  have hPiP : Pi * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination u * h2
        | linear_combination (u * t) * h2
        | linear_combination t * h2
  have hAP : A * P = P * Λ := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hΛ, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination -hu' + (u * l) * h2
    · have : a * t + b = 0 := by
        have h1 : (l + m) * (a * t + b) = 0 := by linear_combination a * ht' + hrel
        exact (mul_eq_zero.mp h1).resolve_left hlm'
      exact this
    · linear_combination -ht' + (m * t) * h2
  have hDΛ : D * Λ = Λ * D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, hΛ, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]
  have hPiA : Pi * A = Λ * Pi := by
    calc Pi * A = Pi * A * (P * Pi) := by rw [hPPi, Matrix.mul_one]
      _ = Pi * (A * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * (P * Λ) * Pi := by rw [hAP]
      _ = (Pi * P) * Λ * Pi := by simp only [Matrix.mul_assoc]
      _ = Λ * Pi := by rw [hPiP, Matrix.one_mul]
  refine ⟨P * D * Pi, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fin_three P, Matrix.det_fin_three D,
      Matrix.det_fin_three Pi]
    simp [hP, hD, hPi]
    linear_combination hw3
  · have hD3 : D * D * D = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first
          | linear_combination hw3
          | linear_combination ((ω : F) * (ω * ω) + 1) * hw3
    calc (P * D * Pi) ^ 3 = P * D * (Pi * P) * D * (Pi * P) * D * Pi := by
          simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
      _ = P * (D * D * D) * Pi := by rw [hPiP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hD3, Matrix.mul_one, hPPi]
  · calc P * D * Pi * A = P * D * (Pi * A) := by simp only [Matrix.mul_assoc]
      _ = P * (D * Λ) * Pi := by rw [hPiA]; simp only [Matrix.mul_assoc]
      _ = P * (Λ * D) * Pi := by rw [hDΛ]
      _ = (P * Λ) * D * Pi := by simp only [Matrix.mul_assoc]
      _ = A * P * D * Pi := by rw [hAP]
      _ = A * (P * D * Pi) := by simp only [Matrix.mul_assoc]
  · simp [hP, hD, hPi, Matrix.mul_apply, Fin.sum_univ_three]
    exact hω1

theorem exists_fix_slConjugation (hF : Nat.card F = 4) {A : GL (Fin 3) F}
    (hdet : GeneralLinearGroup.det A ≠ 1)
    (h3 : ∃ u : Fˣ, A ^ 3 = GeneralLinearGroup.scalar (Fin 3) u)
    {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (hfix : slConjugation 3 F A (g⁻¹ * LinearFieldFour.wMat 1 * g) =
      g⁻¹ * LinearFieldFour.wMat 1 * g) :
    ∃ y : Matrix.SpecialLinearGroup (Fin 3) F, y ^ 3 = 1 ∧
      y ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
      slConjugation 3 F A y = y := by
  set gm := ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgm
  set gi := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgi
  have hgg : gm * gi = 1 := by
    rw [hgm, hgi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hgg' : gi * gm = 1 := by
    rw [hgm, hgi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  set Am := ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hAm
  set Ai := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hAi
  have hAA : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set W := LinearFieldFour.wM (1 : F) with hW
  have hfix' : Am * (gi * W * gm) * Ai = gi * W * gm := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
      (x : Matrix (Fin 3) (Fin 3) F)) hfix
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have hcomm : Am * (gi * W * gm) = (gi * W * gm) * Am := by
    calc Am * (gi * W * gm) = Am * (gi * W * gm) * (Ai * Am) := by rw [hAA', Matrix.mul_one]
      _ = (Am * (gi * W * gm) * Ai) * Am := by simp only [Matrix.mul_assoc]
      _ = (gi * W * gm) * Am := by rw [hfix']
  set A' := gm * Am * gi with hA'
  have hT : A' * W = W * A' := by
    calc A' * W = gm * Am * gi * W * (gm * gi) := by rw [hgg, Matrix.mul_one]
      _ = gm * (Am * (gi * W * gm)) * gi := by simp only [Matrix.mul_assoc]
      _ = gm * ((gi * W * gm) * Am) * gi := by rw [hcomm]
      _ = (gm * gi) * W * (gm * Am * gi) := by simp only [Matrix.mul_assoc]
      _ = W * A' := by rw [hgg, Matrix.one_mul]
  have h3' : ∃ s : F, A' ^ 3 = Matrix.scalar (Fin 3) s := by
    obtain ⟨u, hu⟩ := h3
    refine ⟨(u : F), ?_⟩
    have hu' : Am * Am * Am = Matrix.scalar (Fin 3) (u : F) := by
      have := congrArg Units.val hu
      rw [pow_succ, sq, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
      exact this
    calc A' ^ 3 = gm * (Am * Am * Am) * gi := by
          rw [hA', pow_succ, sq]
          calc gm * Am * gi * (gm * Am * gi) * (gm * Am * gi) =
              gm * Am * (gi * gm) * Am * (gi * gm) * Am * gi := by simp only [Matrix.mul_assoc]
            _ = gm * (Am * Am * Am) * gi := by
              rw [hgg']
              simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Matrix.scalar (Fin 3) (u : F) := by
          rw [hu', Matrix.scalar_apply, Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul,
            Matrix.mul_smul, hgg, Matrix.smul_one_eq_diagonal]
  have hdetA : Am.det ≠ 1 := by
    rwa [hAm, ← GeneralLinearGroup.val_det_apply, Ne, Units.val_eq_one]
  have hdetA0 : Am.det ≠ 0 := by
    rw [hAm, ← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdg : gm.det * gi.det = 1 := by rw [← Matrix.det_mul, hgg, Matrix.det_one]
  have hdet' : A'.det = Am.det := by
    rw [hA', Matrix.det_mul, Matrix.det_mul]
    linear_combination Am.det * hdg
  obtain ⟨y', hy'1, hy'3, hy'A, hy'00⟩ := exists_commute_of_commute_wM hF hT h3'
    (by rw [hdet']; exact hdetA0) (by rw [hdet']; exact hdetA)
  have hydet : (gi * y' * gm).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hy'1, mul_one, mul_comm]
    linear_combination hdg
  let y : Matrix.SpecialLinearGroup (Fin 3) F := ⟨gi * y' * gm, hydet⟩
  have hy : (y : Matrix (Fin 3) (Fin 3) F) = gi * y' * gm := rfl
  refine ⟨y, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hy]
    calc (gi * y' * gm) ^ 3 = gi * y' * (gm * gi) * y' * (gm * gi) * y' * gm := by
          rw [pow_succ, sq]; simp only [Matrix.mul_assoc]
      _ = gi * y' ^ 3 * gm := by
          rw [hgg, pow_succ, sq]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hy'3, Matrix.mul_one, hgg']
  · intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hr' : gi * y' * gm = Matrix.scalar (Fin 3) r := by
      rw [← hy]
      exact hr.symm
    have hy'r : y' = Matrix.scalar (Fin 3) r := by
      calc y' = (gm * gi) * y' * (gm * gi) := by rw [hgg, Matrix.one_mul, Matrix.mul_one]
        _ = gm * (gi * y' * gm) * gi := by simp only [Matrix.mul_assoc]
        _ = Matrix.scalar (Fin 3) r := by
          rw [hr', Matrix.scalar_apply, Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul,
            Matrix.mul_smul, hgg, Matrix.smul_one_eq_diagonal]
    apply hy'00
    rw [hy'r]
    simp
  · apply Subtype.ext
    rw [coe_slConjugation, hy]
    have hc2 : Am * (gi * y' * gm) = (gi * y' * gm) * Am := by
      have e1 : gi * (gm * Am * gi * y') * gm = gi * (y' * (gm * Am * gi)) * gm := by
        rw [hy'A]
      calc Am * (gi * y' * gm) = (gi * gm) * Am * gi * y' * gm := by
            rw [hgg', Matrix.one_mul]; simp only [Matrix.mul_assoc]
        _ = gi * (gm * Am * gi * y') * gm := by simp only [Matrix.mul_assoc]
        _ = gi * (y' * (gm * Am * gi)) * gm := e1
        _ = gi * y' * gm * Am * (gi * gm) := by simp only [Matrix.mul_assoc]
        _ = (gi * y' * gm) * Am := by rw [hgg', Matrix.mul_one]
    rw [hc2, Matrix.mul_assoc, hAA, Matrix.mul_one]

end Mat

section E27

variable {Q : Type} [Group Q]

theorem false_of_commute_e9 (hQ : Vol2Native.SQTKHypCat Q) {E : Subgroup Q}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {p : Q} (hp3 : p ^ 3 = 1) (hpE : p ∉ E)
    (hpc : ∀ e ∈ E, p * e = e * p) : False := by
  have := hQ.finite
  have hp1 : p ≠ 1 := fun h1 => hpE (h1 ▸ one_mem E)
  have hop : orderOf p = 3 := orderOf_eq_prime hp3 hp1
  have hcomm : ∀ (a : ↥E) (b : ↥(Subgroup.zpowers p)),
      Commute (E.subtype a) ((Subgroup.zpowers p).subtype b) := by
    intro a b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : Q) (b : Q)
    rw [← hn]
    exact (Commute.zpow_right (hpc a a.2).symm n)
  let f : ↥E × ↥(Subgroup.zpowers p) →* Q :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers p).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Q) * b = 1 := hab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hbE : (b : Q) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hab']
      exact inv_mem a.2
    have hb1 : (b : Q) = 1 := by
      by_contra hb1
      apply hpE
      have h3n : ¬ (3 : ℤ) ∣ n := by
        intro hd
        obtain ⟨m, rfl⟩ := hd
        apply hb1
        rw [← hn, zpow_mul, show (p ^ (3 : ℤ)) = p ^ 3 from zpow_natCast p 3, hp3, one_zpow]
      have hsq : p = (p ^ n) ^ n := by
        rw [← zpow_mul, ← zpow_mod_orderOf, hop]
        conv_lhs => rw [← zpow_one p]
        congr 1
        push_cast
        have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h1 with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
      rw [hsq]
      exact zpow_mem (hn ▸ hbE) n
    have ha1 : (a : Q) = 1 := by rw [hb1, mul_one] at hab'; exact hab'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcard : Nat.card (↥E × ↥(Subgroup.zpowers p)) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_zpowers, hop, hE9]
    norm_num
  have hA := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (A := ↥E × ↥(Subgroup.zpowers p))
    (fun a b => Prod.ext (hE.1.is_comm.comm a.1 b.1)
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
        change (a.2 : Q) * b.2 = b.2 * a.2
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm])))
    (fun a => Prod.ext (Subtype.ext (by
        change ((a.1 : Q)) ^ 3 = 1
        exact hE.2 _ a.1.2))
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        change ((a.2 : Q)) ^ 3 = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3, one_zpow])))
    hcard f hf (H := ⊤) le_top
  have h2 := hQ.sqt 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

end E27

section SL34

variable {F : Type} [Field F]

theorem false_of_autConf_l34_of_conj (hF : Nat.card F = 4) {ν : MulAut (projectiveSL 3 F)}
    {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))} (h : AutConf (projectiveSL 3 F) ν Lb Pb)
    {c : projectiveSL 3 F} (hc1 : c ≠ 1) (hcP : MulAut.conj c ∈ Pb) : False := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  have hZ := LinearThreeFourOuter.center_projectiveSL_three_eq_bot hF
  have hcj := conj_injective_of_center_eq_bot hZ
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.sylowCentralizingAutInner_projectiveSL
    (K := F) (le_refl 3) S hS ν hSν
  have hν : ν = MulAut.conj x⁻¹ := MulEquiv.ext fun y => by
    rw [hx, MulAut.conj_apply, inv_inv]
  subst hν
  have hz2 : orderOf x⁻¹ = 2 := by
    refine orderOf_eq_prime (hcj ?_) fun h1 => h.ne_one (by rw [h1, map_one])
    rw [map_pow, h.sq, map_one]
  have hc3 : orderOf c = 3 := by
    refine orderOf_eq_prime (hcj ?_) hc1
    rw [map_pow, h.elem.2 _ hcP, map_one]
  have hfix := h.fix_of_mem_innerPart hZ (show c ∈ innerPart Lb from h.le hcP)
  rw [MulAut.conj_apply] at hfix
  refine CFSG.RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hF hc3 hz2 ?_
  calc c * x⁻¹ = x⁻¹ * c * x⁻¹⁻¹ * x⁻¹ := by rw [hfix]
    _ = x⁻¹ * c := by group

end SL34

section Main

variable {F : Type} [Field F]

theorem quotient_scalars_eq_descendAut [(scalars 3 F).Characteristic]
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) :
    quotient (scalars 3 F) α = descendAut 3 F α := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [descendAut_proj]
  exact quotient_apply_mk (scalars 3 F) α g

theorem exists_E9_sl34 (hF : Nat.card F = 4) :
    ∃ E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have hinj : Function.Injective (LinearThreeFourFixedNine.dHom (k := F)) := by
    intro p q hpq
    have h' := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
      (x : Matrix (Fin 3) (Fin 3) F)) hpq
    simp only [LinearThreeFourFixedNine.coe_dHom] at h'
    have h0 := congrFun (congrFun h' 0) 0
    have h1 := congrFun (congrFun h' 1) 1
    simp at h0 h1
    exact Prod.ext (Units.ext h0) (Units.ext h1)
  refine ⟨(LinearThreeFourFixedNine.dHom (k := F)).range, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩,
    fun x hx => ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := a.2
    obtain ⟨q, hq⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨p, rfl⟩ := hx
    rw [← map_pow, show p ^ 3 = 1 from Prod.ext (LinearThreeFourOuter.units_pow_three hF _)
      (LinearThreeFourOuter.units_pow_three hF _), map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_prod, LinearThreeFourOuter.card_units_eq_three hF]

theorem not_sl34 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) : ¬ IsSLEps3 true 4 ↥K := by
  intro hK
  have := hQ.finite
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hK
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  let e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e₀.trans (specialLinearGroupEquivStatedSL 3 F).symm
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  have hNc : scalars 3 F ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (scalars_eq_center 3 F).le
  have : (scalars 3 F).Characteristic := by rw [scalars_eq_center]; infer_instance
  have hodd : Odd (Nat.card (scalars 3 F)) := odd_card_of_pow_three fun z => Subtype.ext (by
    rw [Subgroup.coe_pow, pow_three_of_mem_center_sl3 (hNc z.2), Subgroup.coe_one])
  have hbar := (h.autConf.map e).descend hNc hodd
  have hZ := LinearThreeFourOuter.center_projectiveSL_three_eq_bot hF
  have hcj := conj_injective_of_center_eq_bot hZ
  set Pib := (h.rhoP.range.map (MulAut.congr e).toMonoidHom).map (quotient (scalars 3 F))
    with hPib
  by_cases hc : ∃ c : projectiveSL 3 F, c ≠ 1 ∧ MulAut.conj c ∈ Pib
  · obtain ⟨c, hc1, hcP⟩ := hc
    exact false_of_autConf_l34_of_conj hF hbar hc1 hcP
  push Not at hc
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_E9_sl34 hF
  set EK : Subgroup Q := (E₀.map e.symm.toMonoidHom).map K.subtype with hEK
  have hEKK : EK ≤ K := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hEKe : IsElemAbelian 3 EK :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE₀ _) _
  have hEK9 : Nat.card EK = 9 := by
    rw [hEK, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hE₀9]
  obtain ⟨p, hpP, hpc⟩ : ∃ p ∈ P, ¬ ∀ k ∈ K, p * k = k * p := by
    by_contra hall
    push Not at hall
    have hmem := fun (x : ↥P) => h.mem_center_of_centralizes hQ hEKK hEKe hEK9 x.2 (hall x x.2)
    let f : ↥P → ↥(Subgroup.center ↥K) := fun x => ⟨⟨x, (hmem x).1⟩, (hmem x).2⟩
    have hf : Function.Injective f := fun a b hab => Subtype.ext (by
      have := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : Q)) hab
      exact this)
    have h1 := Nat.card_le_card_of_injective f hf
    let g : ↥(Subgroup.center ↥K) → ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
      fun z => ⟨e z, by
        rw [Subgroup.mem_center_iff]
        intro y
        rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2]⟩
    have hg : Function.Injective g := fun a b hab => Subtype.ext (e.injective (by
      have := congrArg Subtype.val hab
      exact this))
    have h2 := Nat.card_le_card_of_injective g hg
    have h3 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ 3 := by
      rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
      exact (card_rootsOfUnity F _).trans (by simp)
    rw [h.P_card] at h1
    omega
  set π := h.rhoP ⟨p, hpP⟩ with hπdef
  have hπk : ∀ k : ↥K, ((π k : ↥K) : Q) = p * k * p⁻¹ := fun k => rfl
  have hπ1 : π ≠ 1 := by
    intro h1
    apply hpc
    intro k hk
    have := hπk ⟨k, hk⟩
    rw [h1, MulAut.one_apply] at this
    calc p * k = p * k * p⁻¹ * p := by group
      _ = k * p := by rw [← this]
  set π' := MulAut.congr e π with hπ'def
  set πb := quotient (scalars 3 F) π' with hπbdef
  have hπb1 : πb ≠ 1 := fun h1 => hπ1 ((MulAut.congr e).injective
    (quotient_injective hNc (h1.trans (map_one _).symm) |>.trans (map_one _).symm))
  have hπbP : πb ∈ Pib := ⟨π', ⟨π, ⟨⟨p, hpP⟩, rfl⟩, rfl⟩, rfl⟩
  have hnot : ∀ c : projectiveSL 3 F, MulAut.conj c ≠ πb := by
    intro c hcπ
    have hc1 : c ≠ 1 := fun h1 => hπb1 (by rw [← hcπ, h1, map_one])
    exact hc c hc1 (hcπ ▸ hπbP)
  have hπb3 : πb ^ 3 = 1 := hbar.elem.2 πb hπbP
  have hσ : ∀ a, frobeniusEquiv F 2 a = a ^ 2 := fun a => frobeniusEquiv_apply F 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hF
  obtain ⟨⟨A, a, b⟩, hnf⟩ := LinearThreeFourOuter.exists_nf hσ hF πb
  have hab : a = 0 ∧ b = 0 := by
    have h3 : Ψ πb ^ 3 = 1 := by rw [← map_pow, hπb3, map_one]
    rw [hnf, hΨ] at h3
    have hr := congrArg SemidirectProduct.rightHom h3
    rw [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at hr
    change ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 at hr
    have key : ∀ a b : ZMod 2, ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) :
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 3 = 1 → a = 0 ∧ b = 0 := by
      decide
    exact key a b hr
  obtain ⟨rfl, rfl⟩ := hab
  rw [LinearThreeFourOuter.nf_zero_zero] at hnf
  have hdetA : Matrix.GeneralLinearGroup.det A ≠ 1 := fun h1 => by
    obtain ⟨c, hc⟩ := (LinearThreeFourOuter.conjAut_mem_range_conj_iff hF A).mpr h1
    exact hnot c (hc.trans hnf.symm)
  have hA3 : ∃ u : Fˣ, A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    have : Finite F := inferInstance
    refine (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff le_rfl
      (A ^ 3)).mp ?_
    rw [map_pow, ← hnf, hπb3]
  have hφ : π' = slConjugation 3 F A := by
    apply CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := F) le_rfl
    rw [← quotient_scalars_eq_descendAut, ← hπbdef, hnf]
    rfl
  obtain ⟨S, hS, hSν⟩ := hbar.sylow
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.sylowCentralizingAutInner_projectiveSL
    (K := F) (le_refl 3) S hS _ hSν
  set νb := quotient (scalars 3 F) (MulAut.congr e h.nu) with hνb
  have hνbx : νb = MulAut.conj x⁻¹ := MulEquiv.ext fun y => by
    rw [hx, MulAut.conj_apply, inv_inv]
  have hz2 : x⁻¹ * x⁻¹ = 1 := hcj (by rw [map_mul, ← sq, ← hνbx, hbar.sq, map_one])
  have hz1 : x⁻¹ ≠ 1 := fun h1 => hbar.ne_one (by rw [hνbx, h1, map_one])
  have hπz : πb x⁻¹ = x⁻¹ := by
    have hcomm := hbar.comm πb (hbar.le hπbP)
    rw [hνbx] at hcomm
    apply hcj
    refine MulEquiv.ext fun w => ?_
    have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (πb.symm w)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at this
    rw [MulAut.conj_apply, MulAut.conj_apply, ← this, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    simp only [map_inv]
  obtain ⟨g, hg⟩ := LinearFieldFour.exists_conj_eq_wP_one x⁻¹ hz2 hz1
  have hxg : x⁻¹ = proj 3 F (g⁻¹ * LinearFieldFour.wMat 1 * g) := by
    rw [map_mul, map_mul, map_inv, ← LinearFieldFour.wP, ← hg]
    group
  have hW2 : LinearFieldFour.wMat (1 : F) * LinearFieldFour.wMat 1 = 1 := by
    rw [← LinearFieldFour.wMat_add, CharTwo.add_self_eq_zero]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.wMat, LinearFieldFour.wM]
  have hgW2 : (g⁻¹ * LinearFieldFour.wMat 1 * g) * (g⁻¹ * LinearFieldFour.wMat 1 * g) = 1 := by
    calc (g⁻¹ * LinearFieldFour.wMat 1 * g) * (g⁻¹ * LinearFieldFour.wMat 1 * g) =
        g⁻¹ * (LinearFieldFour.wMat 1 * LinearFieldFour.wMat 1) * g := by group
      _ = 1 := by rw [hW2]; group
  have hfix : slConjugation 3 F A (g⁻¹ * LinearFieldFour.wMat 1 * g) =
      g⁻¹ * LinearFieldFour.wMat 1 * g := by
    refine CFSG.QuasithinUnique.K1.eq_of_proj_eq_of_mul_self_eq_one (by norm_num)
      (by rw [← map_mul, hgW2, map_one]) hgW2 ?_
    rw [← conjAut_proj, ← hxg, ← hnf, hπz]
  obtain ⟨y, hy3, hyZ, hyA⟩ := exists_fix_slConjugation hF hdetA hA3 hfix
  obtain ⟨ω, hω1⟩ : ∃ ω : Fˣ, ω ≠ 1 := by
    have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [LinearThreeFourOuter.card_units_eq_three hF]; norm_num)
    exact exists_ne 1
  have hω3 := LinearThreeFourOuter.units_pow_three hF ω
  set ζ := scalarElement ω hω3 with hζdef
  have hζZ : ζ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    hNc (scalarElement_mem_scalars ω hω3)
  have hζ3 : ζ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalarElement, ← map_pow,
      ← Units.val_pow_eq_pow_val, hω3, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hζ00 : ∀ k : ℕ, ((ζ ^ k : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = ((ω ^ k : Fˣ) : F) := fun k => by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalarElement, ← map_pow,
      ← Units.val_pow_eq_pow_val]
    simp
  have hζA : slConjugation 3 F A ζ = ζ := by
    apply Subtype.ext
    have hAA : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [coe_slConjugation, coe_scalarElement, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAA]
  have hcen : ∀ w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F),
      ∀ k : ℕ, w ^ k ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    fun w hw k => pow_mem hw k
  have hindX : ∀ i j : Fin 3, ζ ^ (i : ℕ) * y ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
    intro i j hij
    have hyj : y ^ (j : ℕ) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [eq_inv_of_mul_eq_one_right hij]
      exact inv_mem (hcen ζ hζZ _)
    have hj : j = 0 := by
      fin_cases j
      · rfl
      · exact absurd (by simpa using hyj) hyZ
      · exfalso
        apply hyZ
        have : y = (y ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hy3, one_mul]
        rw [this]
        exact hcen _ (by simpa using hyj) 2
    subst hj
    refine ⟨?_, rfl⟩
    have hi : ζ ^ (i : ℕ) = 1 := by simpa using hij
    have h00 := congrArg (fun w : Matrix.SpecialLinearGroup (Fin 3) F =>
      (w : Matrix (Fin 3) (Fin 3) F) 0 0) hi
    simp only [hζ00, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h00
    have hω' : ω ^ (i : ℕ) = 1 := Units.ext (by rw [h00, Units.val_one])
    fin_cases i
    · rfl
    · exact absurd (by simpa using hω') hω1
    · exfalso
      apply hω1
      have h2' : ω ^ 2 = 1 := by simpa using hω'
      calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
        _ = 1 := by rw [hω3, h2']; group
  have hπ'apply : ∀ k : ↥K, π k = e.symm (π' (e k)) := fun k => by
    simp [hπ'def, MulAut.congr_apply]
  have hpfix : ∀ z : Matrix.SpecialLinearGroup (Fin 3) F, slConjugation 3 F A z = z →
      ((e.symm z : ↥K) : Q) * p = p * ((e.symm z : ↥K) : Q) := by
    intro z hz
    have h1 := hπk (e.symm z)
    rw [hπ'apply, e.apply_symm_apply, hφ, hz] at h1
    calc ((e.symm z : ↥K) : Q) * p = p * ((e.symm z : ↥K) : Q) * p⁻¹ * p := by rw [← h1]
      _ = p * ((e.symm z : ↥K) : Q) := by group
  set H := K ⊓ Subgroup.centralizer {p} with hH
  have hζH : ((e.symm ζ : ↥K) : Q) ∈ H :=
    ⟨(e.symm ζ).2, Subgroup.mem_centralizer_singleton_iff.mpr (hpfix ζ hζA)⟩
  have hyH : ((e.symm y : ↥K) : Q) ∈ H :=
    ⟨(e.symm y).2, Subgroup.mem_centralizer_singleton_iff.mpr (hpfix y hyA)⟩
  have hcoe : ∀ w : Matrix.SpecialLinearGroup (Fin 3) F, ∀ k : ℕ,
      (((e.symm w : ↥K) : Q)) ^ k = ((e.symm (w ^ k) : ↥K) : Q) := fun w k => by
    rw [map_pow, Subgroup.coe_pow]
  obtain ⟨E₁, hE₁, hE₁9⟩ := exists_elemAbelian_nine (G := ↥H)
    (a := ⟨((e.symm ζ : ↥K) : Q), hζH⟩) (b := ⟨((e.symm y : ↥K) : Q), hyH⟩)
    (Subtype.ext (by
      change ((e.symm ζ : ↥K) : Q) * ((e.symm y : ↥K) : Q) =
        ((e.symm y : ↥K) : Q) * ((e.symm ζ : ↥K) : Q)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp hζZ y]))
    (Subtype.ext (by
      change ((e.symm ζ : ↥K) : Q) ^ 3 = 1
      rw [hcoe, hζ3, map_one, Subgroup.coe_one]))
    (Subtype.ext (by
      change ((e.symm y : ↥K) : Q) ^ 3 = 1
      rw [hcoe, hy3, map_one, Subgroup.coe_one]))
    (fun i j hij => hindX i j (e.symm.injective (Subtype.ext (by
      have := congrArg (fun w : ↥H => (w : Q)) hij
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [map_mul, map_pow, map_pow, map_one, Subgroup.coe_mul, Subgroup.coe_pow,
        Subgroup.coe_pow]
      exact this))))
  have hE : IsElemAbelian 3 (E₁.map H.subtype) := CFSG.SectionRank.isElemAbelian_map hE₁ _
  have hE9 : Nat.card (E₁.map H.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hE₁9]
  have hpK : p ∉ K := by
    intro hpK
    have hπc : π = MulAut.conj (⟨p, hpK⟩ : ↥K) := MulEquiv.ext fun _ => Subtype.ext rfl
    apply hnot ((e ⟨p, hpK⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix.SpecialLinearGroup (Fin 3) F ⧸ scalars 3 F)
    rw [hπbdef, hπ'def, hπc, congr_conj, quotient_conj]
  have hpE : p ∉ E₁.map H.subtype := fun hp => by
    obtain ⟨w, -, hw⟩ := hp
    exact hpK (hw ▸ w.2.1)
  exact false_of_commute_e9 hQ hE hE9 (h.P_elem.2 p hpP) hpE
    (fun w hw => by
      obtain ⟨u, -, rfl⟩ := hw
      exact (Subgroup.mem_centralizer_singleton_iff.mp u.2.2).symm)

end Main

end CFSG.Quasithin.H13.S126C
