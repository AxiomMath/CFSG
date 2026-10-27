module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Points
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate71

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.TauCetiBridge.BigCell TauCeti TauCeti.F4ShortRoot

@[expose] def isoRow (b : ℕ) : Fin 4 × Fin 26 :=
  [(3, 0), (2, 1), (1, 2), (0, 3), (2, 3), (0, 5), (3, 5), (1, 6), (0, 7), (2, 8), (1, 9), (3, 10),
    (2, 11), (2, 12), (3, 13), (1, 14), (2, 15), (0, 16), (1, 17), (0, 19), (2, 19), (0, 21),
    (1, 22), (2, 23), (3, 24)].getD (b - 1) (0, 0)

@[expose] def parentOf (t : ℕ) : Fin 4 × Fin 26 :=
  [(3, 0), (2, 1), (1, 2), (0, 3), (2, 3), (2, 4), (3, 5), (1, 6), (3, 6), (2, 8), (3, 8), (2, 11),
    (3, 10), (2, 13), (3, 12), (1, 14), (3, 14), (0, 16), (3, 16), (3, 18), (2, 19), (2, 20),
    (1, 22), (2, 23), (3, 24)].getD (t - 1) (0, 0)

theorem isoRow_spec : ∀ b : Fin 26, b ≠ 0 →
    raisingTarget (isoRow b).1 b = (isoRow b).2 ∧ raisingCoeff (isoRow b).1 b = 1 ∧
      ∀ k : Fin 26, k ≠ b → raisingTarget (isoRow b).1 k = (isoRow b).2 →
        raisingCoeff (isoRow b).1 k % 2 = 0 := by
  decide

theorem raisingCoeff_zero : ∀ i : Fin 4, raisingCoeff i 0 = 0 := by
  decide

theorem parentOf_spec : ∀ t : Fin 26, t ≠ 0 →
    (parentOf t).2 < t ∧ loweringTarget (parentOf t).1 (parentOf t).2 = t ∧
      loweringCoeff (parentOf t).1 (parentOf t).2 = 1 := by
  decide

section Commutant

variable {L : Type*} [Field L] [CharP L 2]

theorem intCast_eq_zero_of_even {z : ℤ} (h : z % 2 = 0) : (z : L) = 0 :=
  (CharP.intCast_eq_zero_iff L 2 z).2 (Int.dvd_of_emod_eq_zero h)

theorem eq_smul_one_of_commute {M : Matrix (Fin 26) (Fin 26) L}
    (hE : ∀ i : Fin 4, M * (tcE (.inl i)).map (Int.cast : ℤ → L) =
      (tcE (.inl i)).map (Int.cast : ℤ → L) * M)
    (hF : ∀ i : Fin 4, M * (tcE (.inr i)).map (Int.cast : ℤ → L) =
      (tcE (.inr i)).map (Int.cast : ℤ → L) * M) :
    M = M 0 0 • (1 : Matrix (Fin 26) (Fin 26) L) := by
  have h0 : ∀ b : Fin 26, b ≠ 0 → M b 0 = 0 := by
    intro b hb
    obtain ⟨ht, hc, hk⟩ := isoRow_spec b hb
    have e := congrFun (congrFun (hE (isoRow b).1) (isoRow b).2) 0
    simp only [Matrix.mul_apply, Matrix.map_apply, tcE, raisingMatrix_apply] at e
    have hl : ∑ k, M (isoRow b).2 k * ((if k = raisingTarget (isoRow b).1 0 then
        raisingCoeff (isoRow b).1 0 else 0 : ℤ) : L) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [raisingCoeff_zero]
      simp
    rw [hl, Finset.sum_eq_single b] at e
    · rw [ite_eq_left ht.symm, hc, Int.cast_one, one_mul] at e
      exact e.symm
    · intro k _ hkb
      by_cases hr : (isoRow b).2 = raisingTarget (isoRow b).1 k
      · rw [ite_eq_left hr, intCast_eq_zero_of_even (hk k hkb hr.symm), zero_mul]
      · rw [ite_eq_right hr, Int.cast_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hcol : ∀ n, ∀ t : Fin 26, (t : ℕ) = n → ∀ r,
      M r t = if r = t then M 0 0 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t htn r
      by_cases ht0 : t = 0
      · subst ht0
        by_cases hr : r = 0
        · simp [hr]
        · rw [ite_eq_right hr, h0 r hr]
      obtain ⟨hlt, htgt, hco⟩ := parentOf_spec t ht0
      have hb := ih (parentOf t).2 (by omega) (parentOf t).2 rfl
      have e := congrFun (congrFun (hF (parentOf t).1) r) (parentOf t).2
      simp only [Matrix.mul_apply, Matrix.map_apply, tcE, loweringMatrix_apply] at e
      have hl : ∑ k, M r k * ((if k = loweringTarget (parentOf t).1 (parentOf t).2 then
          loweringCoeff (parentOf t).1 (parentOf t).2 else 0 : ℤ) : L) = M r t := by
        rw [Finset.sum_eq_single t]
        · rw [ite_eq_left htgt.symm, hco, Int.cast_one, mul_one]
        · intro k _ hkt
          rw [ite_eq_right (fun h => hkt (h.trans htgt)), Int.cast_zero, mul_zero]
        · exact fun h => absurd (Finset.mem_univ _) h
      have hr : ∑ k, ((if r = loweringTarget (parentOf t).1 k then
          loweringCoeff (parentOf t).1 k else 0 : ℤ) : L) * M k (parentOf t).2 =
          if r = t then M 0 0 else 0 := by
        rw [Finset.sum_eq_single (parentOf t).2]
        · rw [hb (parentOf t).2, ite_eq_left rfl, htgt, hco]
          by_cases hrt : r = t
          · simp [hrt]
          · simp [hrt]
        · intro k _ hk
          rw [hb k, ite_eq_right hk, mul_zero]
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [hl, hr] at e
      exact e
  ext r t
  rw [hcol t t rfl r, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

end Commutant

@[expose] def formL : SpMat :=
  [(0, 25, 1), (1, 24, -1), (2, 23, 1), (3, 22, -1), (4, 21, 1), (5, 20, 1), (6, 19, -1),
    (7, 18, -1), (8, 17, 1), (9, 16, 1), (10, 15, -1), (11, 14, -1), (12, 12, 2), (12, 13, 1),
    (13, 12, 1), (13, 13, 2), (14, 11, -1), (15, 10, -1), (16, 9, 1), (17, 8, 1), (18, 7, -1),
    (19, 6, -1), (20, 5, 1), (21, 4, 1), (22, 3, -1), (23, 2, 1), (24, 1, -1), (25, 0, 1)]

@[expose] def formMat : Matrix (Fin 26) (Fin 26) ℤ :=
  smat formL

@[expose] def transL (L : SpMat) : SpMat :=
  L.map fun e => (e.2.1, e.1, e.2.2)

theorem ent_transL (L : SpMat) (r c : Fin 26) : ent (transL L) r c = ent L c r := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [transL, List.map_cons] at ih ⊢
    rw [ent_cons, ent_cons, ih]
    dsimp only
    congr 1
    simp only [and_comm]

theorem smat_transL (L : SpMat) : smat (transL L) = (smat L).transpose := by
  ext r c
  simp [smat, ent_transL]

@[expose] def formCheck (g : Fin 4 ⊕ Fin 4) : Bool :=
  eqB (mulL (transL (spE g)) formL ++ mulL formL (spE g)) [] &&
  eqB (mulL (transL (spE2 g)) formL ++ mulL (mulL (transL (spE g)) formL) (spE g) ++
    mulL formL (spE2 g)) [] &&
  eqB (mulL (mulL (transL (spE2 g)) formL) (spE g) ++
    mulL (mulL (transL (spE g)) formL) (spE2 g)) [] &&
  eqB (mulL (mulL (transL (spE2 g)) formL) (spE2 g)) []

theorem formCheck_all : ∀ g : Fin 4 ⊕ Fin 4, formCheck g = true := by
  decide +kernel

theorem formCheck_spec (g : Fin 4 ⊕ Fin 4) :
    (tcE g).transpose * formMat + formMat * tcE g = 0 ∧
    (tcE2 g).transpose * formMat + (tcE g).transpose * formMat * tcE g + formMat * tcE2 g = 0 ∧
    (tcE2 g).transpose * formMat * tcE g + (tcE g).transpose * formMat * tcE2 g = 0 ∧
    (tcE2 g).transpose * formMat * tcE2 g = 0 := by
  have h := formCheck_all g
  simp only [formCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := smat_eq_of_eqB h1
  have e2 := smat_eq_of_eqB h2
  have e3 := smat_eq_of_eqB h3
  have e4 := smat_eq_of_eqB h4
  simp only [smat_append, smat_mulL, smat_transL, smat_spE, smat_spE2, smat_nil] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

variable {A : Type*} [CommRing A]

abbrev formR (A : Type*) [CommRing A] : Matrix (Fin 26) (Fin 26) A :=
  formMat.map (Int.cast : ℤ → A)

theorem mapMatrix_transpose {B : Type*} [CommRing B] (f : A →+* B)
    (M : Matrix (Fin 26) (Fin 26) A) : f.mapMatrix M.transpose = (f.mapMatrix M).transpose := by
  ext i j
  rfl

theorem transpose_expand (t : A) (e f b : Matrix (Fin 26) (Fin 26) A) :
    (1 + t • e + t ^ 2 • f).transpose * b * (1 + t • e + t ^ 2 • f) =
      b + t • (e.transpose * b + b * e) +
        t ^ 2 • (f.transpose * b + e.transpose * b * e + b * f) +
        t ^ 3 • (f.transpose * b * e + e.transpose * b * f) + t ^ 4 • (f.transpose * b * f) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add, smul_smul, Matrix.mul_assoc]
  module

theorem transpose_expand_int (E E2 B : Matrix (Fin 26) (Fin 26) ℤ) (t : A) :
    (1 + t • E.map (Int.cast : ℤ → A) + t ^ 2 • E2.map (Int.cast : ℤ → A)).transpose *
        B.map (Int.cast : ℤ → A) *
        (1 + t • E.map (Int.cast : ℤ → A) + t ^ 2 • E2.map (Int.cast : ℤ → A)) =
      B.map (Int.cast : ℤ → A) + t • (E.transpose * B + B * E).map (Int.cast : ℤ → A) +
        t ^ 2 • (E2.transpose * B + E.transpose * B * E + B * E2).map (Int.cast : ℤ → A) +
        t ^ 3 • (E2.transpose * B * E + E.transpose * B * E2).map (Int.cast : ℤ → A) +
        t ^ 4 • (E2.transpose * B * E2).map (Int.cast : ℤ → A) := by
  simp only [map_intCast_eq_mapMatrix]
  rw [transpose_expand]
  simp only [map_add, map_mul, mapMatrix_transpose]

theorem rootPointMat_transpose_formR (k : Fin 4 ⊕ Fin 4) (t : A) :
    (rootPointMat k t).transpose * formR A * rootPointMat k t = formR A := by
  obtain ⟨h1, h2, h3, h4⟩ := formCheck_spec k
  rw [rootPointMat_eq, formR, transpose_expand_int, h1, h2, h3, h4]
  simp

theorem transpose_formR_of_mem_ratRootGroup {s : Matrix.GeneralLinearGroup (Fin 26) ℚ}
    (hs : s ∈ ratRootGroup) :
    (s : Matrix (Fin 26) (Fin 26) ℚ).transpose * formR ℚ * (s : Matrix (Fin 26) (Fin 26) ℚ) =
      formR ℚ := by
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, t, rfl⟩ := hx
    exact rootPointMat_transpose_formR k t
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (y : Matrix (Fin 26) (Fin 26) ℚ).transpose * (x : Matrix (Fin 26) (Fin 26) ℚ).transpose *
          formR ℚ * (x * y : Matrix (Fin 26) (Fin 26) ℚ) =
        (y : Matrix (Fin 26) (Fin 26) ℚ).transpose *
          ((x : Matrix (Fin 26) (Fin 26) ℚ).transpose * formR ℚ * x) * y := by
          simp only [Matrix.mul_assoc]
      _ = formR ℚ := by rw [hx, hy]
  | inv x _ hx =>
    have hxi : (x : Matrix (Fin 26) (Fin 26) ℚ) * ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) :
        Matrix (Fin 26) (Fin 26) ℚ) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) : Matrix (Fin 26) (Fin 26) ℚ).transpose *
          formR ℚ * ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) : Matrix (Fin 26) (Fin 26) ℚ) =
        ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) : Matrix (Fin 26) (Fin 26) ℚ).transpose *
          ((x : Matrix (Fin 26) (Fin 26) ℚ).transpose * formR ℚ * x) *
          ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) : Matrix (Fin 26) (Fin 26) ℚ) := by
          rw [hx]
      _ = ((x : Matrix (Fin 26) (Fin 26) ℚ) * ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) :
            Matrix (Fin 26) (Fin 26) ℚ)).transpose * formR ℚ *
          ((x : Matrix (Fin 26) (Fin 26) ℚ) * ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 26) ℚ) :
            Matrix (Fin 26) (Fin 26) ℚ)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = formR ℚ := by rw [hxi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] def formPoly (r c : Fin 26) : PolyRing :=
  (genMat.transpose * formR PolyRing * genMat - formR PolyRing) r c

theorem evalMat_formPoly (M : Matrix (Fin 26) (Fin 26) A) (r c : Fin 26) :
    evalMat M (formPoly r c) = (M.transpose * formR A * M - formR A) r c := by
  have key : evalMat M (formPoly r c) = ((evalMat M).mapMatrix
      (genMat.transpose * formR PolyRing * genMat - formR PolyRing)) r c := rfl
  rw [key, map_sub, map_mul, map_mul, mapMatrix_transpose, mapMatrix_evalMat_coordMatrix]
  have hB : (evalMat M).mapMatrix (formR PolyRing) = formR A := by
    ext i j
    simp [formR]
  rw [hB]

theorem transpose_mul_formMat_mul_of_mem_points {A : Type} [CommRing A] [Algebra (ZMod 2) A]
    {g : Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ PrimeField.points A) :
    (g : Matrix (Fin 26) (Fin 26) A).transpose * formR A * g = formR A := by
  have h : ∀ r c, evalMat (g : Matrix (Fin 26) (Fin 26) A) (formPoly r c) = 0 := fun r c =>
    evalMat_eq_zero_of_mem_points _ (fun s hs => by
      rw [evalMat_formPoly, transpose_formR_of_mem_ratRootGroup hs, sub_self,
        Matrix.zero_apply]) hg
  simp only [evalMat_formPoly] at h
  exact sub_eq_zero.1 (Matrix.ext h)

theorem bMat_simple_check : ∀ (i : Fin 4) (a b : Fin 26),
    ent (bL (4 + i)) a b = (if (i : ℕ) % 2 = 0 then 1 else -1) * ent (spE (.inl i)) a b ∧
      ent (bL (4 + genRoot (.inr i))) a b =
        (if (i : ℕ) % 2 = 0 then -1 else 1) * ent (spE (.inr i)) a b := by
  decide +kernel

theorem genRoot_inr_lt (i : Fin 4) : 4 + genRoot (.inr i) < 52 := by
  fin_cases i <;> decide

theorem bMat_simple (k : Fin 4 ⊕ Fin 4) :
    ∃ s : Fin 52, ∃ ε : ℤ, ε * ε = 1 ∧ bMat s = ε • tcE k := by
  rcases k with i | i
  · refine ⟨⟨4 + i, by omega⟩, if (i : ℕ) % 2 = 0 then 1 else -1, by split_ifs <;> rfl, ?_⟩
    ext a b
    rw [← smat_spE, bMat, Matrix.smul_apply, smul_eq_mul]
    exact (bMat_simple_check i a b).1
  · refine ⟨⟨4 + genRoot (.inr i), genRoot_inr_lt i⟩, if (i : ℕ) % 2 = 0 then -1 else 1,
      by split_ifs <;> rfl, ?_⟩
    ext a b
    rw [← smat_spE, bMat, Matrix.smul_apply, smul_eq_mul]
    exact (bMat_simple_check i a b).2

theorem commute_of_bMat_eq_smul {L : Type*} [Field L] {g : Matrix (Fin 26) (Fin 26) L}
    {s : ℕ} {ε : ℤ} {X : Matrix (Fin 26) (Fin 26) ℤ} (hε : ε * ε = 1) (hs : bMat s = ε • X)
    (h : g * bMatR L s = bMatR L s * g) :
    g * X.map (Int.cast : ℤ → L) = X.map (Int.cast : ℤ → L) * g := by
  have hX : bMatR L s = (ε : L) • X.map (Int.cast : ℤ → L) := by
    rw [bMatR, hs]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]
  have hε' : (ε : L) * ε = 1 := by
    have := congrArg (Int.cast : ℤ → L) hε
    rwa [Int.cast_mul, Int.cast_one] at this
  rw [hX, Matrix.mul_smul, Matrix.smul_mul] at h
  calc g * X.map (Int.cast : ℤ → L) = ((ε : L) * ε) • (g * X.map (Int.cast : ℤ → L)) := by
        rw [hε', one_smul]
    _ = ((ε : L) * ε) • (X.map (Int.cast : ℤ → L) * g) := by rw [← smul_smul, h, smul_smul]
    _ = X.map (Int.cast : ℤ → L) * g := by rw [hε', one_smul]

theorem commute_bMatR_of_adConj_eq_one {L : Type*} [Field L]
    {g : Matrix.GeneralLinearGroup (Fin 26) L} (hgN : g ∈ normGroup L) (hg : adConj g = 1)
    (s : Fin 52) :
    (g : Matrix (Fin 26) (Fin 26) L) * bMatR L s =
      bMatR L s * (g : Matrix (Fin 26) (Fin 26) L) := by
  have hs := congrArg (fun f : Module.End L (RootModule .F4 L) => f (posVec .F4 L s)) hg
  simp only [Module.End.one_apply] at hs
  rw [adOp_posVec] at hs
  have hcoord : ∀ u : Fin 52, coord u ((g : Matrix (Fin 26) (Fin 26) L) * bMatR L s *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) L) : Matrix (Fin 26) (Fin 26) L)) =
        if u = s then 1 else 0 := by
    intro u
    have hu := congrArg (posCoord .F4 L u) hs
    rw [map_sum, posCoord_posVec (by rw [dim_F4]; exact s.2)] at hu
    have hterm : ∀ v : Fin 52, posCoord .F4 L u (coord v ((g : Matrix (Fin 26) (Fin 26) L) *
        bMatR L s * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) L) : Matrix (Fin 26) (Fin 26) L)) •
          posVec .F4 L v) =
        if u = v then coord v ((g : Matrix (Fin 26) (Fin 26) L) * bMatR L s *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) L) : Matrix (Fin 26) (Fin 26) L)) else 0 :=
      fun v => by
        rw [map_smul, posCoord_posVec (by rw [dim_F4]; exact v.2), smul_eq_mul]
        by_cases huv : u = v
        · rw [ite_eq_left (congrArg Fin.val huv), ite_eq_left huv, mul_one]
        · rw [ite_eq_right (fun h => huv (Fin.ext h)), ite_eq_right huv, mul_zero]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hu
    rw [hu]
    by_cases hus : u = s
    · rw [ite_eq_left (congrArg Fin.val hus), ite_eq_left hus]
    · rw [ite_eq_right (fun h => hus (Fin.ext h)), ite_eq_right hus]
  have hX : (g : Matrix (Fin 26) (Fin 26) L) * bMatR L s *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) L) : Matrix (Fin 26) (Fin 26) L) = bMatR L s := by
    rw [((hgN s).1).eq_sum]
    simp only [hcoord, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  calc (g : Matrix (Fin 26) (Fin 26) L) * bMatR L s =
      (g : Matrix (Fin 26) (Fin 26) L) * bMatR L s *
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) L) : Matrix (Fin 26) (Fin 26) L) *
          (g : Matrix (Fin 26) (Fin 26) L)) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = bMatR L s * (g : Matrix (Fin 26) (Fin 26) L) := by rw [← Matrix.mul_assoc, hX]

theorem eq_one_of_commute_of_mem_points {L : Type} [Field L] [Algebra (ZMod 2) L] [CharP L 2]
    {g : Matrix.GeneralLinearGroup (Fin 26) L} (hgP : g ∈ PrimeField.points L)
    (hgen : ∀ k : Fin 4 ⊕ Fin 4, (g : Matrix (Fin 26) (Fin 26) L) * (tcE k).map (Int.cast : ℤ → L) =
      (tcE k).map (Int.cast : ℤ → L) * (g : Matrix (Fin 26) (Fin 26) L)) :
    g = 1 := by
  have hM := eq_smul_one_of_commute (fun i => hgen (.inl i)) (fun i => hgen (.inr i))
  have hB := transpose_mul_formMat_mul_of_mem_points hgP
  rw [hM] at hB
  have h025 := congrFun (congrFun hB 0) 25
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, formR,
    Matrix.map_apply] at h025
  have hval : (formMat 0 25 : L) = 1 := by
    have : formMat 0 25 = 1 := by decide +kernel
    rw [this, Int.cast_one]
  rw [hval, mul_one] at h025
  have hc : (g : Matrix (Fin 26) (Fin 26) L) 0 0 = 1 := by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have h0 : ((g : Matrix (Fin 26) (Fin 26) L) 0 0 + 1) *
        ((g : Matrix (Fin 26) (Fin 26) L) 0 0 + 1) = 0 := by
      linear_combination h025 + ((g : Matrix (Fin 26) (Fin 26) L) 0 0 + 1) * h2
    have := eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp h0)
    rwa [CharTwo.neg_eq] at this
  refine Units.ext ?_
  rw [Units.val_one, hM, hc, one_smul]

theorem adPoints_injective {L : Type} [Field L] [Algebra (ZMod 2) L] :
    Function.Injective (adPoints L) := by
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  rw [injective_iff_map_eq_one]
  intro g hg
  have hconj : adConj (g : Matrix.GeneralLinearGroup (Fin 26) L) = 1 := by
    rw [← coe_adPoints, hg, Units.val_one]
  have hcomm := commute_bMatR_of_adConj_eq_one (points_le_normGroup g.2) hconj
  refine Subtype.ext (eq_one_of_commute_of_mem_points g.2 fun k => ?_)
  obtain ⟨s, ε, hε, hs⟩ := bMat_simple k
  exact commute_of_bMat_eq_smul hε hs (hcomm s)

end CFSG.TauCetiBridge.ReeF4
