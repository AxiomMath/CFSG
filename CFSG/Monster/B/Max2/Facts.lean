module

public import CFSG.Monster.B.Intertwiner.PairFacts
public import Certificates.Certificate3048

public section

namespace CFSG.Monster.B

open Bin Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def wordTwo {M : Type*} [Monoid M] (a b : M) (w : List Bool) : M :=
  (w.map fun l => if l then a else b).prod

section WordM

variable {M : Type*} [Monoid M] (a b : M)

theorem wordTwo_nil : wordTwo a b [] = 1 := by
  rw [wordTwo, List.map_nil, List.prod_nil]

theorem wordTwo_cons (l : Bool) (w : List Bool) :
    wordTwo a b (l :: w) = (if l then a else b) * wordTwo a b w := by
  rw [wordTwo, wordTwo, List.map_cons, List.prod_cons]

variable {a b}

theorem isUnit_wordTwo (ha : IsUnit a) (hb : IsUnit b) : ∀ w : List Bool, IsUnit (wordTwo a b w)
  | [] => by
    rw [wordTwo_nil]
    exact isUnit_one
  | l :: w => by
    rw [wordTwo_cons]
    refine IsUnit.mul ?_ (isUnit_wordTwo ha hb w)
    cases l
    · rw [if_neg Bool.false_ne_true]
      exact hb
    · rw [if_pos rfl]
      exact ha

theorem commute_wordTwo {x : M} (ha : Commute x a) (hb : Commute x b) :
    ∀ w : List Bool, Commute x (wordTwo a b w)
  | [] => by
    rw [wordTwo_nil]
    exact Commute.one_right x
  | l :: w => by
    rw [wordTwo_cons]
    refine Commute.mul_right ?_ (commute_wordTwo ha hb w)
    cases l
    · rw [if_neg Bool.false_ne_true]
      exact hb
    · rw [if_pos rfl]
      exact ha

theorem map_wordTwo {N : Type*} [Monoid N] (f : M →* N) (w : List Bool) :
    f (wordTwo a b w) = wordTwo (f a) (f b) w := by
  induction w with
  | nil => rw [wordTwo_nil, wordTwo_nil, map_one]
  | cons l w ih => rw [wordTwo_cons, wordTwo_cons, map_mul, ih, apply_ite f]

end WordM

section Defs

variable (Qf : ℕ → Matrix (Fin 4370) (Fin 4370) (ZMod 2))
  (Tm cm dm A2 : Matrix (Fin 4370) (Fin 4370) (ZMod 2))

@[expose] noncomputable def wordQ (w : List ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (w.map Qf).prod

@[expose] noncomputable def Xm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (Qf 0 * ((Qf 1)⁻¹ * Qf 0 * Qf 1)) ^ 2

@[expose] noncomputable def preConj (t : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (wordQ Qf (basisWord.take t))⁻¹ * Qf 0 * wordQ Qf (basisWord.take t)

@[expose] noncomputable def Em (i : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  preConj Qf (basisLens.getD i 0)

@[expose] noncomputable def BWm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := wordQ Qf parityWord24

@[expose] noncomputable def zm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Tm * dm ^ 24 * Tm⁻¹

@[expose] noncomputable def km : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (BWm Qf)⁻¹ * zm Tm dm * BWm Qf * Xm Qf

@[expose] noncomputable def uWm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  BWm Qf * km Qf Tm dm ^ 3

@[expose] noncomputable def zqm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  Xm Qf * (Dyadic.bridgeZE.map (Em Qf)).prod

@[expose] noncomputable def um : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  Tm * (wordTwo cm dm bridgeU * (wordTwo cm dm bridgeV)⁻¹) * Tm⁻¹ * (uWm Qf Tm dm * zqm Qf)

@[expose] noncomputable def C0m : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := (um Qf Tm cm dm)⁻¹ * Tm

@[expose] noncomputable def G1m : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  C0m Qf Tm cm dm * cm * (C0m Qf Tm cm dm)⁻¹

@[expose] noncomputable def G2m : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  C0m Qf Tm cm dm * dm * (C0m Qf Tm cm dm)⁻¹

@[expose] noncomputable def rowProdM (r : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  ((List.range 22).reverse.map fun j => if r.testBit j then Em Qf j else 1).prod

@[expose] noncomputable def Km : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (G2m Qf Tm cm dm * G1m Qf Tm cm dm * G1m Qf Tm cm dm * G2m Qf Tm cm dm * G2m Qf Tm cm dm *
    G1m Qf Tm cm dm) ^ 14

@[expose] noncomputable def X'm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Qf 25 ^ 2 * Xm Qf * Qf 25

@[expose] noncomputable def Y'm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (C0m Qf Tm cm dm)⁻¹ * X'm Qf * C0m Qf Tm cm dm

@[expose] noncomputable def W'm : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := A2 ^ 2 * dm ^ 24 * A2

end Defs

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

theorem commute_inv_mat {x a : Matrix n n R} (ha : IsUnit a) (h : x * a = a * x) :
    x * a⁻¹ = a⁻¹ * x := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 ha
  calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    _ = a⁻¹ * (x * a) * a⁻¹ := by rw [h]
    _ = a⁻¹ * x := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem mul_wordTwo_comm {x a b : Matrix n n R} (ha : x * a = a * x) (hb : x * b = b * x) :
    ∀ w : List Bool, x * wordTwo a b w = wordTwo a b w * x
  | [] => by rw [wordTwo_nil, Matrix.mul_one, Matrix.one_mul]
  | l :: w => by
    have hl : x * (if l then a else b) = (if l then a else b) * x := by
      cases l
      · rw [if_neg Bool.false_ne_true]
        exact hb
      · rw [if_pos rfl]
        exact ha
    rw [wordTwo_cons, ← Matrix.mul_assoc, hl, Matrix.mul_assoc, mul_wordTwo_comm ha hb w,
      Matrix.mul_assoc]

theorem bridge_mul_mat {T w v U' C : Matrix n n R} (hT : IsUnit T) (hw : IsUnit w) (hv : IsUnit v)
    (hb : U' * C * w = T * v) : T * (w * v⁻¹) * T⁻¹ * U' * C = T := by
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 hT
  have hwd := (Matrix.isUnit_iff_isUnit_det _).1 hw
  have hvd := (Matrix.isUnit_iff_isUnit_det _).1 hv
  have h1 : U' * C = T * v * w⁻¹ := by
    calc U' * C = U' * C * w * w⁻¹ := by
          rw [Matrix.mul_assoc (U' * C), Matrix.mul_nonsing_inv _ hwd, Matrix.mul_one]
      _ = T * v * w⁻¹ := by rw [hb]
  calc T * (w * v⁻¹) * T⁻¹ * U' * C = T * (w * v⁻¹) * T⁻¹ * (U' * C) :=
        Matrix.mul_assoc (T * (w * v⁻¹) * T⁻¹) U' C
    _ = T * (w * v⁻¹) * T⁻¹ * (T * v * w⁻¹) := by rw [h1]
    _ = T * w * (v⁻¹ * (T⁻¹ * T) * v) * w⁻¹ := by simp only [Matrix.mul_assoc]
    _ = T := by
        rw [Matrix.nonsing_inv_mul _ hTd, Matrix.mul_one, Matrix.nonsing_inv_mul _ hvd,
          Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hwd, Matrix.mul_one]

theorem bridge_conj_mat {T D Z P U' X : Matrix n n R} (hT : IsUnit T) (hTZ : T * D = Z * T)
    (hDP : D * P = P * D) (hZU : Z * U' = U' * X) :
    Z * (T * P * T⁻¹ * U') = T * P * T⁻¹ * U' * X := by
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 hT
  have hDT : D * T⁻¹ = T⁻¹ * Z := by
    calc D * T⁻¹ = T⁻¹ * (T * D) * T⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
      _ = T⁻¹ * (Z * T) * T⁻¹ := by rw [hTZ]
      _ = T⁻¹ * Z := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.mul_one]
  calc Z * (T * P * T⁻¹ * U') = Z * T * P * T⁻¹ * U' := by simp only [Matrix.mul_assoc]
    _ = T * (D * P) * T⁻¹ * U' := by
        rw [← hTZ]
        simp only [Matrix.mul_assoc]
    _ = T * P * (D * T⁻¹) * U' := by
        rw [hDP]
        simp only [Matrix.mul_assoc]
    _ = T * P * T⁻¹ * (Z * U') := by
        rw [hDT]
        simp only [Matrix.mul_assoc]
    _ = T * P * T⁻¹ * U' * X := by
        rw [hZU]
        simp only [Matrix.mul_assoc]

end Generic

theorem det_unit {A : MatB} (h : IsUnit A) : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 h

theorem eq_conj_of_mul {P E A : MatB} (hP : IsUnit P) (h : P * E = A * P) : E = P⁻¹ * A * P := by
  calc E = P⁻¹ * (P * E) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hP),
        Matrix.one_mul]
    _ = P⁻¹ * A * P := by rw [h, Matrix.mul_assoc]

theorem eq_conj_of_mul' {T A B : MatB} (hT : IsUnit T) (h : A * T = T * B) : A = T * B * T⁻¹ := by
  calc A = A * T * T⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (det_unit hT),
        Matrix.mul_one]
    _ = T * B * T⁻¹ := by rw [h]

theorem isUnit_left_of_mul {A B C : MatB} (h : A * B = C) (hC : IsUnit C) : IsUnit A := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (B := B * C⁻¹) ?_)
  rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ (det_unit hC)]

theorem isUnit_wordQ {w : List ℕ} (hw : ∀ j ∈ w, j < 26) (hQ : ∀ j < 26, IsUnit (Qn j)) :
    IsUnit (wordQ Qn w) := by
  induction w with
  | nil => exact isUnit_one
  | cons j w ih =>
    rw [wordQ, List.map_cons, List.prod_cons]
    exact (hQ j (hw j List.mem_cons_self)).mul
      (ih fun k hk => hw k (List.mem_cons_of_mem _ hk))

theorem basisWord_lt26 : ∀ j ∈ basisWord, j < 26 := by decide +kernel

theorem parityWord_lt26 : ∀ j ∈ parityWord24, j < 26 := by decide +kernel

theorem bridgeZE_lt : ∀ j ∈ Dyadic.bridgeZE, j < 22 := by decide +kernel

theorem comm_conj {M A B : MatB} (hM : IsUnit M) (h : A * B = B * A) :
    M * A * M⁻¹ * (M * B * M⁻¹) = M * B * M⁻¹ * (M * A * M⁻¹) := by
  have e : ∀ P R : MatB, M * P * M⁻¹ * (M * R * M⁻¹) = M * (P * R) * M⁻¹ := fun P R => by
    calc M * P * M⁻¹ * (M * R * M⁻¹) = M * P * (M⁻¹ * M) * R * M⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = M * (P * R) * M⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ (det_unit hM), Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, e, h]

theorem conj_sq_one {M A : MatB} (hM : IsUnit M) (h : A * A = 1) :
    M * A * M⁻¹ * (M * A * M⁻¹) = 1 := by
  calc M * A * M⁻¹ * (M * A * M⁻¹) = M * A * (M⁻¹ * M) * A * M⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = M * (A * A) * M⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ (det_unit hM), Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_nonsing_inv _ (det_unit hM)]

section Kernel

open CFSG.Monster.B.Dyadic

theorem max2K : FactMax2 := Certificates.certificate3048.1

theorem pinnedK : FactPinned := Certificates.certificate3048.2

theorem TK_isUnit : IsUnit TK :=
  pinnedK.2.2.2.2.2.2.1

theorem cK_isUnit : IsUnit cK :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse pinnedK.1)

theorem dK_isUnit : IsUnit dK := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (B := dK ^ 47) ?_)
  rw [← pow_succ']
  exact pinnedK.2.2.1

theorem wordCD_eq (w : List Bool) : wordCD w = wordTwo cK dK w := rfl

theorem wordCD_isUnit (w : List Bool) : IsUnit (wordCD w) := by
  rw [wordCD_eq]
  exact isUnit_wordTwo cK_isUnit dK_isUnit w

theorem D_mul_wordCD (w : List Bool) :
    dK ^ 24 * wordCD w = wordCD w * dK ^ 24 := by
  rw [wordCD_eq]
  exact mul_wordTwo_comm pinnedK.2.2.2.2.2.1 (Commute.self_pow dK 24).eq.symm w

@[expose] noncomputable def UbK : MatB :=
  TK * (wordCD bridgeU * (wordCD bridgeV)⁻¹) * TK⁻¹ * UzK

theorem UbK_mul_CK : UbK * CK = TK := by
  obtain ⟨-, -, -, -, -, -, ⟨hb, -⟩, -⟩ := max2K.1
  exact bridge_mul_mat TK_isUnit (wordCD_isUnit _) (wordCD_isUnit _) hb

theorem ZK_mul_UbK : ZK * UbK = UbK * XK := by
  obtain ⟨-, -, hTZ, -, -, ⟨-, -, hZU, -⟩, -⟩ := max2K.1
  have hDP : dK ^ 24 * (wordCD bridgeU * (wordCD bridgeV)⁻¹) =
      wordCD bridgeU * (wordCD bridgeV)⁻¹ * dK ^ 24 := by
    rw [← Matrix.mul_assoc, D_mul_wordCD, Matrix.mul_assoc,
      commute_inv_mat (wordCD_isUnit _) (D_mul_wordCD bridgeV), Matrix.mul_assoc]
  exact bridge_conj_mat TK_isUnit hTZ hDP hZU

theorem UbK_isUnit : IsUnit UbK :=
  isUnit_left_of_mul UbK_mul_CK TK_isUnit

theorem CK_isUnit : IsUnit CK := by
  obtain ⟨-, -, -, -, -, -, ⟨-, hCC⟩, -⟩ := max2K.1
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hCC)

theorem CK_inv : CK⁻¹ = CiK := by
  obtain ⟨-, -, -, -, -, -, ⟨-, hCC⟩, -⟩ := max2K.1
  exact Matrix.inv_eq_right_inv hCC

theorem CK_eq : CK = UbK⁻¹ * TK := by
  rw [← UbK_mul_CK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit UbK_isUnit),
    Matrix.one_mul]

theorem G1K_eq : G1K = CK * cK * CK⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hCc, -⟩, -⟩ := max2K.1
  exact eq_conj_of_mul' CK_isUnit hCc.symm

theorem G2K_eq : G2K = CK * dK * CK⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, hCd, -⟩, -⟩ := max2K.1
  exact eq_conj_of_mul' CK_isUnit hCd.symm

theorem G1K_inv : G1K⁻¹ = G1K := by
  refine Matrix.inv_eq_right_inv ?_
  rw [G1K_eq]
  exact conj_sq_one CK_isUnit pinnedK.1

theorem G2K_inv : G2K⁻¹ = Gi2K := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hG⟩, -⟩ := max2K.1
  exact Matrix.inv_eq_right_inv hG

theorem ZK_eq :
    ZK = TK * dK ^ 24 * TK⁻¹ := by
  obtain ⟨-, -, hTZ, -⟩ := max2K.1
  exact eq_conj_of_mul' TK_isUnit hTZ.symm

theorem XK_eq_conj :
    XK = CK * dK ^ 24 * CK⁻¹ := by
  have hX : XK = UbK⁻¹ * ZK * UbK := eq_conj_of_mul UbK_isUnit ZK_mul_UbK.symm
  have hCi : CK⁻¹ = TK⁻¹ * UbK := by
    rw [CK_eq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit UbK_isUnit)]
  rw [hX, ZK_eq, hCi, CK_eq]
  simp only [Matrix.mul_assoc]

end Kernel

section Facts

variable (hQ : ∀ j < 26, IsUnit (Qn j))

include hQ in
theorem Xm_eq : Xm Qn = Dyadic.XK := by
  obtain ⟨⟨hV, hXV⟩, -⟩ := max2K.1
  have hV' : Qn 1 * Dyadic.VK = Qn 0 * Qn 1 := hV
  rw [Xm, ← eq_conj_of_mul (hQ 1 (by norm_num)) hV']
  exact hXV

include hQ in
theorem Em_eq {i : ℕ} (hi : i < 22) : Em Qn i = Dyadic.EK i := by
  obtain ⟨-, -, -, -, -, -, -, -, hPE, -⟩ := max2K.1
  have hw : ∀ j ∈ basisWord.take (basisLens.getD i 0), j < 26 :=
    fun j hj => basisWord_lt26 j (List.mem_of_mem_take hj)
  have h : wordQ Qn (basisWord.take (basisLens.getD i 0)) * Dyadic.EK i =
      Qn 0 * wordQ Qn (basisWord.take (basisLens.getD i 0)) := hPE i hi
  rw [Em, preConj]
  exact (eq_conj_of_mul (isUnit_wordQ hw hQ) h).symm

include hQ in
theorem km_eq :
    km Qn Dyadic.TK Dyadic.dK = Dyadic.YK := by
  obtain ⟨-, -, -, hWZ, ⟨hZwX, -⟩, -⟩ := max2K.1
  have hWZ' : BWm Qn * Dyadic.ZwK = Dyadic.ZK * BWm Qn := hWZ
  have hB : IsUnit (BWm Qn) := isUnit_wordQ parityWord_lt26 hQ
  rw [km, zm, ← ZK_eq, Xm_eq hQ, ← hZwX, ← eq_conj_of_mul hB hWZ']

include hQ in
theorem uWm_eq :
    uWm Qn Dyadic.TK Dyadic.dK = Dyadic.UK := by
  obtain ⟨-, -, -, -, -, ⟨hWU, -⟩, -⟩ := max2K.1
  rw [uWm, km_eq hQ, ← hWU]
  rfl

include hQ in
theorem zqm_eq : zqm Qn = Dyadic.ZqK := by
  obtain ⟨-, -, -, -, -, ⟨-, -, -, hZq⟩, -⟩ := max2K.1
  have hE : Dyadic.bridgeZE.map (Em Qn) = Dyadic.bridgeZE.map Dyadic.EK :=
    List.map_congr_left fun i hi => Em_eq hQ (bridgeZE_lt i hi)
  rw [zqm, Xm_eq hQ, hE, hZq]

include hQ in
theorem um_eq :
    um Qn Dyadic.TK Dyadic.cK Dyadic.dK = UbK := by
  obtain ⟨-, -, -, -, -, ⟨-, hUz, -⟩, -⟩ := max2K.1
  rw [um, uWm_eq hQ, zqm_eq hQ, hUz]
  rfl

include hQ in
theorem C0m_eq :
    C0m Qn Dyadic.TK Dyadic.cK Dyadic.dK = Dyadic.CK := by
  rw [C0m, um_eq hQ, CK_eq]

include hQ in
theorem G1m_eq :
    G1m Qn Tmat cMat dMat = Dyadic.G1K := by
  have e : G1m Qn Dyadic.TK Dyadic.cK Dyadic.dK = Dyadic.G1K := by
    rw [G1m, C0m_eq hQ, G1K_eq]
  exact e

include hQ in
theorem G2m_eq :
    G2m Qn Tmat cMat dMat = Dyadic.G2K := by
  have e : G2m Qn Dyadic.TK Dyadic.cK Dyadic.dK = Dyadic.G2K := by
    rw [G2m, C0m_eq hQ, G2K_eq]
  exact e

include hQ in
theorem max2_matrix_facts :
    Xm Qn ^ 2 = 1 ∧ Xm Qn ≠ 1 ∧ km Qn Tmat dMat ^ 5 = 1 ∧ km Qn Tmat dMat ≠ 1 ∧
    Tmat * Tmat⁻¹ = 1 ∧ BWm Qn * (BWm Qn)⁻¹ = 1 ∧
    (um Qn Tmat cMat dMat)⁻¹ * zm Tmat dMat * um Qn Tmat cMat dMat = Xm Qn ∧
    G1m Qn Tmat cMat dMat * Xm Qn = Xm Qn * G1m Qn Tmat cMat dMat ∧
    G2m Qn Tmat cMat dMat * Xm Qn = Xm Qn * G2m Qn Tmat cMat dMat ∧
    (∀ i j, i < 22 → j < 22 →
      CFSG.KC.BM.e0 ᵥ* ((G1m Qn Tmat cMat dMat)⁻¹ * Em Qn i * G1m Qn Tmat cMat dMat * Em Qn j) =
      CFSG.KC.BM.e0 ᵥ* (Em Qn j * Xm Qn ^ Dyadic.actK quotRows1 i j *
        ((G1m Qn Tmat cMat dMat)⁻¹ * Em Qn i * G1m Qn Tmat cMat dMat))) ∧
    (∀ i j, i < 22 → j < 22 →
      CFSG.KC.BM.e0 ᵥ* ((G2m Qn Tmat cMat dMat)⁻¹ * Em Qn i * G2m Qn Tmat cMat dMat * Em Qn j) =
      CFSG.KC.BM.e0 ᵥ* (Em Qn j * Xm Qn ^ Dyadic.actK quotRows2 i j *
        ((G2m Qn Tmat cMat dMat)⁻¹ * Em Qn i * G2m Qn Tmat cMat dMat))) ∧
    Km Qn Tmat cMat dMat ≠ 1 ∧ Km Qn Tmat cMat dMat ≠ Xm Qn ∧
    CFSG.KC.BM.e0 ᵥ* Xm Qn ≠ CFSG.KC.BM.e0 ∧
    (∀ i j, i < 22 → j < 22 → CFSG.KC.BM.e0 ᵥ* (Em Qn i * Em Qn j) =
      CFSG.KC.BM.e0 ᵥ* (Em Qn j * Xm Qn ^ Dyadic.rowBitK gramRows i j * Em Qn i)) ∧
    X'm Qn * Xm Qn = Xm Qn * X'm Qn ∧ (W'm dMat genA₂ * Y'm Qn Tmat cMat dMat) ^ 5 = 1 := by
  obtain ⟨-, ⟨hX2, hX1⟩, -, -, ⟨-, hY5, hY1⟩, -, -, -, -, hvx, hgram, hact1,
    hact2, ⟨hK, -, hK1, hKX⟩, hXp, hWY⟩ := max2K.1
  have hDc : Dyadic.dK ^ 24 * Dyadic.cK = Dyadic.cK * Dyadic.dK ^ 24 :=
    pinnedK.2.2.2.2.2.1
  have hX := Xm_eq hQ
  have hE : ∀ i, i < 22 → Em Qn i = Dyadic.EK i := fun i hi => Em_eq hQ hi
  have hG1 : G1m Qn Tmat cMat dMat = Dyadic.G1K := G1m_eq hQ
  have hG2 : G2m Qn Tmat cMat dMat = Dyadic.G2K := G2m_eq hQ
  have hk : km Qn Tmat dMat = Dyadic.YK := km_eq hQ
  have hu : um Qn Tmat cMat dMat = UbK := um_eq hQ
  have hz : zm Tmat dMat = Dyadic.ZK := ZK_eq.symm
  have hC0 : C0m Qn Tmat cMat dMat = Dyadic.CK := C0m_eq hQ
  have hT : IsUnit Tmat := TK_isUnit
  have hd : dMat = Dyadic.dK := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX, sq, hX2]
  · rw [hX]
    exact hX1
  · rw [hk, hY5]
  · rw [hk]
    exact hY1
  · exact Matrix.mul_nonsing_inv _ (det_unit hT)
  · exact Matrix.mul_nonsing_inv _ (det_unit (isUnit_wordQ parityWord_lt26 hQ))
  · rw [hu, hz, hX, ← eq_conj_of_mul UbK_isUnit ZK_mul_UbK.symm]
  · rw [hG1, hX, XK_eq_conj, G1K_eq]
    exact comm_conj CK_isUnit hDc.symm
  · rw [hG2, hX, XK_eq_conj, G2K_eq]
    exact comm_conj CK_isUnit (Commute.self_pow Dyadic.dK 24).eq
  · intro i j hi hj
    rw [hG1, hE i hi, hE j hj, hX, G1K_inv]
    exact hact1 i j hi hj
  · intro i j hi hj
    rw [hG2, hE i hi, hE j hj, hX, G2K_inv]
    exact hact2 i j hi hj
  · rw [Km, hG1, hG2, ← hK]
    exact hK1
  · rw [Km, hG1, hG2, ← hK, hX]
    exact hKX
  · rw [hX]
    exact hvx
  · intro i j hi hj
    rw [hE i hi, hE j hj, hX]
    exact hgram i j hi hj
  · rw [X'm, hX, sq]
    exact hXp
  · rw [W'm, Y'm, X'm, hX, hC0, CK_inv, sq, sq, hd]
    exact hWY

include hQ in
theorem max2_file_facts :
    Xm Qn = Dyadic.rowsK KC.BM.Max2.Xb.rows ∧
    C0m Qn Tmat cMat dMat = Dyadic.rowsK KC.BM.Max2.C.rows ∧
    (C0m Qn Tmat cMat dMat)⁻¹ = Dyadic.rowsK KC.BM.Max2.Ci.rows ∧
    G1m Qn Tmat cMat dMat = Dyadic.rowsK KC.BM.Max2.G1.rows ∧
    G2m Qn Tmat cMat dMat = Dyadic.rowsK KC.BM.Max2.G2.rows := by
  obtain ⟨hXr, hCr, hCir, hG1r, hG2r⟩ := max2K.2
  have hC0 : C0m Qn Tmat cMat dMat = Dyadic.CK := C0m_eq hQ
  refine ⟨(Xm_eq hQ).trans hXr, hC0.trans hCr, by rw [hC0, CK_inv]; exact hCir,
    (G1m_eq hQ).trans hG1r, (G2m_eq hQ).trans hG2r⟩

end Facts

end CFSG.Monster.B

end
