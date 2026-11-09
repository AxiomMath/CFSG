module

public import Certificates.Kernel.BabyMonster.CTIB.LiftH10A
public import Certificates.Kernel.BabyMonster.CTIB.LiftH10B
public import Certificates.Kernel.BabyMonster.CTIB.Signs
public import CFSG.Certificates.Kernel.BabyMonster.Q23Sound
public import CFSG.Certificates.Kernel.BabyMonster.CTIBSmall.All
public import CFSG.Certificates.Kernel.BabyMonster.CTIBSmall.Check0

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Pair CFSG.Monster.B.CTIB.Native

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

@[expose] def actHi (g j : ℕ) : ℕ := (g >>> (j + 1)) <<< (j + 1)

theorem actHi_testBit (g j n : ℕ) : (actHi g j).testBit n = (decide (j < n) && g.testBit n) := by
  rw [actHi, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : j < n
  · have h1 : j + 1 ≤ n := h
    have e : j + 1 + (n - (j + 1)) = n := by omega
    simp only [ge_iff_le, h1, h, decide_true, Bool.true_and, e]
  · have h1 : ¬ j + 1 ≤ n := h
    simp only [ge_iff_le, h1, h, decide_false, Bool.false_and]

@[expose] def actPar (x : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => actPar x n ^^ x.testBit n

theorem actPar_zero : ∀ n, actPar 0 n = false
  | 0 => rfl
  | n + 1 => by
    rw [actPar, actPar_zero n, Nat.zero_testBit]
    rfl

theorem actPar_and_xor (a x y : ℕ) :
    ∀ n, actPar (a &&& (x ^^^ y)) n = (actPar (a &&& x) n ^^ actPar (a &&& y) n)
  | 0 => rfl
  | n + 1 => by
    rw [actPar, actPar, actPar, actPar_and_xor a x y n, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_and, Nat.testBit_xor]
    cases actPar (a &&& x) n <;> cases actPar (a &&& y) n <;> cases a.testBit n <;>
      cases x.testBit n <;> cases y.testBit n <;> rfl

theorem cAtN_eq_actPar (g u j : ℕ) : ∀ n, cAtN g u j n = actPar (u &&& actHi g j) n
  | 0 => rfl
  | n + 1 => by
    rw [cAtN, actPar, cAtN_eq_actPar g u j n, Nat.testBit_and, actHi_testBit]
    cases decide (j < n) <;> cases u.testBit n <;> cases g.testBit n <;> rfl

@[expose] def actWv (G : Array ℕ) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if b.testBit m then actWv G b m ^^^ actHi (G.getD m 0) m else actWv G b m

theorem corrN_eq_actPar (G : Array ℕ) (a b : ℕ) :
    ∀ m, corrN G a b m = actPar (a &&& actWv G b m) 22
  | 0 => by
    rw [corrN, actWv, Nat.and_zero, actPar_zero]
  | m + 1 => by
    rw [corrN, actWv, corrN_eq_actPar G a b m]
    by_cases h : b.testBit m
    · simp only [h, ↓reduceIte]
      rw [actPar_and_xor, cAt, cAtN_eq_actPar]
    · simp only [h, ↓reduceIte, Bool.false_eq_true]

@[expose] def actQmul (G : Array ℕ) (a b : ℕ) : ℕ :=
  (a ^^^ b) % 2 ^ 22 |||
    (if (a.testBit 22 ^^ b.testBit 22) ^^ actPar (a &&& actWv G b 22) 22 then 2 ^ 22 else 0)

theorem qmul_eq_actQmul (G : Array ℕ) (a b : ℕ) : qmul G a b = actQmul G a b := by
  rw [qmul, actQmul, corr, corrN_eq_actPar]

@[expose] def actApplyN (G A : Array ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => if n.testBit 22 then 2 ^ 22 else 0
  | m + 1 => if n.testBit m then actQmul G (actApplyN G A n m) (A.getD m 0) else actApplyN G A n m

theorem autApplyN_eq_act (G A : Array ℕ) (n : ℕ) : ∀ m, autApplyN G A n m = actApplyN G A n m
  | 0 => by rw [autApplyN, actApplyN]
  | m + 1 => by rw [autApplyN, actApplyN, autApplyN_eq_act G A n m, qmul_eq_actQmul]

theorem autApply_eq_act (G B : Array ℕ) : autApply G B = fun n => actApplyN G B n 22 := by
  funext n
  rw [autApply, autApplyN_eq_act]

theorem autWord_eq_act (w : List ℕ) : autWord gArr genImgs w =
    w.foldl (fun A l => A.map fun n => actApplyN gArr (genImgs l) n 22) (id23 ()) := by
  unfold autWord autComp
  simp only [autApply_eq_act]

theorem img6 : (autWord gArr genImgs liftWord6).toList = liftImgs6 := by
  rw [autWord_eq_act]
  exact eq_of_beq (by quickRfl)

theorem img8 : (autWord gArr genImgs liftWord8).toList = liftImgs8 :=
  eq_of_beq (by quickRfl)

theorem step_first : ((liftWord10.drop 0).take 1).foldl stepA (id23 ()) = genImgs 1 :=
  Array.toList_inj.mp (eq_of_beq (by quickRfl))

theorem drop_end : liftWord10.drop 137 = [] := by decide

theorem img10 : (autWord gArr genImgs liftWord10).toList = liftImgs10 := by
  have e : autWord gArr genImgs liftWord10 = (liftWord10.drop 0).foldl stepA (id23 ()) := rfl
  rw [e, chain_step step_first, chain_step (arr_of h10c0), chain_step (arr_of h10c1),
    chain_step (arr_of h10c2), chain_step (arr_of h10c3), chain_step (arr_of h10c4),
    chain_step (arr_of h10c5), chain_step (arr_of h10c6), chain_step (arr_of h10c7),
    chain_step (arr_of h10c8), chain_step (arr_of h10c9), chain_step (arr_of h10c10),
    chain_step (arr_of h10c11), chain_step (arr_of h10c12), chain_step (arr_of h10c13),
    chain_step (arr_of h10c14), chain_step (arr_of h10c15), chain_step (arr_of h10c16)]
  have e2 : liftWord10.drop (129 + 8) = [] := drop_end
  rw [e2, List.foldl_nil]
  exact eq_of_beq (by quickRfl)

@[expose] def mask22 : ℕ := (List.range 22).foldl (fun acc i => acc ||| (4194303 <<< (32 * i))) 0

theorem sq_of {X Lo Y : ℕ}
    (h : andB (Nat.beq (mm32 22 (Nat.land X mask22) (Nat.land X mask22)) (id32 22))
      (Nat.beq (compAut Lo X X) Y) = true) :
    mat32 (Nat.land X mask22) * mat32 (Nat.land X mask22) = 1 := by
  obtain ⟨h1, -⟩ := Dy.andB_true h
  rw [← mm32_mat, Nat.eq_of_beq_eq_true h1, id32_mat]

theorem rank_of {X P Q k : ℕ} (h : rank22 (Nat.xor (Nat.land X mask22) (id32 22)) P Q k = true)
    (hwf : wf32 22 (Nat.xor (Nat.land X mask22) (id32 22)) = true) (hk : k ≤ 22) :
    (mat32 (Nat.xor (Nat.land X mask22) (id32 22))).rank = k :=
  rank22_sound hk hwf h

theorem mat_rows {X : ℕ} {rows : List ℕ}
    (h : ∀ i < 22, ∀ j < 22, (fld32 (Nat.land X mask22) i).testBit j = (rows.getD i 0).testBit j) :
    mat32 (Nat.land X mask22) = matRows rows := by
  ext i j
  rw [mat32, matRows, Matrix.of_apply, Matrix.of_apply, h i i.2 j j.2]

theorem mat_rows_sub {X : ℕ} {rows : List ℕ}
    (h : ∀ i < 22, ∀ j < 22, (fld32 (Nat.xor (Nat.land X mask22) (id32 22)) i).testBit j =
      ((rows.getD i 0).testBit j ^^ decide (i = j))) :
    mat32 (Nat.xor (Nat.land X mask22) (id32 22)) = matRows rows - 1 := by
  ext i j
  rw [mat32, Matrix.of_apply, h i i.2 j j.2, Matrix.sub_apply, matRows, Matrix.of_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · have e : decide ((i : ℕ) = j) = true := by simp [hij]
    rw [e, ite_eq_left hij]
    cases (rows.getD i 0).testBit j <;> decide
  · have e : decide ((i : ℕ) = j) = false := by simp [Fin.val_ne_of_ne hij]
    rw [e, ite_eq_right hij, Bool.xor_false]
    exact (sub_zero _).symm

theorem sq6 : mat32 (Nat.land CTIBSmall.X1 mask22) * mat32 (Nat.land CTIBSmall.X1 mask22) = 1 :=
  sq_of CTIBSmall.sq6

theorem sq8 : mat32 (Nat.land CTIBSmall.A0 mask22) * mat32 (Nat.land CTIBSmall.A0 mask22) = 1 :=
  sq_of CTIBSmall.sq8

theorem sq10 :
    mat32 (Nat.land CTIBSmall.X18 mask22) * mat32 (Nat.land CTIBSmall.X18 mask22) = 1 :=
  sq_of CTIBSmall.sq10

theorem qrk6 : (mat32 (Nat.xor (Nat.land CTIBSmall.X1 mask22) (id32 22))).rank = 6 :=
  rank_of CTIBSmall.rk6 (by decide +kernel) (by decide)

theorem qrk8 : (mat32 (Nat.xor (Nat.land CTIBSmall.A0 mask22) (id32 22))).rank = 8 :=
  rank_of CTIBSmall.rk8 (by decide +kernel) (by decide)

theorem qrk10 : (mat32 (Nat.xor (Nat.land CTIBSmall.X18 mask22) (id32 22))).rank = 10 :=
  rank_of CTIBSmall.rk10 (by decide +kernel) (by decide)

theorem rows6 : mat32 (Nat.land CTIBSmall.X1 mask22) = matRows liftRows6 :=
  mat_rows (by decide +kernel)

theorem rows8 : mat32 (Nat.land CTIBSmall.A0 mask22) = matRows liftRows8 :=
  mat_rows (by decide +kernel)

theorem rows10 : mat32 (Nat.land CTIBSmall.X18 mask22) = matRows liftRows10 :=
  mat_rows (by decide +kernel)

theorem rows6' : mat32 (Nat.xor (Nat.land CTIBSmall.X1 mask22) (id32 22)) = matRows liftRows6 - 1 :=
  mat_rows_sub (by decide +kernel)

theorem rows8' : mat32 (Nat.xor (Nat.land CTIBSmall.A0 mask22) (id32 22)) = matRows liftRows8 - 1 :=
  mat_rows_sub (by decide +kernel)

theorem rows10' :
    mat32 (Nat.xor (Nat.land CTIBSmall.X18 mask22) (id32 22)) = matRows liftRows10 - 1 :=
  mat_rows_sub (by decide +kernel)

theorem r12_sq : repK 12 * repK 12 = 1 := by
  rw [rep12]
  exact sm1one CTIB.wf_R12 CTIB.wf_R12 (by bm_strips CFSG.KC.BM.CTIB.sq12 69)

theorem factAct : FactAct := by
  refine ⟨signs_g0, signs_g1, fun k hk => ?_, r12_sq⟩
  rcases hk with rfl | rfl | rfl
  · have e : liftData 6 = (liftWord6, liftImgs6, liftRows6) := rfl
    rw [e]
    exact ⟨img6, by rw [← rows6]; exact sq6, by rw [← rows6']; exact qrk6⟩
  · have e : liftData 8 = (liftWord8, liftImgs8, liftRows8) := rfl
    rw [e]
    exact ⟨img8, by rw [← rows8]; exact sq8, by rw [← rows8']; exact qrk8⟩
  · have e : liftData 10 = (liftWord10, liftImgs10, liftRows10) := rfl
    rw [e]
    exact ⟨img10, by rw [← rows10]; exact sq10, by rw [← rows10']; exact qrk10⟩

end CertificateChecks.KernelBM.CTIB

end
