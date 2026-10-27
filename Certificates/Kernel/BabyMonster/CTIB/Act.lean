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

theorem img6 : (autWord gArr genImgs liftWord6).toList = liftImgs6 :=
  eq_of_beq (by quickRfl)

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
