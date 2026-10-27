module

public import Certificates.Data.U52Yamada
public import CFSG.Certificates.Kernel.EvenBN.F4MatSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.Batch27032

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open Certificates.U52Yamada

@[expose] noncomputable def wK (w : List (Fin 10)) : Nat :=
  List.rec (motive := fun _ => Nat) (enc 1) (fun i _ acc => mulK (enc (genMat i)) acc) w

@[expose] noncomputable def cK : Nat := mulK (enc (x₃Mat 1)) (enc (x₄Mat 0 1))

@[expose] noncomputable def bK : Nat :=
  mulK (mulK (mulK (mulK (mulK (enc (x₁Mat 0 1)) (enc (x₄Mat 0 1))) (enc uMat)) (enc vMat))
    (enc uMat)) (enc vMat)

@[expose] noncomputable def cbK (w : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (enc 1) (fun x _ acc => mulK (Bool.rec cK bK x) acc) w

theorem wK_eq : ∀ w : List (Fin 10), decM (wK w) = wordMat w
  | [] => by
    change decM (enc 1) = _
    rw [decM_enc]
    rfl
  | i :: w => by
    change decM (mulK (enc (genMat i)) (wK w)) = _
    rw [decM_mulK, decM_enc, wK_eq w, wordMat, wordMat, List.map_cons, List.prod_cons]

theorem cK_eq : decM cK = cA5 := by simp only [cK, decM_mulK, decM_enc, cA5]

theorem bK_eq : decM bK = bA5 := by simp only [bK, decM_mulK, decM_enc, bA5]

theorem cbK_eq : ∀ w : List Bool, decM (cbK w) = cbMat w
  | [] => by
    change decM (enc 1) = _
    rw [decM_enc]
    rfl
  | x :: w => by
    change decM (mulK (Bool.rec cK bK x) (cbK w)) = _
    rw [decM_mulK, cbK_eq w, cbMat, cbMat, List.map_cons, List.prod_cons]
    cases x
    · rw [cK_eq]
      rfl
    · rw [bK_eq]
      rfl

theorem eqL {L R : Matrix (Fin 5) (Fin 5) F4} {X Y : Nat} (hX : decM X = L) (hY : decM Y = R)
    (h : Nat.beq X Y = true) : L = R := by
  rw [← hX, ← hY, Nat.eq_of_beq_eq_true h]

theorem normL (A B : Matrix (Fin 5) (Fin 5) F4)
    (h : chkL (mulK (mulK (enc A) (enc B)) (invK (enc A))) fShapeL = true) :
    IsFShape (A * B * invMat A) := by
  have hf := fShape_of h
  rwa [decM_mulK, decM_mulK, decM_invK, decM_enc, decM_enc] at hf

theorem orbL (w : List (Fin 10)) (M : Matrix (Fin 5) (Fin 5) F4) (p : F4 × F4 × F4)
    (h : Nat.beq (mulK (wK w) (enc M)) (mulK (mulK (mulK (mulK (enc (x₁Mat 0 p.1)) (enc (x₂Mat 0)))
      (enc (x₃Mat p.2.1))) (enc (x₄Mat 0 p.2.2))) (wK w)) = true) :
    wordMat w * M = fMat p * wordMat w :=
  eqL (by rw [decM_mulK, wK_eq, decM_enc])
    (by simp only [decM_mulK, decM_enc, wK_eq, fMat, nfMat]) h

theorem a5L {X : Nat} {M : Matrix (Fin 5) (Fin 5) F4} (u v : List Bool) (hM : decM X = M)
    (h : Nat.beq (mulK (mulK X (cbK u)) (cbK v)) (mulK (cbK v) (cbK u)) = true) :
    M * cbMat u * cbMat v = cbMat v * cbMat u :=
  eqL (by rw [decM_mulK, decM_mulK, hM, cbK_eq, cbK_eq]) (by rw [decM_mulK, cbK_eq, cbK_eq]) h

theorem normF : CheckNormF := by
  intro i j
  fin_cases i <;> fin_cases j <;> exact normL _ _ (by quickRfl)

theorem orb5OK : CheckOrb5 := by
  intro k
  fin_cases k <;> exact orbL _ _ _ (by quickRfl)

theorem orb10OK : CheckOrb10 := by
  intro k
  fin_cases k <;> exact orbL _ _ _ (by quickRfl)

theorem a5OK : CheckA5 :=
  ⟨a5L _ _ cK_eq (by quickRfl), a5L _ _ bK_eq (by quickRfl)⟩

theorem identOK : CheckIdent := ⟨normF, orb5OK, orb10OK, a5OK⟩

theorem checkIdent_true : checkIdent () = true := by
  unfold checkIdent
  exact @decide_eq_true CheckIdent
    (@decidable_of_iff _ CheckIdentM checkIdentM_iff (decCheckIdentM ())) identOK

end CertificateChecks.Batch27032

namespace Certificates

open CertificateChecks

theorem certificate27032 : Certificates.U52Yamada.checkIdent () = true := by
  exact CertificateChecks.Batch27032.checkIdent_true

end Certificates
