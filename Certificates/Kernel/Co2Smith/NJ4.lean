module

public import Certificates.Kernel.Co2Smith.NJ1
public import Certificates.Kernel.Co2Smith.NJFix
public import Certificates.Kernel.Co2Jc.Gen
public import Certificates.Kernel.Co2Smith.IdxAll
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem njG_all (k : Nat) : glNJG k = unpackR 22 (njGK k) := by
  by_cases hk : k < 3
  · exact njG_eq hk
  · have hs : glNJGw.size = 3 := by decide
    have e : glNJGw[k]! = [] := getElem!_neg glNJGw k (by omega)
    rw [glNJG, njGK, e, glR, CFSG.Sporadic.Co2Smith.Native.wRows, wK_nil, idRows_eq]

@[expose] noncomputable def gsK (s k : Nat) : Nat := if k = 1 then mulV (jcK s) (njGK 1) else njGK k

theorem njGs_eq (s k : Nat) : glNJGs s k = unpackR 22 (gsK s k) := by
  unfold glNJGs gsK
  split_ifs
  · rw [jc_eq, njG_all, mulRows_unpack]
  · exact njG_all k

theorem njWord_eq (g : Nat → Array Nat) (G : Nat → Nat) (hg : ∀ k, g k = unpackR 22 (G k)) :
    ∀ w : List Nat, glNJWord g w = unpackR 22 (w.foldr (fun k acc => mulV (G k) acc) IDP)
  | [] => idRows_eq
  | k :: w => by
    rw [glNJWord, List.foldr_cons, ← glNJWord, njWord_eq g G hg w, hg, mulRows_unpack,
      List.foldr_cons]

theorem njNrm_size : glNJNrm.size = 1024 := by decide +kernel

@[expose] noncomputable def njKF (k x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (glNJT k x) (CFSG.KC.Enum.pg 10 1023 (KernelCo2Jc.NJ k) x)
    (Nat.blt k 3 && Nat.blt x 1024)

theorem njK_eq_F (k x : Nat) : KernelCo2Jc.njK k x = njKF k x := by
  unfold KernelCo2Jc.njK njKF
  by_cases h : k < 3 ∧ x < 1024
  · have hb : (Nat.blt k 3 && Nat.blt x 1024) = true := by simp [h.1, h.2]
    rw [if_pos h, hb]
  · have hb : (Nat.blt k 3 && Nat.blt x 1024) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      exact h hc
    rw [if_neg h, hb]

theorem nj4_ite0 (k a b : Nat) :
    (if k = 0 then a else b) = Bool.rec (motive := fun _ => Nat) b a (Nat.beq k 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · rw [if_neg h, show Nat.beq k 0 = false from
      Bool.eq_false_iff.2 (fun hb => h (Nat.eq_of_beq_eq_true hb))]

theorem nj4_ok : glNJ4OK = true := by
  have h01 : ∀ k, (if k = 0 then glNJG 0 else glNJG 1) =
      unpackR 22 (if k = 0 then njGK 0 else njGK 1) := by
    intro k
    split_ifs <;> exact njG_all _
  unfold glNJ4OK glNJH1OK glNJFusOK glNJF
  rw [CFSG.KC.IdxAll.all_range_get1 glNJNrm 1024 njNrm_size
    (fun x v => decide (v < 1024) && [0, 64].contains (x ^^^ v ^^^ glNJT 0 v))]
  simp only [njWord_eq _ _ h01, njWord_eq _ _ njG_all, njWord_eq _ _ (njGs_eq _), njFixR_eq,
    CertificateChecks.KernelCo2Jc.glNJT_eq_njK, mulRows_unpack, idRows_eq, beq_unpack,
    bne_unpack, njK_eq_F, nj4_ite0]
  decide +kernel

end CertificateChecks.KernelCo2Smith
