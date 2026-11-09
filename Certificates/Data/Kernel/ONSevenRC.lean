module

public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Enum.DefsC
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.ONR

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def fKC (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat) : Bool :=
  bAnd(allN nfg (fun l => memK nC TC (FG l)),
  bAnd(allN ng (fun k => allN nfg fun l =>
      memK nF TF (pcompC n w (mask w) (G k) (pcompC n w (mask w) (FG l)
        (pinvS n w (mask w) (G k))))),
  bAnd(memK nF TF (PX 1),
    allN nC (fun k => bIf(allN nfg fun l => Nat.beq (pcompC n w (mask w) (TC k) (FG l))
        (pcompC n w (mask w) (FG l) (TC k)),
      CFSG.KC.LQT.P.anyN (nat_lit 7) fun e => Nat.beq (TC k) (PX e), true)))))

theorem fK_eq_C (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat) :
    fK n nC nF w ng nfg TC TF G FG PX = fKC n nC nF w ng nfg TC TF G FG PX := by
  unfold fK fKC
  simp only [CFSG.KS.PK.pcompC_eq]

@[expose] noncomputable def fKD (n w nfg : Nat) (TC FG PX : Nat → Nat) (k : Nat) : Bool :=
  bIf(allN nfg fun l => Nat.beq (pcompC n w (mask w) (TC k) (FG l))
      (pcompC n w (mask w) (FG l) (TC k)),
    CFSG.KC.LQT.P.anyN (nat_lit 7) fun e => Nat.beq (TC k) (PX e), true)

@[expose] noncomputable def fKH (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat) : Bool :=
  bAnd(allN nfg (fun l => memK nC TC (FG l)),
  bAnd(allN ng (fun k => allN nfg fun l =>
      memK nF TF (pcompC n w (mask w) (G k) (pcompC n w (mask w) (FG l)
        (pinvS n w (mask w) (G k))))),
    memK nF TF (PX 1)))

@[expose] noncomputable def fKR (n w nfg : Nat) (TC FG PX : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun i => fKD n w nfg TC FG PX (Nat.add lo i))

theorem fKC_split (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat)
    (h : ∀ k < nC, fKD n w nfg TC FG PX k = true) :
    fKC n nC nF w ng nfg TC TF G FG PX = fKH n nC nF w ng nfg TC TF G FG PX := by
  have h4 : allN nC (fun k => fKD n w nfg TC FG PX k) = true := CFSG.KS.Raw.Orb.allN_iff.2 h
  unfold fKD at h4
  unfold fKC fKH
  rw [h4]
  cases memK nF TF (PX 1) <;> rfl

theorem fKD_of_parts (n w nfg : Nat) (TC FG PX : Nat → Nat) (q L nC : Nat) (hc : nC = q * L)
    (hp : ∀ t, t < q → fKR n w nfg TC FG PX (Nat.mul t L) L = true) :
    ∀ k < nC, fKD n w nfg TC FG PX k = true := by
  intro k hk
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at hc; omega
    · exact h0
  have ht : k / L < q := by
    subst hc; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 (hp (k / L) ht) (k % L) (Nat.mod_lt k hL)
  have e : Nat.add (Nat.mul (k / L) L) (k % L) = k := by
    show k / L * L + k % L = k
    rw [Nat.mul_comm]; exact Nat.div_add_mod k L
  rw [e] at h1
  exact h1

end CFSG.KC.ONR

end
