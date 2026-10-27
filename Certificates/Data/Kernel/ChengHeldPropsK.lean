module

public import Certificates.Data.Kernel.ChengHeldSec2K
public import Certificates.Data.ChengHeldPresProps

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeldS2
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def aW (n w P x : ℕ) : ℕ := if x < n then pg w (mask w) P x else 0

@[expose] noncomputable def oW (n w : ℕ) (T : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then pg w (mask w) (T i) 0 else 0

@[expose] noncomputable def pW (n w : ℕ) (T PL : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then pg w (mask w) (T (CFSG.KS.PEnum.parOf PL i)) 0 else 0

@[expose] noncomputable def lW (n : ℕ) (PL : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then CFSG.KS.PEnum.labOf PL i else 0

@[expose] noncomputable def iW (n w IVP a : ℕ) : ℕ := if a < n then pg w (mask w) IVP a else 0

@[expose] noncomputable def gW (w : ℕ) (G : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j < 7 then pg w (mask w) (G j) 0 else 0

@[expose] noncomputable def mW (n w : ℕ) (T : ℕ → ℕ) (IXP a b : ℕ) : ℕ :=
  if a * n + b < n * n then
    pg w (mask w) (T (pg w (mask w) IXP ((a * n + b) / n))) ((a * n + b) % n)
  else 0

@[expose] noncomputable def bindW (n w : ℕ) (T PL : ℕ → ℕ) (IXP IVP : ℕ) : Bool :=
  allN n fun a => bAnd(Nat.blt (pg w (mask w) IXP a) n,
    bAnd(Nat.beq (pg w (mask w) (T (pg w (mask w) IXP a)) 0) a,
    bAnd(Nat.blt (iW n w IVP a) n, bAnd(Nat.beq (mW n w T IXP a (iW n w IVP a)) 0,
      Nat.blt (CFSG.KS.PEnum.parOf PL a) n))))

@[expose] def imgL (m : ℕ → ℕ → ℕ) (inv g : ℕ → ℕ) (rels : List (ℕ × Tm)) (j : ℕ) : ℕ :=
  match rels.find? (fun e => e.1 == j) with
  | some e => evalK m inv g e.2
  | none => 0

@[expose] noncomputable def autRecW (n w : ℕ) (m : ℕ → ℕ → ℕ) (T PL : ℕ → ℕ) (img : ℕ → ℕ)
    (P : ℕ) : Bool :=
  bAnd(Nat.beq (aW n w P 0) 0, allN (n - 1) fun j =>
    Nat.beq (aW n w P (oW n w T (Nat.succ j)))
      (m (img (lW n PL (Nat.succ j))) (aW n w P (pW n w T PL (Nat.succ j)))))

@[expose] noncomputable def homW (n w : ℕ) (T : ℕ → ℕ) (IXP P : ℕ) : Bool :=
  allN n fun x =>
    strictB (T (pg w (mask w) IXP x)) fun R =>
    strictB (T (pg w (mask w) IXP (aW n w P x))) fun S =>
      allN n fun y => Nat.beq (aW n w P (pg w (mask w) R y)) (pg w (mask w) S (aW n w P y))

@[expose] noncomputable def ltW (n w P : ℕ) : Bool :=
  allN n fun x => Nat.blt (aW n w P x) n

@[expose] noncomputable def invoW (n w P : ℕ) : Bool :=
  allN n fun x => Nat.beq (aW n w P (aW n w P x)) x

@[expose] noncomputable def ord3W (n w P x0 : ℕ) : Bool :=
  bAnd(Nat.blt x0 n, bAnd(Bool.not (Nat.beq (aW n w P x0) x0),
    allN n fun x => Nat.beq (aW n w P (aW n w P (aW n w P x))) x))

end CFSG.KC.ChengHeldP

end
