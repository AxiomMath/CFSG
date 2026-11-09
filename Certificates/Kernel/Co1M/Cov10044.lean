module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Monster.GMS.Facts.Co1OddPairs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Monster.GMS.S365RootInputs
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10044
public meta import Certificates.Kernel.VecCert.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.VecK CFSG.KD.Co1M CFSG.Sporadic.Co1.Module.Pairs

@[expose] noncomputable def covF44 (p : Nat) : Bool :=
  !orthAll rootGs (lk CertificateChecks.KernelVec.Co1.Pt 32 p) ||
    TL.contains (lk CertificateChecks.KernelVec.Co1.Pt 32 p)

@[expose] noncomputable def parR44 (x n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => Bool.rec (motive := fun _ => Bool) ih (Bool.rec (motive := fun _ => Bool) true false ih)
      (Nat.beq (Nat.land (Nat.shiftRight x j) 1) 1)) n

@[expose] def rootGsL44 : List Nat :=
  [11188443, 10379264, 1286564, 1430296, 1421732, 7973247, 14194660, 7230446, 9412022, 4602249,
    10249669, 16310113, 4284337, 12199149, 9076597, 16730443]

@[expose] noncomputable def orthL44 (gs : List Nat) (u : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => Bool.rec (motive := fun _ => Bool) ih false (parR44 (Nat.land u g) 24)) gs

@[expose] noncomputable def covK44 (p : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (TL.contains (lk CertificateChecks.KernelVec.Co1.Pt 32 p))
    (orthL44 rootGsL44 (lk CertificateChecks.KernelVec.Co1.Pt 32 p))

theorem testBit_eq44 (x j : Nat) : x.testBit j = Nat.beq (Nat.land (Nat.shiftRight x j) 1) 1 := by
  have h : Nat.land (Nat.shiftRight x j) 1 = (x >>> j) % 2 := Nat.and_one_is_mod _
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one (x >>> j) with h2 | h2 <;>
    simp [h2, Nat.testBit, Nat.one_and_eq_mod_two] <;> rfl

theorem fold_eq44 (x : Nat) :
    ∀ n, (List.range n).foldl (fun acc j => acc ^^ x.testBit j) false = parR44 x n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, fold_eq44 x n, List.foldl_cons, List.foldl_nil,
      testBit_eq44]
    change _ = Bool.rec (motive := fun _ => Bool) (parR44 x n)
      (Bool.rec (motive := fun _ => Bool) true false (parR44 x n)) (Nat.beq (Nat.land (Nat.shiftRight x n) 1) 1)
    generalize Nat.beq (Nat.land (Nat.shiftRight x n) 1) 1 = b
    generalize parR44 x n = a
    cases a <;> cases b <;> rfl

theorem parity24_eq44 (x : Nat) : parity24 x = parR44 x 24 := fold_eq44 x 24

theorem orthAll_eq44 (u : Nat) : ∀ gs, orthAll gs u = orthL44 gs u
  | [] => rfl
  | g :: gs => by
    have e : u &&& g = Nat.land u g := rfl
    rw [orthAll, List.all_cons, ← orthAll, orthAll_eq44 u gs, parity24_eq44, e]
    change _ = Bool.rec (motive := fun _ => Bool) (orthL44 gs u) false (parR44 (Nat.land u g) 24)
    generalize orthL44 gs u = a
    generalize parR44 (Nat.land u g) 24 = b
    cases a <;> cases b <;> rfl

theorem rootGs_eq44 : rootGs = rootGsL44 := by
  have h : (rootGs == rootGsL44) = true := by quickRfl
  exact beq_iff_eq.mp h

theorem covF44_eq44 (p : Nat) : covF44 p = covK44 p := by
  rw [covF44, rootGs_eq44, orthAll_eq44]
  change _ = Bool.rec (motive := fun _ => Bool) true _ _
  generalize orthL44 rootGsL44 (lk CertificateChecks.KernelVec.Co1.Pt 32 p) = a
  cases a <;> rfl

end CertificateChecks.KernelCo1M

open Lean Elab Command CFSG.KC.VecGen in
elab "#c10044_cover" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := `CertificateChecks.KernelCo1M
  let f := mkConst ``CertificateChecks.KernelCo1M.covK44
  let pf ← coverOf (P ++ `C44) (fun _ => true) "cov" f (mkRawNatLit 98280) 98280 256
  let ty ← Meta.MetaM.run' (Meta.inferType pf)
  addThm (P ++ `cov44K) ty pf

#c10044_cover

namespace CertificateChecks.KernelCo1M

theorem cov44All : ∀ p < 98280, covF44 p = true := fun p hp =>
  (covF44_eq44 p).trans (cov44K p hp)

end CertificateChecks.KernelCo1M

end
