module

public import Certificates.Kernel.Co2Jc.OffDefs

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

@[expose] noncomputable def mulRowK (s : Nat) : Bool :=
  (List.range 256).all fun i => decide (mulL s i < 256) &&
    Nat.beq (PT (mulL s i)) (CFSG.KC.M1F2.mulF 10 (PT i) (PT s))

@[expose] noncomputable def fixRowK (i : Nat) : Bool :=
  (List.range 1024).all fun m => (FX i).testBit m == Nat.beq (CFSG.KC.M1F2.vmF 10 (PT i) m) m

@[expose] noncomputable def bfsStepN (i : Nat) (o : Option Nat) (k : Nat) : Option Nat :=
  o.bind fun n =>
    if mulL (gI k) i < n then some n else if mulL (gI k) i = n then some (n + 1) else none

@[expose] noncomputable def bfsSim : Nat → Nat → Nat → Bool
  | 0, n, _ => n == 256
  | fuel + 1, n, i =>
    if i < n then
      match (List.range 4).foldl (bfsStepN i) (some n) with
      | none => false
      | some n' => bfsSim fuel n' (i + 1)
    else n == 256

@[expose] noncomputable def stepLK (l : List Nat) (s : Nat) : List Nat :=
  (List.range 256).filter fun i => l.contains i || (l.map (mulL s)).contains i

@[expose] noncomputable def offMaskL (l : List Nat) : Nat :=
  l.foldl (fun acc i => Nat.lor acc (Nat.shiftLeft 1 i)) 0

@[expose] noncomputable def stepMask (l : List Nat) (s : Nat) : Nat :=
  l.foldl (fun acc i => Nat.lor (Nat.lor acc (Nat.shiftLeft 1 i)) (Nat.shiftLeft 1 (mulL s i))) 0

@[expose] noncomputable def stepT (l : List Nat) (q : Nat) : Bool :=
  (List.range 256).all fun s =>
    (l.contains s) || Nat.beq s 0 || !(Nat.beq (mulL s s) 0) ||
      !(l.all fun i => Nat.beq (mulL s i) (mulL i s)) ||
      (decide (stI q s < 715) && Nat.beq (offSM (stI q s)) (stepMask l s))

@[expose] noncomputable def offSMOK : Bool :=
  subs.zipIdx.all fun p => Nat.beq (offSM p.2) (offMaskL p.1) && decide (p.1.Pairwise (· < ·))

@[expose] noncomputable def andM (l : List Nat) : Nat :=
  l.foldl (fun acc i => acc &&& FX i) (2 ^ 1024 - 1)

@[expose] noncomputable def boundT (l : List Nat) : Bool :=
  CFSG.KC.M1F2.strictB (andM l) fun A =>
    decide (l.length * ((List.range 1024).filter fun m => A.testBit m).length ≤ 512)

@[expose] noncomputable def stepC (c : Nat) : Bool :=
  ((subs.zipIdx.drop (32 * c)).take 32).all fun p => stepT p.1 p.2

@[expose] noncomputable def stepR (lo n : Nat) : Bool :=
  ((subs.zipIdx.drop lo).take n).all fun p => stepT p.1 p.2

theorem stepC_eq (c : Nat) : stepC c = stepR (32 * c) 32 := rfl

theorem stepR_add (lo a b : Nat) : stepR lo (a + b) = (stepR lo a && stepR (lo + a) b) := by
  unfold stepR
  have e : (subs.zipIdx.drop lo).drop a = subs.zipIdx.drop (lo + a) := by
    simp [List.drop_drop, Nat.add_comm]
  rw [List.take_add, List.all_append, e]

theorem stepR_chunks (lo m : Nat) : ∀ k : Nat, (∀ q < k, stepR (lo + q * m) m = true) →
    stepR lo (k * m) = true
  | 0, _ => by simp [stepR]
  | k + 1, h => by
    rw [Nat.add_mul, Nat.one_mul, stepR_add, stepR_chunks lo m k (fun q hq => h q (by omega)),
      h k (by omega)]
    all_goals rfl

theorem stepC_of (c : Nat) (h : ∀ q < 4, stepR (32 * c + q * 8) 8 = true) : stepC c = true := by
  have e : stepR (32 * c) (4 * 8) = true := stepR_chunks (32 * c) 8 4 h
  rw [stepC_eq]
  exact e

theorem stepC_of_pieces (base n : Nat)
    (h : ∀ t < 4 * n, stepR (32 * (base + t / 4) + t % 4 * 8) 8 = true) :
    ∀ d < n, stepC (base + d) = true := by
  intro d hd
  refine stepC_of _ fun q hq => ?_
  have := h (4 * d + q) (by omega)
  rwa [show (4 * d + q) / 4 = d by omega, show (4 * d + q) % 4 = q by omega] at this

@[expose] noncomputable def boundC (c : Nat) : Bool :=
  ((subs.drop (32 * c)).take 32).all boundT

end CertificateChecks.KernelCo2Jc
