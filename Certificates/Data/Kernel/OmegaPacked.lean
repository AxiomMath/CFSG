module

public import CFSG.LieType.Ree.OmegaWordCheck
public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace Certificates.OmegaPacked

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley.RootOps

@[expose] def colOf (w m X k : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul w k)) m

@[expose] def stepE (w m U V d : Nat) (D : Nat × Nat) (e : Entry) : Nat × Nat :=
  if Nat.beq (e.2.2.natAbs % 2) 0 then D else
  let cu := colOf w m U e.2.1
  let cv := colOf w m V e.2.1
  let a := if Nat.beq d 0 then cu else if Nat.beq d 1 then cv else Nat.xor cu cv
  let b := if Nat.beq d 0 then cv else if Nat.beq d 1 then Nat.xor cu cv else cu
  (Nat.xor D.1 (Nat.shiftLeft a (Nat.mul w e.1)), Nat.xor D.2 (Nat.shiftLeft b (Nat.mul w e.1)))

@[expose] def stepF (τ : Tag) (w m : Nat) (M : Nat × Nat) (f : ℕ × ℤ × ℕ) : Nat × Nat :=
  if Nat.beq ((famSign τ f.1 * f.2.1).natAbs % 2) 0 then M else
  let D := [1, 2, 3].foldl (fun D k =>
    (entries τ f.1 k).foldl (stepE w m M.1 M.2 ((k * f.2.2) % 3)) D) (0, 0)
  (Nat.xor M.1 D.1, Nat.xor M.2 D.2)

@[expose] def idU (w : Nat) : Nat :=
  (List.range w).foldl (fun a i => Nat.lor a (Nat.shiftLeft 1 (Nat.mul (w + 1) i))) 0

@[expose] def prodP (τ : Tag) (w m : Nat) (L : List (ℕ × ℤ × ℕ)) : Nat × Nat :=
  L.foldl (stepF τ w m) (idU w, 0)

@[expose] def entriesOk (τ : Tag) (w g : Nat) : Bool :=
  [1, 2, 3].all (fun k => (entries τ g k).all fun e => Nat.blt e.1 w && Nat.blt e.2.1 w) &&
    Nat.ble (2 * w * w + ([1, 2, 3].foldl (fun n k => n + (entries τ g k).length) 0) * (2 * w + 1))
      65536

@[expose] def omegaCheckP (τ : Tag) (L L' : List (ℕ × ℤ × ℕ)) : Bool :=
  (L ++ L').all (fun f => Nat.blt f.1 τ.rootCertificate.roots.length && entriesOk τ (dim τ) f.1) &&
    Nat.beq (prodP τ (dim τ) (Nat.shiftLeft 1 (dim τ) - 1) L).1
      (prodP τ (dim τ) (Nat.shiftLeft 1 (dim τ) - 1) L').1 &&
    Nat.beq (prodP τ (dim τ) (Nat.shiftLeft 1 (dim τ) - 1) L).2
      (prodP τ (dim τ) (Nat.shiftLeft 1 (dim τ) - 1) L').2

end Certificates.OmegaPacked
