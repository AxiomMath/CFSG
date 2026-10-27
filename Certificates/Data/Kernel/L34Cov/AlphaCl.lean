module

public import Certificates.Data.Kernel.L34Cov.AlphaGen

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.KC.L34W

@[expose] noncomputable def zaddC (v vA vB eA eB : Nat) : Nat :=
  (v % 4 + eA * (vA % 4) + eB * (vB % 4)) % 4 +
    4 * ((v / 4 % 4 + eA * (vA / 4 % 4) + eB * (vB / 4 % 4)) % 4) +
    16 * ((v / 16 + eA * (vA / 16) + eB * (vB / 16)) % 3)

@[expose] noncomputable def zEnt (α : Nat) : Nat := 12 * (α % 4) + 3 * (α / 4 % 4) + α / 16

@[expose] noncomputable def zlabOK (d n a b c α₁ α₂ α₃ : Nat) : Bool :=
  andB (Nat.beq ((d % 48 / 12 + c % 48 / 12 * (α₁ % 4) + c % 12 / 3 * (α₂ % 4) +
      c % 3 * (α₃ % 4)) % 4) ((n % 48 / 12 + a % 48 / 12 + b % 48 / 12) % 4))
    (andB (Nat.beq ((d % 12 / 3 + c % 48 / 12 * (α₁ / 4 % 4) + c % 12 / 3 * (α₂ / 4 % 4) +
        c % 3 * (α₃ / 4 % 4)) % 4) ((n % 12 / 3 + a % 12 / 3 + b % 12 / 3) % 4))
      (Nat.beq ((d % 3 + c % 48 / 12 * (α₁ / 16) + c % 12 / 3 * (α₂ / 16) +
        c % 3 * (α₃ / 16)) % 3) ((n % 3 + a % 3 + b % 3) % 3)))

@[expose] noncomputable def clStepOK (T A : Nat → Nat) (i l g α₁ α₂ α₃ : Nat) : Bool :=
  bindB (ent A i l) fun a => bindB (ent A i g) fun b => bindB (ent T l g) fun c =>
  bindB (ent A i (c / 48)) fun d => bindB (ent T (a / 48) (b / 48)) fun n =>
    andB (Nat.beq (d / 48) (n / 48)) (zlabOK d n a b c α₁ α₂ α₃)

@[expose] noncomputable def clStepsOK (T A : Nat → Nat) (i α₁ α₂ α₃ l : Nat) : Bool :=
  andB (clStepOK T A i l 1 α₁ α₂ α₃) (andB (clStepOK T A i l 2 α₁ α₂ α₃)
    (andB (clStepOK T A i l 16 α₁ α₂ α₃) (clStepOK T A i l 20 α₁ α₂ α₃)))

@[expose] noncomputable def alClOK (V : Nat) (TA TB T : Nat → Nat) (F : List (List Nat))
    (A : Nat → Nat) (uA uB : List Nat) (i : Nat) : Bool :=
  bindB (zvC V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 []))) fun vA =>
  bindB (zvC V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 []))) fun vB =>
  bindB (zvC V TA TB (substC [uA, uB] (F.getD 10 []))) fun v₁ =>
  bindB (zvC V TA TB (substC [uA, uB] (F.getD 11 []))) fun v₂ =>
  bindB (zvC V TA TB (substC [uA, uB] (F.getD 12 []))) fun v₃ =>
    andB (zvOK V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 [])) vA)
    (andB (zvOK V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 [])) vB)
    (andB (zvOK V TA TB (substC [uA, uB] (F.getD 10 [])) v₁)
    (andB (zvOK V TA TB (substC [uA, uB] (F.getD 11 [])) v₂)
    (andB (zvOK V TA TB (substC [uA, uB] (F.getD 12 [])) v₃)
    (andB (Nat.beq (ent A i 0) 0)
    (bindB (zaddC v₁ vA vB (eN 0 (F.getD 10 [])) (eN 1 (F.getD 10 []))) fun α₁ =>
     bindB (zaddC v₂ vA vB (eN 0 (F.getD 11 [])) (eN 1 (F.getD 11 []))) fun α₂ =>
     bindB (zaddC v₃ vA vB (eN 0 (F.getD 12 [])) (eN 1 (F.getD 12 []))) fun α₃ =>
      andB (andB (Nat.blt α₁ 48) (Nat.beq (ent A i 64) (zEnt α₁)))
        (andB (andB (Nat.blt α₂ 48) (Nat.beq (ent A i 65) (zEnt α₂)))
          (Mono.allR 0 64 (clStepsOK T A i α₁ α₂ α₃)))))))))

end CFSG.KC.L34Cov

end
