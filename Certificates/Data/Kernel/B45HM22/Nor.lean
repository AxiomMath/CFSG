module

public import Certificates.Data.Kernel.B45M12.Four
public import CFSG.Quasithin.Background.SmithB45HM22Chk
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.KC.B45HM22

open CFSG.KC.B45M12 CFSG.Quasithin.HM22 CFSG.CharacterTheory.SteinbergBY

@[expose] noncomputable def progC (p : List (ℕ × Bool)) : List (ℕ × ℕ) :=
  p.map fun e => (e.1, Bool.rec 1 2 e.2)

@[expose] noncomputable def termsC (t : List (List Bool × FieldFour)) : List (List ℕ × ℕ) :=
  t.map fun x => (x.1.map (Bool.rec 1 2), Bool.toNat x.2.re + 2 * Bool.toNat x.2.im)

@[expose] noncomputable def norP (n : ℕ) (d : PSpin) (Ga Gb : List (ℕ × ℕ)) : Bool :=
  let Ha := trF4 n Ga
  let Hb := trF4 n Gb
  let terms := termsC d.terms
  let z := sumTF4 Ha Hb terms d.w
  Nat.ble Ga.length n && Nat.ble Gb.length n && Nat.ble d.Q.length n &&
    Nat.ble d.Qi.length n && Nat.ble d.R.length n && Nat.ble d.Si.length n &&
    Nat.ble d.Ti.length n &&
    Nat.beq (d.spin.length + 1) n && Nat.beq (d.dual.length + 1) n &&
    eqF4 n (mulF4 d.Qi d.Q) (idF4 n) &&
    eqF4 n ((trF4 n d.R).map fun r => actF4 (trF4 n d.Q) (sumTF4 Ha Hb terms r)) (diag0F4 n) &&
    eqF4 n (mulF4 d.Si (spinF4M Ga Gb (d.Q.headD (0, 0)) (progC d.spin))) (idF4 n) &&
    Nat.beq (z.1 % 2 ^ n) 0 && Nat.beq (z.2 % 2 ^ n) 0 &&
    eqF4 n (mulF4 (spinF4M Ha Hb d.w (progC d.dual)) (trF4 n d.Ti)) (idF4 n)

end CFSG.KC.B45HM22

end
