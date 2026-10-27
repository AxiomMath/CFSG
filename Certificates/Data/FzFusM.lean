module

public import Certificates.Data.FzJ36
public import Certificates.Data.FzFusCls

public section

namespace Certificates.FzFus

open Certificates.FzJ36

@[expose] def lett : Q8 → Nat
  | QuaternionGroup.a i => if i.val % 2 = 0 then 0 else 1
  | QuaternionGroup.xa i => if i.val % 2 = 0 then 2 else 3

@[expose] def qL (n : Nat) : Q8 :=
  if n = 1 then QuaternionGroup.a 1
  else if n = 2 then QuaternionGroup.xa 0
  else QuaternionGroup.xa 3

@[expose] def mkE (a b c : Q8) : Model := ⟨(a, b, c), 1⟩

@[expose] def mkY (a b c : Q8) : Model := ⟨(a, b, c), Multiplicative.ofAdd 1⟩

@[expose] def typeCls : Nat → Nat → Nat → Cls
  | 1, 1, 1 => .III
  | 1, 1, 2 => .IIJ
  | 1, 1, 3 => .IIK
  | 1, 2, 1 => .IJI
  | 1, 2, 2 => .IJJ
  | 1, 2, 3 => .IJK
  | 1, 3, 1 => .IKI
  | 1, 3, 2 => .IKJ
  | 1, 3, 3 => .IKK
  | 2, 1, 1 => .IJI
  | 2, 1, 2 => .IJJ
  | 2, 1, 3 => .IJK
  | 2, 2, 1 => .JJI
  | 2, 2, 2 => .JJJ
  | 2, 2, 3 => .JJK
  | 2, 3, 1 => .JKI
  | 2, 3, 2 => .JKJ
  | 2, 3, 3 => .JKK
  | 3, 1, 1 => .IKI
  | 3, 1, 2 => .IKJ
  | 3, 1, 3 => .IKK
  | 3, 2, 1 => .JKI
  | 3, 2, 2 => .JKJ
  | 3, 2, 3 => .JKK
  | 3, 3, 1 => .KKI
  | 3, 3, 2 => .KKJ
  | 3, 3, 3 => .KKK
  | _, _, _ => .III

@[expose] def negBit (q : Q8) : Nat := if q = QuaternionGroup.a 2 then 1 else 0

@[expose] def clsOf (m : Model) : Cls :=
  if m.right = 1 then
    if lett m.left.1 ≠ 0 ∧ lett m.left.2.1 ≠ 0 ∧ lett m.left.2.2 ≠ 0 then
      typeCls (lett m.left.1) (lett m.left.2.1) (lett m.left.2.2)
    else if negBit m.left.1 = negBit m.left.2.1 ∧ negBit m.left.2.2 ≠ negBit m.left.1 then .z3
    else .z12
  else if lett m.left.2.2 = 0 then .lam
  else if lett m.left.2.2 = 1 then .oI
  else if lett m.left.2.2 = 2 then .oJ
  else .oK

@[expose] def rep : Cls → Model
  | .III => mkE (qL 1) (qL 1) (qL 1)
  | .IIJ => mkE (qL 1) (qL 1) (qL 2)
  | .IIK => mkE (qL 1) (qL 1) (qL 3)
  | .JJI => mkE (qL 2) (qL 2) (qL 1)
  | .JJJ => mkE (qL 2) (qL 2) (qL 2)
  | .JJK => mkE (qL 2) (qL 2) (qL 3)
  | .KKI => mkE (qL 3) (qL 3) (qL 1)
  | .KKJ => mkE (qL 3) (qL 3) (qL 2)
  | .KKK => mkE (qL 3) (qL 3) (qL 3)
  | .IJI => mkE (qL 1) (qL 2) (qL 1)
  | .IJJ => mkE (qL 1) (qL 2) (qL 2)
  | .IJK => mkE (qL 1) (qL 2) (qL 3)
  | .IKI => mkE (qL 1) (qL 3) (qL 1)
  | .IKJ => mkE (qL 1) (qL 3) (qL 2)
  | .IKK => mkE (qL 1) (qL 3) (qL 3)
  | .JKI => mkE (qL 2) (qL 3) (qL 1)
  | .JKJ => mkE (qL 2) (qL 3) (qL 2)
  | .JKK => mkE (qL 2) (qL 3) (qL 3)
  | .oI => mkY (qL 1) (qL 1) (qL 1)
  | .oJ => mkY (qL 2) (qL 2) (qL 2)
  | .oK => mkY (qL 3) (qL 3) (qL 3)
  | .lam => ⟨1, Multiplicative.ofAdd 1⟩
  | .z12 => mkE (QuaternionGroup.a 2) 1 1
  | .z3 => mkE 1 1 (QuaternionGroup.a 2)

@[expose] def tM : Model := mkE (qL 1) (qL 1) (qL 1)

@[expose] def x1M : Model := mkE (QuaternionGroup.a 2) (qL 1) (qL 1)

@[expose] def x2M : Model := mkE (qL 1) (QuaternionGroup.a 2) (qL 1)

@[expose] def lamM : Model := ⟨1, Multiplicative.ofAdd 1⟩

@[expose] def z1M : Model := mkE (QuaternionGroup.a 2) 1 1

@[expose] def z3M : Model := mkE 1 1 (QuaternionGroup.a 2)

end Certificates.FzFus
