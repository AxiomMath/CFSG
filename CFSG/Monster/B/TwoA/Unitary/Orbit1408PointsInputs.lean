
module

public import CFSG.Monster.B.TwoA.Unitary.SemilinearBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Form
import CFSG.Fischer.F4
public meta import CFSG.Monster.B.TwoA.Unitary.PlanesBase

public noncomputable section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer
open CFSG.Monster.B.Classical.UnitarySix (bar)

@[expose] def singVec (i : Fin 693) : V6 := vec6 b6SingArr[(i : ℕ)]!

@[expose] def enc6 (v : V6) : ℕ :=
  (List.finRange 6).foldr (fun t acc => ((v t).code : ℕ) * 4 ^ (t : ℕ) + acc) 0

@[expose] def singLook (v : V6) : Fin 693 :=
  ⟨b6SingArr.toList.idxOf (enc6 ((v (piv v))⁻¹ • v)) % 693, Nat.mod_lt _ (by norm_num)⟩

end CFSG.Monster.B.TwoA.Unitary
