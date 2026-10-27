
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionGenBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitBase
public import CFSG.Monster.B.TwoA.Sp8.QuadInvBase
public import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public meta import CFSG.Monster.B.TwoA.Sp8.QuadDataBase
public meta import CFSG.Monster.B.TwoA.Sp8.QuadInvBase
public meta import CFSG.Monster.B.TwoA.Sp8.ElemAbBase
public meta import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public meta import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.QuadInvInputs
public meta import CFSG.Monster.B.TwoA.Sp8.QuadInvInputs
public meta import CFSG.Monster.B.TwoA.Sp8.T9Base
public import CFSG.Monster.B.TwoA.Sp8.T9Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

@[expose] def cRows : List ℕ := [256, 256, 256, 256, 256, 257, 257, 256, 256, 256, 256, 256, 256,
  256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 260, 256,
  256, 256, 256, 256, 256, 259, 259, 256, 256, 256, 256, 256, 256]

@[expose] def cImg (k : ℕ) : Fin 8 → ZMod 2 := bvec 8 (cRows.getD k 256 - 256)

@[expose] def genM (k : ℕ) (j : Fin 8) : Fin 8 → ZMod 2 := bvec 8 (genRow k j)

@[expose] def affM (k : ℕ) (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  if k < 44 then cImg k + ∑ j, v j • genM k j else ∑ j, v j • triM j

@[expose] def xorRows (m : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc j => if n.testBit j then acc ^^^ m j else acc) 0

@[expose] def affN (k n : ℕ) : ℕ :=
  if k < 44 then (cRows.getD k 256 - 256) ^^^ xorRows (genRow k) n
  else xorRows (fun j => triRows.getD j 0) n

@[expose] def qN (n : ℕ) : Bool :=
  ((List.range 8).foldl (fun acc i => (List.range 8).foldl (fun acc j =>
    if decide (i < j) && n.testBit i && n.testBit j && (gramRows.getD i 0).testBit j then !acc
    else acc) acc) false ^^ n.testBit 6) ^^ n.testBit 7

@[expose] def affTab : Array (Array ℕ) :=
  ((List.range 45).map fun k => ((List.range 256).map (affN k)).toArray).toArray

@[expose] def zeroTab : Array Bool := ((List.range 256).map fun n => !qN n).toArray

end CFSG.Monster.B.TwoA.Sp8
