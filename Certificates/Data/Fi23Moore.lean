module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public import Certificates.Data.Fi24Moore
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import Certificates.Data.Fi24Moore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative

set_option compiler.extract_closed false

@[expose] def mooreTab23 (O : WOrbit) (D Bi : Table) (P : List Nat) (j : Nat) : Table :=
  starWordTab O D Bi (mooreWord P j)

@[expose] def mooreRelOK23 (A : Nat → Table) (M : Nat) : Bool :=
  eqTab (powT 31671 3 (A 1)) (idT 31671) &&
    ((List.range (M + 1)).all fun j => j < 2 ||
      (eqTab (powT 31671 2 (A j)) (idT 31671) &&
        eqTab (powT 31671 3 (compT 31671 (A (j - 1)) (A j))) (idT 31671))) &&
    ((List.range (M + 1)).all fun i => (List.range (M + 1)).all fun j =>
      i < 1 || j < i + 2 || eqTab (powT 31671 2 (compT 31671 (A i) (A j))) (idT 31671))

@[expose] def mooreChain23 (O : WOrbit) (D Bi W : Table) (k : Nat) : List Nat :=
  chainOf (commB O D Bi) (fixList W) k

@[expose] def mooreAt23OK (O : WOrbit) (D Bi W : Table) (k : Nat) : Bool :=
  let P := mooreChain23 O D Bi W k
  P.length == k && P.all (· < 31671) &&
    mooreRelOK23 (mooreTab23 O D Bi P) (k - 1) && !eqTab (mooreTab23 O D Bi P 1) (idT 31671) &&
    ((List.range k).all fun j => j < 1 ||
      eqTab (compT 31671 (mooreTab23 O D Bi P j) W) (compT 31671 W (mooreTab23 O D Bi P j)))

@[expose] def fi23FiveMooreOK (O : WOrbit) : Bool :=
  mooreAt23OK O (dTable O) (genTables O (-2)) (eTab O) 6

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
