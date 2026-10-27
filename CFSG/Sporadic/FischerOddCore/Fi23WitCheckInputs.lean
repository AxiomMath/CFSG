module

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

@[expose] def fi23W0 : List Int := [1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2]

@[expose] def fi23W1 : List Int :=
  [1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2]

@[expose] def fi23W2 : List Int := [1, -2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def fi23BrayT (R G Gi : Table) (e : Nat) (odd : Bool) : Table :=
  if odd then compT 31671 G (powT 31671 e (compT 31671 R (compT 31671 Gi (compT 31671 R G))))
  else powT 31671 e (compT 31671 R (compT 31671 Gi (compT 31671 R G)))

@[expose] def fi23CommT (X Y : Table) : Table :=
  compT 31671 X (compT 31671 Y (compT 31671 (invT 31671 X) (invT 31671 Y)))

@[expose] def fi23Common (R E₁ E₂ : Table) : Nat :=
  (List.range 31671).countP fun i => ap R i == i && ap E₁ i == i && ap E₂ i == i

@[expose] def fi23WitOK (R G : Table) (e : Nat) (odd : Bool) : Bool :=
  invOK 31671 G (invT 31671 G) &&
    invOK 31671 (fi23BrayT R G (invT 31671 G) e odd)
      (invT 31671 (fi23BrayT R G (invT 31671 G) e odd)) &&
    compT 31671 (fi23BrayT R G (invT 31671 G) e odd) R ==
      compT 31671 R (fi23BrayT R G (invT 31671 G) e odd)

@[expose] def fi23CT (O : WOrbit) (R : Table) (w : List Int) (e : Nat) (odd : Bool) : Table :=
  fi23BrayT R (wordT 31671 (genTables O) w) (invT 31671 (wordT 31671 (genTables O) w)) e odd

@[expose] def fi23CaseOK (O : WOrbit) (R : Table) (e₀ e₁ e₂ : Nat) (o₀ o₁ o₂ : Bool) : Bool :=
  fi23WitOK R (wordT 31671 (genTables O) fi23W0) e₀ o₀ &&
    fi23WitOK R (wordT 31671 (genTables O) fi23W1) e₁ o₁ &&
    fi23WitOK R (wordT 31671 (genTables O) fi23W2) e₂ o₂ &&
    fi23Common R (fi23CommT (fi23CT O R fi23W1 e₁ o₁) (fi23CT O R fi23W0 e₀ o₀))
      (fi23CommT (fi23CT O R fi23W2 e₂ o₂) (fi23CT O R fi23W0 e₀ o₀)) == 2

@[expose] def fi23Fix (P : Table) : Nat := (List.range 31671).countP fun i => ap P i == i

@[expose] def fi23WordW : List Int := [2, 2, 1, 2, 2, 1, 2]

@[expose] def fi23U2T (O : WOrbit) : Table :=
  compT 31671 (dTab O) (compT 31671 (genTables O 1) (compT 31671 (dTab O) (genTables O (-1))))

@[expose] def fi23U3T (O : WOrbit) : Table :=
  compT 31671 (fi23U2T O) (compT 31671 (wordT 31671 (genTables O) fi23WordW)
    (compT 31671 (dTab O) (invT 31671 (wordT 31671 (genTables O) fi23WordW))))

@[expose] def fi23RepOK (O : WOrbit) : Bool :=
  invOK 31671 (wordT 31671 (genTables O) fi23WordW)
      (invT 31671 (wordT 31671 (genTables O) fi23WordW)) &&
    compT 31671 (fi23U2T O) (fi23U2T O) == idT 31671 && !(isIdT (fi23U2T O)) &&
    fi23Fix (fi23U2T O) == 695 &&
    compT 31671 (fi23U3T O) (fi23U3T O) == idT 31671 && !(isIdT (fi23U3T O)) &&
    fi23Fix (fi23U3T O) == 183

@[expose] def fi23WitChecks (O : WOrbit) : Bool :=
  fi23CaseOK O (compT 31671 (dTab O) (treeActTab O (dTab O) (genTables O (-2)) 1))
      2 2 3 true true false &&
    fi23CaseOK O (compT 31671 (compT 31671 (dTab O) (treeActTab O (dTab O) (genTables O (-2)) 1))
      (treeActTab O (dTab O) (genTables O (-2)) 39)) 30 9 9 false false false &&
    fi23RepOK O

end CFSG.Sporadic.FischerOddCore
