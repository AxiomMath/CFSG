module

public import CFSG.RankThree.Native.HSMcLAuxData
public import CFSG.Sporadic.Schreier.PairHSCert
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.RankThree.Native.HSMcLAuxData
public meta import CFSG.RankThree.Native.HSMcLSmallData
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.RankThree.Native.HSMcLSmallData

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier

@[expose] def hs100BaseArr : Array ℕ := (hs100Base.map Fin.val).toArray

@[expose] def hs100RBaseArr : Array ℕ := (hs100RBase.map Fin.val).toArray

@[expose] def mcl275RBaseArr : Array ℕ := (mcl275RBase.map Fin.val).toArray

@[expose] def hs100KappaEquiv (a g : Array ℕ) : Bool :=
  allLt 3850 fun x =>
    let y := a[x]!
    let p := g[hs100Kappa1[x]!]!
    let q := g[hs100Kappa2[x]!]!
    (hs100Kappa1[y]! == p && hs100Kappa2[y]! == q) ||
      (hs100Kappa1[y]! == q && hs100Kappa2[y]! == p)

@[expose] def hs100K1 (x : Fin 3850) : Fin 100 :=
  ⟨hs100Kappa1[(x : ℕ)]! % 100, Nat.mod_lt _ (by norm_num)⟩

@[expose] def hs100K2 (x : Fin 3850) : Fin 100 :=
  ⟨hs100Kappa2[(x : ℕ)]! % 100, Nat.mod_lt _ (by norm_num)⟩

@[expose] def hs100Kappa (x : Fin 3850) : Finset (Fin 100) := {hs100K1 x, hs100K2 x}

end CFSG.RankThree.Native
