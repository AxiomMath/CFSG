module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertDataTits
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def titsArray (s : String) : Array ℕ :=
  let l := CFSG.Open.quasithinDigits s
  Array.ofFn (n := 1755) fun i => CFSG.Open.quasithinFixedWidth 4 l i.val % 1755

@[expose] def titsGens : Array (Array ℕ) :=
  #[titsArray CFSG.Open.quasithinTitsData1, titsArray CFSG.Open.quasithinTitsData2]

@[expose] def titsWords : Array (List ℤ) := CFSG.YGroups.ModelNative.chainWords titsChainText

@[expose] def titsBase : List (Fin 1755) := [0, 1, 3, 6, 5, 24, 12]

@[expose] def titsStrong : Array (Array ℕ) :=
  (CFSG.YGroups.ModelNative.strongOf 1755 titsGens titsWords).1

@[expose] def titsRawWords : Array (List ℤ) := Array.replicate 2 [] ++ titsWords

end CFSG.Quasithin
