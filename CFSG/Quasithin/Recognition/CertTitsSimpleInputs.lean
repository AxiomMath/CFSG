
module

public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertTitsBase
public meta import CFSG.Quasithin.Recognition.CertPermSimple
public meta import CFSG.Quasithin.Recognition.CertDataTits
public meta import CFSG.Quasithin.Recognition.CertDataTitsSimple
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def rawLines (s : String) : List String := (s.splitOn "\n").drop 1

@[expose] def titsAbWords : List (List ℤ) :=
  (CFSG.YGroups.ModelNative.textLines titsAbWordsText).map CFSG.YGroups.ModelNative.parseInts

@[expose] def titsA : Array ℕ :=
  wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD 0 [])

@[expose] def titsB : Array ℕ :=
  wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD 1 [])

@[expose] def titsPairO : Array (Array ℕ) := #[titsA, titsB]

@[expose] def titsPairWords : Array (List ℤ) :=
  CFSG.YGroups.ModelNative.chainWords titsPairChainText

@[expose] def titsPairBase : List (Fin 1755) := [0, 3, 1, 5, 6, 12, 24]

@[expose] def titsPairStrong : Array (Array ℕ) :=
  (CFSG.YGroups.ModelNative.strongOf 1755 titsPairO titsPairWords).1

@[expose] def titsPairRawWords : Array (List ℤ) := Array.replicate 2 [] ++ titsPairWords

@[expose] def titsLabels : Array ℕ :=
  CFSG.YGroups.ModelNative.parseNats ((CFSG.YGroups.ModelNative.textLines titsLabelsText).headD "")

@[expose] def titsRoots : Array ℕ :=
  CFSG.YGroups.ModelNative.parseNats ((CFSG.YGroups.ModelNative.textLines titsRootsText).headD "")

@[expose] def titsTw : Array (List ℤ) :=
  ((rawLines titsTwText).map CFSG.YGroups.ModelNative.parseInts).toArray

@[expose] def titsHw : Array (List ℤ) :=
  ((rawLines titsHwText).map CFSG.YGroups.ModelNative.parseInts).toArray

end CFSG.Quasithin
