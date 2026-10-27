module

public import CFSG.Sporadic.ThSchreier.Transporter
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def sepFNats : List ℕ := hexsOf (include_str "Data/SepForm.txt")

@[expose] def decodeWords : ℕ → List ℕ → List (List ℤ)
  | 0, _ => []
  | k + 1, l => ((l.drop 1).take (l.headD 0)).map (fun n => (n : ℤ)) ::
      decodeWords k ((l.drop 1).drop (l.headD 0))

@[expose] def sepWords : List (List ℤ) :=
  decodeWords 124 (natsOf (include_str "Data/SepWords.txt"))

@[expose] def sepRowNats : List ℕ := hexsOf (include_str "Data/SepRows.txt")

end CFSG.Sporadic.ThSchreier
