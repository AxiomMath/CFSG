module

public import Certificates.Data.RudvalisFF81Sp8Codes

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U

@[expose] def conjL : List (List ℕ) :=
  [[83, 97, 114, 128, 52, 55, 7, 8], [56, 161, 178, 64, 171, 59, 11, 4],
    [56, 59, 177, 64, 155, 169, 11, 4]]

@[expose] def pairsChk899103 : Bool :=
  pGens.all spS && conjL.all spS

@[expose] def e0Chk899103 : Bool :=
  let E := tabS e0Gens 81
  tabOK e0Gens E 81 && allCheck (fun x => e0Gens.all (commS x)) E &&
    allCheck (fun x => mulS x (mulS x x) == one8) E

@[expose] def pChk899103 : Bool :=
  tabOK pGens (tabS pGens 243) 243

@[expose] def cpChk899103 : Bool :=
  let E := tabS e0Gens 81
  let mE := indexMap E
  let T := tabS pGens 243
  allCheck (fun p => found E mE p ||
    decide (((List.range T.size).filter fun s => commS p (T.getD s [])).length < 81)) T

@[expose] def conjChk899103 : Bool :=
  let E := tabS e0Gens 81
  let mE := indexMap E
  let T := tabS pGens 243
  allCheck (fun p => !(mulS p (mulS p p) == one8) || p == one8 || found E mE p ||
    conjL.any fun c => found E mE (conjS c p) && mulS c p == mulS (conjS c p) c) T

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
