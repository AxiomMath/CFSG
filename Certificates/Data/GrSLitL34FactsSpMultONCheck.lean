module

public import Certificates.Data.GrSLitL34FactsSpMultJ3Check

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

abbrev onGens : ℕ := TauCeti.SporadicName.ONan.presentation.generatorCount

abbrev onRels : List (List (Fin onGens × Bool)) := TauCeti.SporadicName.ONan.presentation.relators

@[expose] def onExactIdx : List ℕ := List.range 22 ++ [23, 26, 27]

@[expose] def onCentralIdx : List ℕ := [22, 24, 25, 28]

@[expose] def onCoverRels : List (List (Fin onGens × Bool)) :=
  onExactIdx.map (fun i => onRels.getD i []) ++
    onCentralIdx.flatMap (fun i => centralWords (onRels.getD i []))

end CFSG.ComponentClassification.GSThmB.SpMult
