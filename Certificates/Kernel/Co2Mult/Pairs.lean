module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs

public section

namespace CertificateChecks.KernelCo2Mult

open CFSG.CosetTable CFSG.Sporadic.Recognition.Co2Multiplier

@[expose] def co2Pairs : List (List (Fin 7 × Bool) × List (Fin 2 × Bool)) :=
  co2Rels.map (fun r => (r, [])) ++
    (List.finRange 7).map (fun i => ((i, false) :: co2CommWord i, [])) ++
    [(co2SurjA, [(0, false)]), (co2SurjB, [(1, false)])]

theorem co2CheckWords_eq :
    co2CheckWords = co2Pairs.map fun q => substWord co2GenWords q.1 ++ q.2 := by
  simp [co2CheckWords, co2Pairs, Function.comp_def]

end CertificateChecks.KernelCo2Mult

end
