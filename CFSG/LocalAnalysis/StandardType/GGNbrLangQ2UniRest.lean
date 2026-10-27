module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggBstarAbelianPreimageJUniS1On_offA_of_residual
    (hRes : GGBstarAbelianPreimageJUniS1On (fun p lab => (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨
      (lab.tag = .F4 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p = 3))) :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag ≠ .A ∧ lab.tag ≠ .twA) :=
  ggBstarAbelianPreimageJUniS1On_of_classical_excRest
    ((ggBstarAbelianPreimageJUniS1On_classical.or hRes).mono (fun _ _ h => by tauto))

end CFSG.StandardType
