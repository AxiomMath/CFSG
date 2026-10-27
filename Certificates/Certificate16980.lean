
module

public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation
import Certificates.Kernel.GammaU.ResPairBridge

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA in
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.ResPair in
theorem certificate16980 : ∀ i, i = 0 ∨ i = 1 → ∀ c ∈ resConj i, c ≠ idR →
    ∃ (h1 : mulR c (invR c) = idR) (h2 : mulR (invR c) c = idR),
      Violation (genGrp (n2Gens i) ⊔
        (genGrp (n2Gens i)).map (MulAut.conj (eqvOf c (invR c) h1 h2)).toMonoidHom)
        (compOf i) (idR :: hyp10 i) := CFSG.KD.GURPB.resPairFacts

end Certificates
