
module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29E8FiveFourCharBase
import CFSG.Certificates.Kernel.C425003Cover
import Certificates.Kernel.C425003Check

public section

open CFSG.LocalAnalysis.RankFourTheoremC.E8FiveFour

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem certificate425003 : ∀ (lam : ZMod 5), (lam = 2 ∨ lam = 3) →
    ∀ (b : Fin Tag.E8.rank → ZMod 5) (ω : List (Fin Tag.E8.rank)), pAct ω b = lam • b →
      ∃ (ω₀ : List (Fin Tag.E8.rank)) (Θ : (Fin 3 → ZMod 5) →+ (Fin Tag.E8.rank → ZMod 5)),
        Function.Injective Θ ∧ pAct ω₀ b = lam • b ∧ ∀ c, pAct ω₀ (Θ c) = lam • Θ c :=
  fun _ hlam _ _ hω =>
    exists_datum_of_check Kernel.C425003.e8FiveFourCheck_true kacRepsN_cover hlam hω

end Certificates
