module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadicInputs
import Certificates.Kernel.LocalQT.Word.Mathieu
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 in
open CFSG.Blueprint CFSG.SectionRank in
theorem certificate4103 : (mathieuWord m11LocA m11LocB m11WordX.toList ^ 3 = 1)
    ∧ (mathieuWord m11LocA m11LocB m11WordY.toList ^ 3 = 1)
    ∧ (mathieuWord m11LocA m11LocB m11WordX.toList * mathieuWord m11LocA m11LocB m11WordY.toList =
            mathieuWord m11LocA m11LocB m11WordY.toList *
              mathieuWord m11LocA m11LocB m11WordX.toList)
    ∧ (Function.Injective fun t : Fin 3 × Fin 3 =>
            mathieuWord m11LocA m11LocB m11WordX.toList ^ (t.1 : ℕ) *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ (t.2 : ℕ))
    ∧ (mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordX.toList *
              (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
            mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ 0)
    ∧ (mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordY.toList *
              (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
            mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordX.toList ^ 3 = 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordY.toList ^ 3 = 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordX.toList * mathieuWord m23LocA m23LocB m23WordY.toList =
            mathieuWord m23LocA m23LocB m23WordY.toList *
              mathieuWord m23LocA m23LocB m23WordX.toList)
    ∧ (Function.Injective fun t : Fin 3 × Fin 3 =>
            mathieuWord m23LocA m23LocB m23WordX.toList ^ (t.1 : ℕ) *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ (t.2 : ℕ))
    ∧ (mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordX.toList *
              (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
            mathieuWord m23LocA m23LocB m23WordX.toList ^ 1 *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ 2)
    ∧ (mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordY.toList *
              (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
            mathieuWord m23LocA m23LocB m23WordX.toList ^ 0 *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ 2) := KernelLocalQT.three_cover

end Certificates
