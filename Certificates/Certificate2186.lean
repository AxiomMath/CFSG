module

public import CFSG.Sporadic.Schreier.LyPermCheckInputs
import Certificates.Kernel.SporSch.Ly.Perm2186

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native in
theorem certificate2186 : ∀ a b c d : Fin 11,
    (∀ j : Fin 4, ∀ x, qCand a b c d (arrFun (qImgArr[j.val]!) x) =
      arrFun (qImgArr[j.val]!) (qCand a b c d x)) →
    (∀ x y, qCand a b c d x = qCand a b c d y → x = y) →
    ∃ m : Fin 12, ∀ x, qCand a b c d x = arrFun (qNaturalCentralizer[m.val]!) x := KernelSporSch.LyPerm.facts

end Certificates
