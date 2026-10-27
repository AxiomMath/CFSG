module

public import Certificates.Data.Insp443He
public import CFSG.Quasithin.Vol2.KGFactC31WordBasis
import Certificates.Kernel.SchreierFam.He725F

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.He
  CFSG.SectionRank.QTK.Insp443.He in
theorem certificate725002 :
    ([x7W, c7W].all (lettersOK 2) && fixB bs [wA x7W] 7 && !(fixB bs [wA x7W] 1) &&
      normsW bs qA (wA x7W) (wAi x7W) && normsW bs qA (wA c7W) (wAi c7W)) = true ∧
    (rawChainOK 8330 (arrO l7S l7GenW.length) l7S (arrBase l7B) l7Wd 4 &&
      ((rawOrbitSizes 8330 l7S (arrBase l7B)).prod == 21504)) = true :=
  ⟨KernelSchreierFam.He725.part1, KernelSchreierFam.He725.part2⟩

end Certificates
