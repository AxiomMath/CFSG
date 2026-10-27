module

public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public import Certificates.Data.GH74.McLSylowThree
public import Certificates.Data.GH74.McLSylowKlein
import Certificates.Kernel.Sporadic.OddCore.McLKlF

public section

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native in
theorem certificate11005 : subEnumOK 275 200 8 CFSG.Sporadic.SmallOddCore.mclSift sylAGens = true ∧
    (mulClosureH 275 sylAGens 200).1.all (fun a => tblEq 275 (idT 275) (compT 275 a a)) = true ∧
    sylTwoGens.all (fun s => (mulClosureH 275 sylAGens 200).1.all (fun a =>
      memT 275 (mulClosureH 275 sylAGens 200).1 (compT 275 (compT 275 s a) (CFSG.Sporadic.Th.Native.invT 275 s)))) = true :=
  ⟨KernelSpor.McLKl.sub_ok, KernelSpor.McLKl.squares_ok, KernelSpor.McLKl.normalizes_ok⟩

end Certificates

end
