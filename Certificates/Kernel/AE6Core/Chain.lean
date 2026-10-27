module

public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6ModelCore
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.AE6ModelCore
public import Certificates.Kernel.SporSch.Mathieu.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Core

open CFSG.KS.SporSch.MOCG

meta def letterW (wd : List Nat) : Array Nat :=
  wd.foldr (fun i acc => comp (CFSG.EvenSmallLie.OmegaEight.genArrs[i]!) acc) (idA 360)

meta def gensPL : Array (Array Nat) :=
  let G := CFSG.EvenSmallLie.OmegaEight.genArrs.extract 0 8
  ((Certificates.AE6Model.cWords ()).flatMap fun c =>
    let C := evalW 360 G c
    Certificates.AE6Model.kWords.map fun x => comp (comp C (letterW x)) (invA C)).toArray

meta def strongPL : Array (Array Nat) := strongOf 360 gensPL Certificates.AE6Model.plDerive

meta def basePL : Array Nat := #[0, 2, 4, 8]

end CertificateChecks.KernelAE6Core

#ks_rawchain CertificateChecks.KernelAE6Core.PL 360 9 24 CertificateChecks.KernelAE6Core.strongPL
  CertificateChecks.KernelAE6Core.basePL 8 Certificates.AE6Model.plDerive

end
