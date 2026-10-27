
module

public import CFSG.Quasithin.Vol2.KGFactC31M22Data
public import CFSG.Sporadic.Schreier.ImagePairs
import Certificates.Kernel.KGC31M22.Facts
import Certificates.Kernel.KGC31M22.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import CFSG.Sporadic.Schreier.M22Data

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M22 in
theorem certificate7203 : ordTest 22 5 x5T = true ∧ ordTest 22 7 x7T = true ∧ ordTest 22 11 x11T = true ∧
    orbCheck 22 5 (orderTables m22Certificate 2) (powTabs 22 x5T 5) cands5 = true ∧
    orbCheck 22 7 (orderTables m22Certificate 2) (powTabs 22 x7T 7) cands7 = true ∧
    actCheck 22 11 (orderTables m22Certificate 2) (powTabs 22 x11T 11) = true ∧
    CFSG.Sporadic.Th.Native.invOK 22 hexConjT (CFSG.Sporadic.Th.Native.invT 22 hexConjT) = true ∧
    ebasisOK 22 CFSG.Quasithin.KGC31.M22.hexT = true ∧ ebasisOK 22 duadT = true ∧ ebasisOK 22 e8T = true ∧
    countProducts 22 (CFSG.Sporadic.Schreier.Native.commAll 22 CFSG.Quasithin.KGC31.M22.hexT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 CFSG.Quasithin.KGC31.M22.hexT) (levelTables m22Certificate) (idT 22) = 5760 ∧
    countProducts 22 (CFSG.Sporadic.Schreier.Native.commAll 22 duadT) (levelTables m22Certificate) (idT 22) = 16 ∧
    countProducts 22 (normAll 22 duadT) (levelTables m22Certificate) (idT 22) = 1920 ∧
    countProducts 22 (CFSG.Sporadic.Schreier.Native.commAll 22 e8T) (levelTables m22Certificate) (idT 22) = 8 ∧
    countProducts 22 (normAll 22 e8T) (levelTables m22Certificate) (idT 22) = 1344 ∧
    hexChain.check = true ∧ hexChain.orderCertificate = 5760 ∧
    duadChain.check = true ∧ duadChain.orderCertificate = 960 ∧
    (duadT.all fun b => countProducts 22 (tblEq 22 b) (levelTables duadChain) (idT 22) == 1) =
      true ∧
    (hexGen.zip hexMasks).all (fun p => masksOK 22 CFSG.Quasithin.KGC31.M22.hexT (toTable p.1) p.2) = true ∧
    (duadGen.zip CFSG.Quasithin.KGC31.M22.duadMasks).all (fun p => masksOK 22 duadT (toTable p.1) p.2) = true := KernelKGC31M22.cert7203

end Certificates
