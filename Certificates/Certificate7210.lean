
module

public import CFSG.Quasithin.Vol2.KGFactC31M23Data
import Certificates.Kernel.KGC31M23.Facts
import Certificates.Kernel.KGC31M23.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.KGC31M23.CosDefs
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Sporadic.Schreier.ClassSum

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M23 in
theorem certificate7210 : ordTest 23 5 x5T = true ∧ ordTest 23 7 x7T = true ∧ ordTest 23 11 x11T = true ∧
    ordTest 23 23 x23T = true ∧
    orbCheck 23 5 CFSG.Quasithin.KGC31.M23.invs (powTabs 23 x5T 5) cands5 = true ∧
    orbCheck 23 7 CFSG.Quasithin.KGC31.M23.invs (powTabs 23 x7T 7) cands7 = true ∧
    actCheck 23 11 CFSG.Quasithin.KGC31.M23.invs (powTabs 23 x11T 11) = true ∧
    actCheck 23 23 CFSG.Quasithin.KGC31.M23.invs (powTabs 23 x23T 23) = true ∧
    ((List.range 8).all fun k => CFSG.Sporadic.Th.Native.invOK 23 (candT k) (CFSG.Sporadic.Th.Native.invT 23 (candT k))) = true ∧
    ebasisOK 23 CFSG.Quasithin.KGC31.M23.wT = true ∧ ebasisOK 23 tT = true ∧ ebasisOK 23 CFSG.Quasithin.KGC31.M23.eT = true ∧
    ebasisOK 23 sT = true ∧
    cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 23 CFSG.Quasithin.KGC31.M23.wT) = 16 ∧ cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 23 tT) = 16 ∧
    cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 23 CFSG.Quasithin.KGC31.M23.eT) = 8 ∧ cbT.countP (CFSG.Sporadic.Schreier.Native.commAll 23 sT) = 16 ∧
    cosetOK 23 b0T CFSG.Quasithin.KGC31.M23.wT wCosetT = true ∧ cosetOK 23 b0T tT tCosetT = true ∧
    cosetOK 23 b0T CFSG.Quasithin.KGC31.M23.eT eCosetT = true ∧
    cosetCount 23 cbT wCosetT (normAll 23 CFSG.Quasithin.KGC31.M23.wT) = 40320 ∧
    cosetCount 23 cbT tCosetT (fun g => normAll 23 tT g && fixesAll g triT) = 960 ∧
    cosetCount 23 cbT eCosetT (normAll 23 CFSG.Quasithin.KGC31.M23.eT) = 1344 ∧
    wChain.check = true ∧ wChain.orderCertificate = 40320 ∧
    tChain.check = true ∧ tChain.orderCertificate = 960 ∧
    eChain.check = true ∧ eChain.orderCertificate = 1344 ∧
    (wGen.zip wMasks).all (fun p => masksOK 23 CFSG.Quasithin.KGC31.M23.wT (toTable p.1) p.2) = true ∧
    (tGen.zip CFSG.Quasithin.KGC31.M23.tMasks).all (fun p => masksOK 23 tT (toTable p.1) p.2) = true ∧
    (eGen.zip CFSG.Quasithin.KGC31.M23.eMasks).all (fun p => masksOK 23 CFSG.Quasithin.KGC31.M23.eT (toTable p.1) p.2) = true ∧
    (tGen.all fun g => fixesAll (toTable g) triT) = true ∧
    fixSetIs 23 CFSG.Quasithin.KGC31.M23.wT hexH = true ∧ fixSetIs 23 tT triT = true ∧
    countProducts 23 (fun g => fixesAll g hexH) (levelTables wChain) (idT 23) = 16 ∧
    (sT.length == sInW.length && (sT.zip sInW).all fun p => tblEq 23 p.1 (maskProd 23 CFSG.Quasithin.KGC31.M23.wT p.2)) =
      true := KernelKGC31M23.cert7210

end Certificates
