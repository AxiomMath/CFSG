module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42

meta def lcV : List Nat := lineCert.pts.toList.map (CFSG.KS.RawGen.pack 3)

meta def lcE : List Nat := lineCert.edges.toList.map (CFSG.KS.RawGen.pack 12)

meta def lcP : List Nat :=
  (List.range 18).map fun k => CFSG.KS.RawGen.pack 12 (lineCert.edges.map fun r => r[k]!)

meta def lcG : List Nat := genCodes.toList.map (CFSG.KS.RawGen.pack 3)

meta def lcC : List Nat :=
  (List.range 22).map fun s => Id.run do
    let mut c := 1
    for i in [0:117 * s] do
      for j in lineCert.edges[i]! do
        if j + 1 > c then c := j + 1
    return c

meta def lcS : List Nat :=
  ((List.range 2457).toArray.qsort fun a b =>
    keyV lineCert.pts[a]! < keyV lineCert.pts[b]!).toList

end CertificateChecks.KernelD4

end

#kc_items CertificateChecks.KernelD4.LV include_bytes "data/LinkData.LV.items" 17131 18001942688503432572
#kc_items CertificateChecks.KernelD4.LE include_bytes "data/LinkData.LE.items" 76148 6008530357686555467
#kc_items CertificateChecks.KernelD4.LP include_bytes "data/LinkData.LP.items" 66420 18076215949991807513
#kc_items CertificateChecks.KernelD4.LG include_bytes "data/LinkData.LG.items" 504 10738936890626253098
#kc_items CertificateChecks.KernelD4.LC include_bytes "data/LinkData.LC.items" 131 10217418340253776120
#kc_items CertificateChecks.KernelD4.LS include_bytes "data/LinkData.LS.items" 14485 14673477036448209439
