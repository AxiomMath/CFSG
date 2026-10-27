module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringNarrow
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksTwo
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22
public import CFSG.Perm.ChainComplete
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1Bridge
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.He
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.ON.ActionBase
public import CFSG.Sporadic.ON.CertificateBase
public import CFSG.Sporadic.ON.ChainBase
public import CFSG.Sporadic.ON.LinesBase
public import CFSG.Sporadic.ON.PrimitiveBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.ONan
public import CFSG.Sporadic.Schreier.M23
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate8153
public import Certificates.Certificate8156
public import Certificates.Certificate8157
public import Certificates.Certificate9210
public import Certificates.Certificate9211
public import Certificates.Certificate9212
public import Certificates.Certificate9214
public import Certificates.Certificate9215
public import Certificates.Certificate9216
public import Certificates.Certificate9217
public import Certificates.Certificate9217Base

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Census44


theorem quasisimpleCensus_of_open_cover (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen'') :
    QuasisimpleCensus :=
  quasisimpleCensus_of_open_narrow h41 hGA hSpor (TwoCoverRanksOpen'.of_open'' hcov)


theorem quasisimpleCensus_of_cover (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) : QuasisimpleCensus :=
  quasisimpleCensus_of_open_cover h41 hGA hSpor twoCoverRanksOpen''

end Census44

section Item44


theorem rank3II_4_4_of_open_cover (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen'')
    (hL34 : FourL34NotSLFourOdd) : Item4_4 :=
  rank3II_4_4_of_open_narrow h41 hGA hSpor (TwoCoverRanksOpen'.of_open'' hcov) hL34


theorem rank3II_4_4_of_cover (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hL34 : FourL34NotSLFourOdd) : Item4_4 :=
  rank3II_4_4_of_open_cover h41 hGA hSpor twoCoverRanksOpen'' hL34

end Item44

end CFSG.RankThree.PartTwo.Sec4.Census
