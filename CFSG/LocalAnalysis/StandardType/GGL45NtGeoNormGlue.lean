module

public import CFSG.LocalAnalysis.StandardType.GGL45NtGeoNorm
public import CFSG.LocalAnalysis.StandardType.GGL45NtCoreStruct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtGeoOn_of_normOn :
    {S : ℕ → LargeEvenLabel → Prop} → GGL45NtGeoNormOn S → GGL45NtGeoOn S :=
  fun hn p hp hp2 lab hlab hkg hS =>
    (largeEvenLabelAll_and (ggL45NtStructOn_all _ p hp hp2 lab hlab hkg hS)
      (hn p hp hp2 lab hlab hkg hS)).mono
      fun R _ I F ⟨⟨hfin, hI⟩, hg⟩ hs hna => by
        haveI := hfin
        exact ggL45NtGeo_of_normalized hp (hI hs hna) (hg hs hna)

end CFSG.StandardType
