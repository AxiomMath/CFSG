module

public import CFSG.LocalAnalysis.StandardType.GGL45NtCoreGeo
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtStructOn_all :
    (S : ℕ → LargeEvenLabel → Prop) → GGL45NtStructOn S :=
  fun _ p hp hp2 lab hlab _ _ =>
    (largeEvenLabelAll_and (TCJ.ggTCJ_datum_marking hlab)
      (ggRawInnFieldInput_holds p hp hp2 lab hlab)).mono
      fun R _ I _ ⟨⟨hfin, _⟩, hinn⟩ => ⟨hfin, fun hs hna => by
        obtain ⟨hmul, hinv, hconj, -⟩ := hinn hs hna
        exact ⟨{ carrier := I, mul_mem' := fun {a b} ha hb => hmul a ha b hb,
                 one_mem' := by simpa using hconj 1, inv_mem' := fun {a} ha => hinv a ha }, rfl⟩⟩

theorem ggL45NtCoreOn_of_geoOn :
    {S : ℕ → LargeEvenLabel → Prop} → GGL45NtGeoOn S → GGL45NtCoreOn S :=
  fun hgeo p hp hp2 lab hlab hkg hS =>
    (largeEvenLabelAll_and (ggL45NtStructOn_all _ p hp hp2 lab hlab hkg hS)
      (hgeo p hp hp2 lab hlab hkg hS)).mono
      fun R _ I F ⟨⟨hfin, hI⟩, hg⟩ hs hna => by
        haveI := hfin
        exact ggL45NtCore_of_geo hp hp2 (hI hs hna) (hg hs hna)

end CFSG.StandardType
