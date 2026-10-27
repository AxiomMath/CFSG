module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcGeo
public import CFSG.LocalAnalysis.StandardType.GGL45NtCoreStruct
public import CFSG.LocalAnalysis.StandardType.GGL45NtGeoNormGlue
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.C14Exc

theorem ggL45NtCoreOn_ex_of_bridge
    (hU : ExcBridgeStmtU) (hE6 : ExcBridgeStmtE6) (hTwE6 : ExcBridgeStmtTwE6)
    (hTriD4 : ExcBridgeStmtTriD4) (hTwF4 : ExcBridgeStmtTwF4) (hStd : ExcAlgGeoStd)
    (hRee : ExcAlgGeoRee) :
    GGL45NtCoreOn GGL45NtFamEx := by
  have hrec : GGL45NtRecOn GGL45NtFamEx := ggL45NtRecOn_ex
  have hnorm : GGL45NtGeoNormOn GGL45NtFamEx :=
    ((ggL45NtGeoNormOn_exU hU (hrec.antitone fun _ _ h => h.1) hStd).union
      ((ggL45NtGeoNormOn_e6 hE6 (hrec.antitone fun _ _ h => h.1) hStd).union
        ((ggL45NtGeoNormOn_twE6 hTwE6 (hrec.antitone fun _ _ h => h.1) hStd).union
          (ggL45NtGeoNormOn_exTw hTriD4 hTwF4 (hrec.antitone fun _ _ h => h.1)
            (ggL45NtStructOn_all _) hStd hRee)))).antitone ggL45NtFamEx_cover
  exact ggL45NtCoreOn_of_geoOn (ggL45NtGeoOn_of_normOn hnorm)

end CFSG.StandardType
