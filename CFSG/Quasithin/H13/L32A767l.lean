module

public import CFSG.Quasithin.H13.L32A767k
public import CFSG.Quasithin.H13.U3X10L
public import CFSG.Quasithin.H13.L32A770n

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem normalizer_baum_R1_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (hC137 : U3.C137Statement) :
    Subgroup.normalizer (baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have h13322 := stmt13_3_2_two_of h1332
  rcases U3.stmt13_3_10_L32 h1332 h1222 h1334 hC137 h.hyp.h13 (h.hyp1223 h13322).irrPlus
      (Hyp147.inf_centralizer_eq_bot h h13322 hMod) h.hyp.linear with
    ⟨C, hCB, hC1, hCchar, hLTC⟩ | hblk
  · refine (normalizer_le_normalizer_of_characteristic hCB hCchar).trans ?_
    exact normalizer_le_normalizer_L h h13322 hC1
      ((pCoreOf_isPGroup 2 _).to_le (hCB.trans inf_le_left)) hLTC
  · exact absurd hblk (not_isLnBlock h hMod h63 h1222 h1332 h1334 hF)

end CFSG.Quasithin.H13.L32A
