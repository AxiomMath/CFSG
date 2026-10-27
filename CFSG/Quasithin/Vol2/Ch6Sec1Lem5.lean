module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5C
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Res

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

theorem Cx615.cx615B (c : Cx615 G T M L V H n) (h331 : Stmt3_3_1) (h512 : Stmt5_1_2)
    (h5172 : Stmt5_1_7_two) (he23 : E2.E23Statement) (hRes : Res615Blocks)
    (hV : V = reducedAggregate (L ⊔ T)) : Cx615B G T M L V H n where
  toCx615 := c
  V_eq := hV
  JL := (h5172 G T M L V H n c.hyp.toHyp5_0_1 c.hyp.module c.hH c.commutator_ne).1.symm
  JK := (h5172 G T M L V H n c.hyp.toHyp5_0_1 c.hyp.module c.hH c.commutator_ne).2.1.symm
  nat := c.nat h512 h5172
  ZL := by
    obtain ⟨z, hz, hzL⟩ := c.exists_z h512 h5172
    exact fun hle => hzL (hle hz)
  CZd := c.CZd h512 h5172
  CMZ := c.CMZ h512 h5172
  hU := c.UH_red.1
  e23 := c.e23 h331 h5172 he23
  s3 := fun I hcard hJ htype => hRes G T M L V H n c.hyp c.hH c.notZ c.UH_red.1 I hcard hJ htype

theorem Cx615B.cx615C (c : Cx615B G T M L V H n) (h512 : Stmt5_1_2) (h5172 : Stmt5_1_7_two)
    (hCent : Res615Cent) : Cx615C G T M L V H n := by
  have hsyl := c.toCx615.isSylowTwoOf
  obtain ⟨hUO, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl c.toCx615.charTwo le_rfl
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (Cx615.UH T H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hcent : H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) = pCoreOf 2 H :=
    le_antisymm (hCent G T M L V H n c) (le_inf (pCoreOf_le 2 H) hO2U)
  refine
    { toCx615B := c
      cent := hcent
      HJT := ?_
      X_O2 := c.toCx615.X_O2 h5172
      faithful := c.toCx615.faithful h512 h5172
      QX := c.toCx615.QX h512 h5172 hcent }
  have hTH : T ≤ H := c.hH.1.1
  apply le_antisymm
  · have hK : oTwoUpper H ≤ thompsonJ H := by
      rw [← twoResidual_eq_oTwoUpper']
      exact c.e23.1
    calc H = oTwoUpper H ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
      _ ≤ thompsonJ H ⊔ T := sup_le_sup_right hK T
  · exact sup_le (thompsonJ_le_self H) hTH

theorem stmt6_1_5_of (h331 : Stmt3_3_1) (h512 : Stmt5_1_2) (h5172 : Stmt5_1_7_two)
    (h614 : Stmt6_1_4) (he23 : E2.E23Statement) (hRes : Res615Blocks) (hCent : Res615Cent)
    (hD : Res615D) (hE : Res615E) : Stmt6_1_5 := by
  intro G _ _ T M L V n h H hH
  by_contra hZ
  have cC := ((h.cx615 h614 hH hZ).cx615B h331 h512 h5172 he23 hRes rfl).cx615C h512 h5172 hCent
  by_cases hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)
  · exact hD G T M L _ H n cC hN
  · exact hE G T M L _ H n cC hN

end CFSG.Quasithin.H13
