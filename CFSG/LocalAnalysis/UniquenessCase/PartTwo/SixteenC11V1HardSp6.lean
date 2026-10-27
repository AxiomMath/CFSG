module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSp6A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Fpz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1RouteF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_hard_sp_six (h : H1SpSixNatural) (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h1610 : R16_10_2 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSpn ↥L₀ 6 1) (hSp : IsSpn ↥(lBar ⊥ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => NatSpn H U Z 6 1) :=
    s16e_two_fam_sp D hV hSp hsum'
  have hfpf := s16c11_v1_z_fpf D hin h1217 hc hs hF hK
  obtain ⟨J₀, hM⟩ :=
    s16c11_v1_model_of_fpf (s15_Infra_vtil_sq_eq_one ⊥ V hV) inf_le_left hK hfpf
  exact s16c11_v1_normalizer_le_of_model_rf3 D hin.h61 h1610 hin.h169 hc hsig hM hK hdir
    (s16c11_v1_rf3_sp_six h D hin h1217 hc hs hsig hK hdir hL₀ hSp hsum hV1 hM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
