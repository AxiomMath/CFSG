module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Fpz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt10A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_hard_alt_ten (D : Data G) (hin : In10 D) (h1217 : R1217 D) (h1610 : R16_10_2 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hout : Out10 D ⊥ V hV)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSym ↥L₀ 10) (hA : UC22.IsAlt ↥(lBar ⊥ V hV L) 10)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 10) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 10) :=
    s16e_two_fam_alt D hV (by omega) hA hsum'
  have hfpf := s16c11_v1_z_fpf D hin h1217 hc hs hF hK
  obtain ⟨J₀, hM⟩ :=
    s16c11_v1_model_of_fpf (s15_Infra_vtil_sq_eq_one ⊥ V hV) inf_le_left hK hfpf
  obtain ⟨hr, hD1, P, hPM, hPp, hPc⟩ :=
    s16c11_v1_dimD_alt_ten D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hV1 hM
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hTI : S16C11TI D ⊥ V := by
    intro g _
    exact ⟨bot_inf_eq _, by rw [E3.conjSubgroup_bot, inf_bot_eq]⟩
  have hmB : MBarGT D.M ⊥ V 1 :=
    (h125.mBarGT_iff_lt_mBar 1).2 (lt_of_le_of_lt (TwelveShort.one_le_k D) hout.1)
  have hp3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  exact s16c11_normalizer_le_of_dimD' D hin.h61 hV h125 hTI hmB hr hD1 hp3 hPM hPp hPc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
