module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1LnA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Fpz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_v1_hard_ln_three {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsLn ↥L₀ 3 1) (hL : IsLn ↥(lBar ⊥ V hV L) 3 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h.h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => BinaryNaturalSL H U Z 3 1) :=
    s16e_two_fam_ln D hV (le_refl 3) hL hsum'
  have hfpf := s16c11_v1_z_fpf D (h.in10 h125) h.h1217 hc hs hF hK
  obtain ⟨J₀, hM⟩ :=
    s16c11_v1_model_of_fpf (s15_Infra_vtil_sq_eq_one ⊥ V hV) inf_le_left hK hfpf
  obtain ⟨hm3, hD1, hD2⟩ := s1611e3_v1_ln3_dimD h hc hs hsig hK hdir hL₀ hL hsum hV1 hM
  have hTI : S16C11TI D ⊥ V := by
    intro g _
    exact ⟨bot_inf_eq _, by rw [E3.conjSubgroup_bot, inf_bot_eq]⟩
  have hp3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact s1611e3_normalizer_le_of_dimD h hc hTI hm3 hD1 hD2 hp3

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
