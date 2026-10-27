module

public import CFSG.Quasithin.H13.A6S13827Gl
public import CFSG.Quasithin.H13.A6S13827Ge
public import CFSG.Quasithin.H13.A6S13827Gk

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative

theorem lem13827G2_of
    (h21 : Lem13821) (h16 : Lem13816) (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) : Lem13827G2 := by
  intro G _ _ T L V S hS K hK hU
  have hH : S.G1 ∈ S.Hz := hS.hG1
  have hd := S.dk_of_psu33 h16 h21 hS hH hK hU
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 S.G1) := hF.F911_3.1
  obtain ⟨W, hV1W, hWU, hHW, hmax⟩ := hd.exists_max
  have htriv := hd.triv_of_max_u33 h21 h16 hU hV1W hWU hHW hmax
  have h64 := hd.relIndex_top_u33 hU hV1W hWU hHW hmax
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  have hi : (fsuV1 T V).relIndex W ∣ 2 := by
    rcases hd.cover_u33 h21 h16 hU with hfix | ⟨-, h7, -⟩
    ·
      have hWV : W ≤ fsuV1 T V := by
        intro w hw
        have h1 := hsV.secMk_mem_fixV (x := ⟨w, hWU.le hw⟩) hd.hKH fun k hk => htriv k hk w hw
        rw [hfix, Subgroup.mem_bot, A6Mod.secMk_eq_one_iff] at h1
        exact h1
      rw [Subgroup.relIndex_eq_one.2 hWV]
      exact one_dvd 2
    · rw [Setting4.SecHyp.card_sec] at h7
      have h2 := Subgroup.relIndex_mul_relIndex (fsuV1 T V) W (conjClosure S.V3 S.G1) hV1W hWU.le
      rw [h64, h7] at h2
      have : (fsuV1 T V).relIndex W = 2 := by omega
      rw [this]
  have hi2 : (fsuV1 T V).relIndex W ≤ 2 := Nat.le_of_dvd (by norm_num) hi
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle, -⟩ := S.case2_of_no_transv hF (hd.no_transv_u33 hU)
  have hHK : S.G1 = K ⊔ (S.L1 ⊔ T) := by
    rw [← sup_assoc, sup_eq_left.2 hd.hL1K]
    exact hd.hHK
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS S.G1 hH K hK hd.hKn hHK γ γ' g s
    (conjClosure S.V3 S.G1) le_rfl hDH.not_ge
  have h4 := hd.card_Uγ_le_four_u33 h13315 h1356two h13314 hU s hgen
  have hAU := hd.A₁_le_UH_u33 hU hV1W hWU hHW hmax s hDγ hle h4
  obtain ⟨h4', h8⟩ := hd.e4_u33 hU le_rfl hV1W hWU hHW hi h64 s hDγ hAU h4
  have hn2 := hd.eight_le_card_UH_inf_Dγ h13315 h1356two hV1W hWU hHW s h8
  have hn3 := hd.eight_le_relIndex_VH_u33 h13315 h1356two h13314 hU hV1W hWU hHW h64 s hDγ h8
  have hn4 := hd.not_Dγ_le_VH_u33 h13315 h1356two h13314 le_rfl hV1W hWU hHW hmax htriv s hAU
    h8
  set D := F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) with hD
  have hDU : D ≤ F8.Uγ S.V3 S.G1 (g : G) := centralizerMod_le_left _ _ _
  have hDeq : D = F8.Uγ S.V3 S.G1 (g : G) ⊓ pCoreOf 2 S.G1 := hF.Dγ_eq_inf_pCoreOf s
  have hc1 : D.relIndex (F8.Uγ S.V3 S.G1 (g : G)) * Nat.card D =
      Nat.card (F8.Uγ S.V3 S.G1 (g : G)) := by
    have := Subgroup.relIndex_mul_card D (F8.Uγ S.V3 S.G1 (g : G))
    rwa [inf_eq_left.2 hDU] at this
  have h4D : D.relIndex (F8.Uγ S.V3 S.G1 (g : G)) = 4 := by rw [hDeq]; exact h4'
  have hc2 := Subgroup.relIndex_mul_card (conjClosure V S.G1) D
  have hc3 := Subgroup.relIndex_mul_card (conjClosure S.V3 S.G1) (conjClosure V S.G1 ⊓ D)
  have hUV : conjClosure S.V3 S.G1 ≤ conjClosure V S.G1 := conjClosure_mono S.V3_le_V le_rfl
  rw [← inf_assoc, inf_eq_left.2 hUV] at hc3
  have hVD : 2 ≤ (conjClosure V S.G1).relIndex D := by
    have h1 : (conjClosure V S.G1).relIndex D ≠ 1 := fun h => hn4 (Subgroup.relIndex_eq_one.1 h)
    have h0 : (conjClosure V S.G1).relIndex D ≠ 0 := relIndex_ne_zero' _ _
    omega
  have hUγ : Nat.card (F8.Uγ S.V3 S.G1 (g : G)) = Nat.card (conjClosure S.V3 S.G1) :=
    card_conjSub _ _
  have hcU := Subgroup.relIndex_mul_card (fsuV1 T V) (conjClosure S.V3 S.G1)
  rw [inf_eq_left.2 (hV1W.trans hWU.le), hF1.card_V₁,
    ← Subgroup.relIndex_mul_relIndex (fsuV1 T V) W (conjClosure S.V3 S.G1) hV1W hWU.le,
    h64] at hcU
  have e1 : 64 ≤ Nat.card ↥(conjClosure V S.G1 ⊓ D) := by
    rw [← hc3]
    exact (Nat.mul_le_mul hn3 hn2 : 8 * 8 ≤ _)
  have e2 : 128 ≤ Nat.card D := by
    rw [← hc2]
    exact (Nat.mul_le_mul hVD e1 : 2 * 64 ≤ _)
  rw [h4D] at hc1
  omega

end CFSG.Quasithin.H13.A6
