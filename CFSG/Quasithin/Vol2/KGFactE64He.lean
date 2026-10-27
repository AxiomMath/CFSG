module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.KGFactE64Lat
public import CFSG.Quasithin.Vol2.KGFactE64HeData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import Certificates.Certificate7149
import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.KGInsp CFSG.Blueprint

theorem he_member7_ok :
    ∀ y ∈ heCtx.Y 7, orderOf y = 7 → ∀ a ∈ pCoreOf 2 (heCtx.Y 7),
      ∀ b ∈ pCoreOf 2 (heCtx.Y 7), ¬ Bad y a b := by
  have h7 : 7 < heCtx.J := by rw [he_J]; norm_num
  have hsize : heCtx.D.Om[7]!.lbl.size = 21 := he_Om_size 7 (by norm_num)
  have hcard : Nat.card (heCtx.Y 7) = 21504 := by
    rw [he_member_card 7 (by norm_num)]
    rfl
  have ho2 : Nat.card (pCoreOf 2 (heCtx.Y 7)) = 128 := by
    have h := (heCtx.memStmt_default he_o2OK h7).2.1
    rw [h]
    show 2 ^ 10 / heOtK[7]!.lbl.size = 128
    rw [he_Ot_size 7 (by norm_num)]
    rfl
  have hgens : genTabs 8330 (heCtx.sg ++ heCtx.gens 7) =
      heSTabsC ++ (heMwLit[7]!).map (wordTabA #[heTaC, heTbC] 8330) := by
    rw [heCtx.Y_letters h7]
    obtain ⟨-, hmt, -⟩ := heCtx.membersOK.2.2.2.2 7 h7
    rw [hmt]
    show heCtx.D.sTabs ++ (heCtx.D.mw[7]!).map (wordTabA #[heTa, heTb] 8330) = _
    rw [he_mw_lit]
    rfl
  have hLt : heE64Lt = (genTabs 8330 (heCtx.sg ++ heCtx.gens 7)).toArray := by
    rw [hgens]
    rfl
  have hodd : heCtx.D.Om[7]!.lbl.size % 2 = 1 := by
    rw [hsize]
  refine member_ok_of_check heCtx h7 hodd (by rw [hcard]; norm_num) he_base_lt
    he_base_property heLabels7 (fun x hx => he_labels7 x hx) heE64Lt
    (by rw [hLt, genTabs_size]) (by rw [hLt]; exact genTabs_hel _) heE64Y heE64O
    (by rw [ho2]; rfl) Certificates.certificate7149

theorem not_heInspCfg_he :
    ¬ HeInspCfg (NativeSporadic.Carrier .He) 3 := by
  intro hcfg
  have hcfg' : HeInspCfg NativeSporadic.He 3 := hcfg
  have : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  have hcard : Nat.card NativeSporadic.He = 4030387200 := CFSG.Sporadic.He.card_He
  have : Finite NativeSporadic.He := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hD0 : BadData NativeSporadic.He :=
    badData_of_cfg (X := NativeSporadic.He) (by rw [hcard]; norm_num) hcfg'
  have hD : BadData ↥CFSG.Sporadic.He.J :=
    BadData.map (X := NativeSporadic.He) (Γ := ↥CFSG.Sporadic.He.J) CFSG.Sporadic.He.heEquivJ hD0
  refine false_of_lattice heCtx he_S_sylow ?_ hD
  intro j hj y hy hord a ha b hb hbad
  have hj11 : j < 11 := by rw [he_J] at hj; exact hj
  by_cases hj7 : j = 7
  · subst hj7
    exact he_member7_ok y hy hord a ha b hb hbad
  · have h7 : 7 ∣ Nat.card (heCtx.Y j) := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : heCtx.Y j)
      rwa [Subgroup.orderOf_mk, hord] at this
    rw [he_member_card j hj11] at h7
    have key : ∀ j < 11, j ≠ 7 → ¬ 7 ∣ #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024 := by
      decide
    exact key j hj11 hj7 h7

end CFSG.Quasithin.H13.KGE64
