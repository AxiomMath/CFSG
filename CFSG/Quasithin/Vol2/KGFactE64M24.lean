
module

public import CFSG.Quasithin.Vol2.KGFactE64M24Base

public import CFSG.Quasithin.Vol2.KGFactE64Lat
public import CFSG.Quasithin.Vol2.KGFactE64M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import Certificates.Certificate7148
import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.KGInsp CFSG.Blueprint

theorem m24_member_ok
    {j : ℕ}
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) :
    ∀ y ∈ m24Ctx.Y j, orderOf y = 7 → ∀ a ∈ pCoreOf 2 (m24Ctx.Y j),
      ∀ b ∈ pCoreOf 2 (m24Ctx.Y j), ¬ Bad y a b :=
  Certificates.certificate7148 j hj

theorem not_heInspCfg_m24 :
    ¬ HeInspCfg (NativeSporadic.Carrier .M24) 3 := by
  intro hcfg
  have hcfg' : HeInspCfg ↥NativeSporadic.M24 3 := hcfg
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m24_simplicity
  have hcard : Nat.card ↥NativeSporadic.M24 = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have hD : BadData ↥NativeSporadic.M24 :=
    badData_of_cfg (X := ↥NativeSporadic.M24) (by rw [hcard]; norm_num) hcfg'
  refine false_of_lattice m24Ctx m24_S_sylow ?_ hD
  intro j hj y hy hord a ha b hb hbad
  have hj13 : j < 13 := by rw [m24_J] at hj; exact hj
  by_cases hj7 : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6
  · exact m24_member_ok hj7 y hy hord a ha b hb hbad
  · have h7 : 7 ∣ Nat.card (m24Ctx.Y j) := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : m24Ctx.Y j)
      rwa [Subgroup.orderOf_mk, hord] at this
    rw [m24_member_card j hj13] at h7
    have key : ∀ j < 13, ¬ (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) →
        ¬ 7 ∣ #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 1024 := by
      decide
    exact key j hj13 hj7 h7

end CFSG.Quasithin.H13.KGE64
