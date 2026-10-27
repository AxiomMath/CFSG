module

public import CFSG.Sporadic.SuzI301.Row
public import CFSG.Sporadic.SuzI301Cover.Split
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverPerfect

public section

namespace CFSG.Sporadic.SuzI301Cover

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Monster.B.Co2 CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzI301


theorem suzh_hI (hd : dP ∈ suzM) (E : Type) [Group E] [Finite E] (π : E →* ↥suzM)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center E) (hk3 : Nat.card π.ker = 3)
    (hE : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤) (dh : E) (hdh : π dh = ⟨dP, hd⟩) :
    RowI .suzh 3 (rowIOf 3 dh) := by
  obtain ⟨hq, hz, ⟨eT⟩, hcard⟩ := centD_facts ⟨dP, hd⟩ rfl
  have hidx : ¬ 3 ∣ (Subgroup.centralizer ({(⟨dP, hd⟩ : ↥suzM)} : Set ↥suzM)).index := by
    have h := (Subgroup.centralizer ({(⟨dP, hd⟩ : ↥suzM)} : Set ↥suzM)).card_mul_index
    rw [hcard, suzM_card_chain] at h
    have h45 : (Subgroup.centralizer ({(⟨dP, hd⟩ : ↥suzM)} : Set ↥suzM)).index = 45760 := by
      omega
    rw [h45]
    norm_num
  exact isTypeWithCenter_layer_cover_of_quasisimple π hπ hker hk3 hE hq hz hidx
    (catalogIs_isU4of_three eT) hdh

theorem i301ARowCover_suzh :
    I301ARowCover .suzh := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have hd : dP ∈ suzM := bP_zero ▸ bP_mem' (by norm_num)
  exact @i301ARowCover_of_model .suz .suzh rfl rfl rfl rfl rfl (fun _ _ _ => rfl) ↥suzM
    inferInstance inferInstance ⟨suzEquivM.symm.trans b⟩ _ _ _ (i301ARowCfg_suz ⟨dP, hd⟩ rfl)
    (row_K _ rfl) (row_solvN _ rfl) (row_solvZ _ rfl) (suzh_split hd) (suzh_hI hd)

end CFSG.Sporadic.SuzI301Cover
