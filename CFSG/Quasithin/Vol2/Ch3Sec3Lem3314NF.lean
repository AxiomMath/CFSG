module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314B
public import CFSG.Quasithin.Vol2.Ch3Sec3NFSite

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem stmt3_3_14_of_b_on
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h10 : Stmt3_3_10)
    (h13 : Stmt3_3_13LTOn Site3314) (h8one : Stmt3_3_8One) (hI : Insp3_3_14B) : Stmt3_3_14 := by
  intro G _ _ T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hT
    have hP := (h10 G T M L D h).2.2 hT
    obtain ⟨hc, hcase⟩ := h8one G T M L D h hT
    obtain ⟨H₁, H₂, hH₁, hH₂, he₁, he₂, hsup⟩ := hI G T M L h.toSetup331 hT hc hcase hP
    have hS : Site3314 G T M L D H₁ := ⟨hT, hc, hcase, hP⟩
    have hS' : Site3314 G T M L D H₂ := ⟨hT, hc, hcase, hP⟩
    have hD₁ := h13 G T M L D H₁ h hS hH₁ (le_sup_left.trans hsup.le) he₁
    have hD₂ := h13 G T M L D H₂ h hS' hH₂ (le_sup_right.trans hsup.le) he₂
    have hne : L ⊔ T ≠ ⊥ := fun hb => h.toSetup331.T_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
    apply h.not_le_normalizer h38 h39 hne le_rfl Subgroup.le_normalizer
    rw [← hsup]
    exact fun d hd => mem_normalizer_sup (hD₁ hd) (hD₂ hd)
  have hMp := Hyp331.mPlus_eq_of_le hTL
  refine ⟨hMp, ?_⟩
  rw [h.toSetup331.eq_normalizer h38 h39, hMp]

end CFSG.Quasithin.H13
