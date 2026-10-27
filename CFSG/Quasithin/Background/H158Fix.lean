module

public import CFSG.Quasithin.Background.HLUCoc24

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc CFSG.Quasithin.H.ZTrans

theorem fix_ktCols_ok : ∀ m < 2 ^ 11, (∀ i < 6, actM (ktCols i) m = m) → m ∈ uTMasks := by
  decide +kernel

theorem fixV_ktCent :
    fixV (img11 trQ ⊓ centSub UT) = UT := by
  ext v
  constructor
  · intro hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
    refine (toW_mem_UT_iff hm).2 (fix_ktCols_ok m hm ?_)
    intro i hi
    have hg : ktRho i ∈ img11 trQ ⊓ centSub UT := ⟨ktRho_mem_img i, ktRho_mem_cent hi⟩
    have h := (mem_fixV).1 hv (ktRho i) hg
    have h2 := (actsBy_ktRho hi m).symm.trans h
    exact toW_inj (actM_lt (ktCols_lt i hi) m) hm h2
  · intro hv
    refine (mem_fixV).2 ?_
    intro g hg
    exact hg.2 v hv

end CFSG.Quasithin.H.Coc24
