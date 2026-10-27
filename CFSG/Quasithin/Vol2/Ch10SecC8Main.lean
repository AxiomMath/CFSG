module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4a
public import CFSG.Quasithin.Vol2.Ch10SecC8Main4b
public import CFSG.Quasithin.Vol2.Ch10SecC8Main4d

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

theorem stmt10_2_8_of (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) : Stmt10_2_8 := by
  intro G _ _ T L I hyp hL hcv1
  have hle := fsuUL_inf_le_fsuCVM h37 h38 hyp h1011
  have hcv : fsuCVM T L I ≠ ⊥ := fun h => hcv1 (le_bot_iff.mp (h ▸ hle))
  have hne : cV1 T L I ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcv1
    have hxC := (hle hx).2
    intro h
    apply hx1
    have h1 : (⟨x, hx.1⟩ : ↥(fsuUL T L I)) ∈ cV1 T L I := Subgroup.mem_subgroupOf.mpr hxC
    rw [h, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have h3 := case3_of hyp h1012 hL hcv
  refine ⟨commutator_Z_L_eq_bot h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne,
    omegaOne_Q_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne,
    omegaOne_T1_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne,
    ⟨eq_commutator_thompsonJ hyp h1011 h1012 h3 h3210 hcv, commutator_Z_ne_bot hyp h1026 hcv⟩,
    fun t ht htn U₁ U₂ R₁ R₂ hU₁ hU₂ hR₁ hR₂ v₂ hv₂ hv₂C => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact nonempty_stabilizer_equiv h37 h38 hyp h1011 h484 h3 hne ht htn hU₂ v₂ hv₂ hv₂C
  · exact R_sup_eq_thompsonJ_sup h37 h38 hyp h1011 h1012 h484 h3210 h3 hne ht htn hU₁ hU₂ hR₁
      hR₂
  · exact centralizer_v2_eq h37 h38 hyp h1011 h484 h3 hne ht htn hU₂ hR₂ hv₂ hv₂C
  · exact omegaOne_centralizer_v2_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne ht htn hU₂
      hv₂ hv₂C

end CFSG.Quasithin.Vol2.Ch10.SecC
