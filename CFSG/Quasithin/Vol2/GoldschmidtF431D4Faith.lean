module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin


theorem exists_smul_pt0_eq (i : Fin 819) : ∃ g : D, g • pt0 = i := by
  refine ⟨Classical.choose (exists_conj_cz i.1 (lt_size_cz i.2)), ?_⟩
  apply zElt_injective
  rw [smul_pt_def, zElt_act, zElt_zero]
  rfl

theorem act_ne_one : ∃ g : D, act g ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := exists_smul_pt0_eq ⟨1, by norm_num⟩
  rw [smul_pt_def, h g] at hg
  exact absurd (congrArg Fin.val hg) (by simp [pt0])

theorem act_injective (hs : IsSimpleGroup D) : Function.Injective act := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hs.eq_bot_or_eq_top_of_normal (MonoidHom.ker act) with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := act_ne_one
    apply hg
    have : g ∈ MonoidHom.ker act := by rw [h]; trivial
    exact this

end CFSG.Quasithin.D4Hex
