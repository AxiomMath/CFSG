module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Rec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Orbit
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem asch2_10_holds : Asch2_10 := by
  intro Q _ _ H T K L hK hT hr hL h3 hLT
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨t, htT, hinj⟩ := Asch210.exists_four_conj hT.2.1 L (by omega)
  obtain ⟨B, _, _, M, θ, hθ, hB⟩ :=
    Asch210.exists_pi_quotient hL h3 t (fun i => hT.1 (htT i)) hinj
  have hM : CFSG.pRank 3 ↥M ≤ 3 := by
    have h1 : CFSG.pRank 3 ↥M ≤ CFSG.pRank 3 ↥H := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥M,
        CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥H]
      exact CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) M.subtype
        M.subtype_injective
    exact h1.trans ((CFSG.SectionRank.pRank_coe_eq_openPRank 3 H).trans_le hr)
  have h4 := Asch210.card_le_three_of_pi_quotient hB hM θ hθ
  simp at h4

end CFSG.LocalAnalysis.WeakClosure81
