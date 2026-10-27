module

public import CFSG.RankThree.GF2n.Tim77.Sec414U
public import CFSG.RankThree.GF2n.Tim77.Sec414V

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

theorem sec414t_of
    (h47 : Tim77Sec47Statement) (h412 : Tim77Sec412Statement) : Tim77Sec414Statement := by
  intro G _ _ A Abar S₀ B h hq hA0
  have S : Sec414Sys A (Section3.A0 A Abar) := Sec414Sys.of_ctx tim77Sec49_holds h412 h hq hA0
  by_contra hnot
  have hbad : ∃ g : G, ¬ ∀ x ∈ Section3.A0 A Abar, Sec414InO2 (A ⊔ conjSubgroup g A) x := by
    by_contra hno
    push Not at hno
    exact hnot (sec414_a0_le_pCore S.elem.isPGroup S.a0_le hno)
  obtain ⟨g, hbad', hmem, hmin⟩ := sec414_exists_min_bad S.elem.isPGroup S.a0_le hbad
  have M : Sec414Min A (Section3.A0 A Abar) g := ⟨hbad', hmem, hmin⟩
  obtain ⟨K, _, π, hK, hπ, hAinj, hker⟩ := sec414_bender_of_min S M
  obtain ⟨a₀, ha₀, z, k, hk, hz2, hzc, hC, hC0, hAC⟩ :=
    sec414t_central S M.mem hK π hπ hAinj hker (fun t ht htW => M.inf_W S ht htW)
  exact sec414t_contra S (fun P hP hPA => sec414_exists_partner h47 h hq S hP hPA) hK π hπ
    hAinj ha₀ hk hz2 hzc hC hC0 hAC

end CFSG.RankThree.GF2n.Tim77
