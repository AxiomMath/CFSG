module

public import CFSG.Milestones.ASVolI.C48.Cases
public import CFSG.Milestones.ASVolI.C27
public import CFSG.Milestones.ASVolI.C31.Asm
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverFin
public import CFSG.Quasithin.Background.F918F3
public import CFSG.Quasithin.Background.C48PfD
public import CFSG.Quasithin.Background.C48PfFourModPf

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section C48Main

set_option linter.unusedSectionVars false


theorem burnsideC48_C_4_8_of_insp
    (h31 : C_3_1) (h41 : C_4_1)
    (hInsp : CFSG.Quasithin.InspC31Sporadic) : C_4_8 := by
  intro G _ _ H R M L V h hMH
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  by_cases hF : oTwoFstarIn H ≤ M
  ·
    rcases as_C_2_13 G H R M L V h hF with hHM | ⟨hM0, hLc, hMeq, hidx⟩
    · exact absurd hHM.symm hMH.ne
    · have hn : ¬ H ≤ Subgroup.normalizer (L : Set G) := by
        intro hHN
        apply hMH.ne
        rw [hMeq, hM0]
        exact inf_eq_left.mpr hHN
      obtain ⟨hq, htypes⟩ := C48.a38_of_not_le_normalizer
        CFSG.Quasithin.H13.VolI.a36ForSQTK_holds hA38 h.sqtk hLc hn
      refine ⟨hM0.symm, L, hLc, hq, le_rfl, Or.inl ⟨hF, ?_, hMeq, hidx⟩⟩
      rcases htypes with ⟨n, h1⟩ | ⟨n, h1⟩ | h1 | ⟨p, hp, hp3, h1⟩
      · exact Or.inl ⟨n, h1⟩
      · exact Or.inr (Or.inl ⟨n, h1⟩)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr ⟨p, hp, by omega, h1⟩))
  obtain ⟨K, hK, hq, hKM⟩ := C48.exists_cComp_not_le h (as_C_2_11 G H R M L V h) hF
  rcases C48.isComponentOf_or_charTwo (as_C_2_10 G H R M L V h).1 hK hq with hcomp | hchar
  ·
    have h31' : C31Conclusion H R M L V K := h31 G H R M L V K h hcomp
    obtain ⟨hL0, -, hM0K, hMK, -, hcases⟩ := id h31'
    have hno : ¬ IsC134Case 2 (K ⊔ R) R K :=
      burnsideC48_not_isC134Case_two hcomp (h.le_M.trans hMK)
    have hSpor : C48SporStep G := C48Spor.c48SporStep_of (C22Pf.asc22One_of hA37) hInsp
      C48Cover.c48SporCoverFact_holds
    have hspor := fun hc => burnsideC48_or9_of_spor hno (hSpor H R M L V K h hcomp h31' hc).1
    refine ⟨hL0, K, hK, hq, hL0.le.trans hM0K, Or.inr ⟨?_, hKM, hMK, Or.inl ⟨hcomp, h31'⟩⟩⟩
    rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
    · exact Or.inl (burnsideC48_c48Case1_of_c31Case1 h hL0 c1)
    · exact Or.inr (Or.inl (C48.c48Case2_of_c31Case2 h hL0 c2).1)
    · exact hspor (Or.inl c3)
    · exact hspor (Or.inr (Or.inl c4))
    · exact hspor (Or.inr (Or.inr (Or.inl c5)))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inl c6))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7)))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c8))))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c9))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (C48.c48Case9_of_c31Case10 h hL0 c10))))))))
  ·
    have h41' : ChC.C41Concl H R M L V K := h41 G H R M L V K ⟨h, hK, hchar, hq, hKM⟩
    obtain ⟨hL0, hM0K0, hK0, hcases⟩ := id h41'
    have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
      have := le_normalizer_conjClosure K H
      rwa [hK0] at this
    have hLK : L ≤ K := by
      have h0 := hM0K0
      rw [hK0, ← hL0] at h0
      exact h0
    refine ⟨hL0, K, hK, hq, hLK, Or.inr ⟨?_, hKM, h.le_H.trans hHK,
      Or.inr ⟨hK, hchar, hq, hKM, h41'⟩⟩⟩
    rcases hcases with c1 | c2 | c3 | c4
    · rcases burnsideC48_of_c41Case1 h hL0 c1 with h1 | h8
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
    · exact Or.inl (burnsideC48_c48Case1_of_c41Case2 h hL0 hLK c2)
    · exact Or.inl (burnsideC48_c48Case1_of_c41Case3 h hL0 hLK c3)
    · have hwip : C41Conclusion H R M L V K := ⟨hL0, hM0K0, hK0, Or.inr (Or.inr (Or.inr c4))⟩
      have hFour : C48C41FourStep G := C48Pf.c48C41FourStep_of (C22Pf.asc22Three_of hA37)
        (as_C_2_7 G) B5.asB51_holds asI16Cover_of asI16CoverA8_of C48Pf.fourModFact_holds
      exact Or.inr (Or.inl (hFour H R M L V K h hK hchar hq hKM hwip c4).1)

theorem burnsideC48_C_4_8_of
    (h31 : C_3_1) (h41 : C_4_1)
    (hJ4 : CFSG.Quasithin.InspC31SporadicAtJ .J4) : C_4_8 :=
  burnsideC48_C_4_8_of_insp h31 h41 (burnsideC31_inspC31Sporadic_of_J4 hJ4)

theorem burnsideC48_C_4_8_of_KW
    (h31 : C_3_1) (h41 : C_4_1)
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : C_4_8 :=
  burnsideC48_C_4_8_of h31 h41 (burnsideC31_inspC31Sporadic_of_KW hKW .J4 (by simp))

end C48Main

end CFSG.ASVolI
