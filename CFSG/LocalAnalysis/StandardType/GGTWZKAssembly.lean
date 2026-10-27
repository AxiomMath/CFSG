module

public import CFSG.LocalAnalysis.StandardType.GGTWZK
public import CFSG.LocalAnalysis.StandardType.GGTWZKUnitary
public import CFSG.LocalAnalysis.StandardType.GGTWZKE6
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certs


theorem ggTWZKInput_holds : GGTWZKInput := by
  intro G _ _ p B Bs x L D J y K hH hp labJ labK hJΛ hKΛ hJLab hKLab hJtag hpJ hStage hSide
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hprime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  intro hcenter
  have hlist := oddCenterPrimeLabel_of_resHyp_of_dvd_card_center hH hKΛ hKLab hcenter
  rcases labK with ⟨t, r, f⟩
  rcases hlist with ⟨ht, hd, hq⟩ | ⟨ht, hd, hq⟩ | ⟨ht, hp3, hq⟩ |
    ⟨ht, hp3, hq⟩ | ⟨ht, hp3⟩
  · change t = .A at ht
    subst t
    have hr : 4 ≤ r := by
      have hr1 : 1 ≤ r := hKΛ.2.1
      by_contra h
      have hrle : r ≤ 3 := by omega
      by_cases hr3 : r = 3
      · subst r
        have h4 : p ∣ 2 ^ 2 := by simpa using hd
        have hpTwo := Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two
        exact hp2 (hpTwo.mp (hprime.dvd_of_dvd_pow h4))
      · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKLab
          (Or.inl ⟨rfl, show r = 1 ∨ r = 2 by omega⟩)
    exact not_ggResSideDatum_of_linear_centerPrime hRig hLB hH hr hq hd hKΛ hKLab
      hJΛ hJLab hJtag hpJ hSide
  · change t = .twA at ht
    subst t
    have hr : 4 ≤ r := by
      have hr2 : 2 ≤ r := hKΛ.2.1
      by_contra h
      have hrle : r ≤ 3 := by omega
      by_cases hr3 : r = 3
      · subst r
        have h4 : p ∣ 2 ^ 2 := by simpa using hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
          (hprime.dvd_of_dvd_pow h4))
      · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKLab
          (Or.inr (Or.inr (Or.inl ⟨rfl, show r = 2 by omega⟩)))
    by_cases hr5 : r = 5
    · subst r
      have hp3 : p = 3 := by
        have h6 : p ∣ 2 * 3 := by simpa using hd
        rcases hprime.dvd_mul.mp h6 with hpTwo | hpThree
        · exact False.elim (hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hpTwo))
        · exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).mp hpThree
      subst p
      exact ggZK_unitary_dangerous_six hRig hLB hH hKLab hKΛ hq hJΛ hJLab hJtag hpJ hSide
    · exact ggZK_unitary_dangerous_of_J_le_K hRig hH hr hr5 hq hd hKLab hKΛ
        hJΛ hJLab hJtag hpJ hSide (hH.J_le_K_of_typeA hLB hJΛ hJLab hJtag hpJ)
  · subst p
    exact not_ggResHyp_of_E6_of_three_dvd_rank_add_three hRig hLB hH hJΛ hKΛ hJLab hKLab
      hJtag hpJ (Or.inl ht)
  · subst p
    exact not_ggResHyp_of_E6_of_three_dvd_rank_add_three hRig hLB hH hJΛ hKΛ hJLab hKLab
      hJtag hpJ (Or.inr ht)
  · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKLab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))

end Certs

end CFSG.StandardType

end
