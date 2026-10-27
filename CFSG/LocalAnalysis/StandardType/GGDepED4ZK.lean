module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4ZKClassical
public import CFSG.LocalAnalysis.StandardType.GGDepED4ZKE6
public import CFSG.LocalAnalysis.StandardType.GGTWZK
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certs


theorem ggDepED4ZKInput_holds : GGDepED4ZKInput := by
  intro G _ _ B Bs x L D J y K hH labJ hJΛ hJHas hJtag hJrank hcard hSide hyK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  obtain ⟨labK, hKΛ, hKHas, -⟩ :=
    largeEvenMarking_exists_hasLabel (hH.2.2.1.2 y K hH.2.2.2.2.1)
  obtain ⟨hyC, hy1, hy3, hKperf⟩ := hH.data_K
  have horder : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcenter : 3 ∣ Nat.card (Subgroup.center K) := by
    have hyZ : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC k k.2)
    have hd := orderOf_dvd_natCard (⟨⟨y, hyK⟩, hyZ⟩ : Subgroup.center K)
    rwa [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, horder] at hd
  have hlist := oddCenterPrimeLabel_of_resHyp_of_dvd_card_center hH hKΛ hKHas hcenter
  rcases labK with ⟨t, r, f⟩
  rcases hlist with ⟨ht, hd, hq⟩ | ⟨ht, hd, hq⟩ | ⟨ht, hp3, hq⟩ |
      ⟨ht, hp3, hq⟩ | ⟨ht, hp3⟩
  · change t = .A at ht
    subst t
    have hr : 4 ≤ r := by
      have hr1 : 1 ≤ r := hKΛ.2.1
      by_contra h
      by_cases hr3 : r = 3
      · subst r
        norm_num at hd
      · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKHas
          (Or.inl ⟨rfl, show r = 1 ∨ r = 2 by omega⟩)
    exact not_ggResSideDatum_of_linear_of_label_D4 hRig hLB rfl hH hr hq hKΛ hKHas
      hJΛ hJHas hJtag hJrank hSide
  · change t = .twA at ht
    subst t
    have hr : 4 ≤ r := by
      have hr2 : 2 ≤ r := hKΛ.2.1
      by_contra h
      by_cases hr3 : r = 3
      · subst r
        norm_num at hd
      · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKHas
          (Or.inr (Or.inr (Or.inl ⟨rfl, show r = 2 by omega⟩)))
    by_cases hr5 : r = 5
    · subst r
      exact not_ggResSideDatum_of_unitary_six_of_label_D4 hRig hLB hH hq hKΛ hKHas
        hJΛ hJHas hJtag hJrank hSide
    · exact not_ggResSideDatum_of_unitary_of_label_D4 hRig hLB rfl hH hr hr5 hq hd
        hKΛ hKHas hJΛ hJHas hJtag hJrank hSide
  · exact not_ggResSideDatum_of_E6_three_of_label_D4 hRig hLB hH hcard
      hJΛ hJHas hJtag hJrank hKΛ hKHas ht hq hSide
  · exact not_ggResSideDatum_of_twE6_three_of_label_D4 hRig hLB hH hcard
      hJΛ hJHas hJtag hJrank hKΛ hKHas ht hq hSide
  · exact not_ggResHyp_of_smallRank_label hRig hH hKΛ hKHas
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))

end Certs

end CFSG.StandardType

end
