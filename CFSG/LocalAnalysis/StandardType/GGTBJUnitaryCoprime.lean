module

public import CFSG.LocalAnalysis.StandardType.GGTBJEThree
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTBJUnitaryCoprime_not_six {p r f : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hpd : ¬ p ∣ r + 1) : ¬ (r = 5 ∧ f = 1) := by
  rintro ⟨h5, h1⟩
  apply hpd
  have hp3 : p ∣ 3 := by simpa [h1] using hpq
  have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  rw [h5, hp3']
  norm_num

theorem ggTBJLeftOn_unitaryCoprime
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn (fun p lab => GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank) := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hlabel, hr⟩ := hP.1
  rcases hlabel with ⟨htag, hpq, hpd⟩ | ⟨_, hr3, _⟩
  · have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
      rcases lab with ⟨t, r, n⟩
      simp only at htag
      subst htag
      rfl
    have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
      rw [← hlab]
      exact hΛ
    have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) := by
      rw [← hlab]
      exact hhas
    rcases ggTBJLeft_unitaryCoprime_of_label hRig hH hr
        (ggTBJUnitaryCoprime_not_six hH.1.tableB_facts.1 hpq hpd) hpq hpd hhas' hΛ' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · omega

theorem ggTBJNbrOn_unitaryCoprime
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) :
    GGTBJNbrOn (fun p lab => GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank) := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨hlabel, hr⟩ := hP.1
  rcases hlabel with ⟨htag, hpq, hpd⟩ | ⟨_, hr3, _⟩
  · have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
      rcases lab with ⟨t, r, n⟩
      simp only at htag
      subst htag
      rfl
    have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
      rw [← hlab]
      exact hΛ
    have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) := by
      rw [← hlab]
      exact hhas
    rcases ggTBJNbr_unitaryCoprime_of_label hRig hI3 hLB hSP hH hr
        (ggTBJUnitaryCoprime_not_six hH.1.tableB_facts.1 hpq hpd) hpq hpd hhas' hΛ' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · omega

theorem ggTBJOrderRestSympMinusOne_of_unitaryCoprime
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (h : GGTBJOrderRestUnitaryCoprimeInput) : GGTBJOrderRestSplitAUnitSpPlusEThreeLinMinusUniMinusSympMinusGeTwoOrthSympMinusOneInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_unitaryCoprime hRig)
    (ggTBJNbrOn_unitaryCoprime hRig hI3 hLB hSP) h

end CFSG.StandardType

end
