module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePLA28
public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggForkA8TablePLInput_of_a28 (h6 : GGNbrTablePNbrInputOn GGRegimeA8Seven)
    (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hA : GGForkA8TablePLA28Input) : GGForkA8TablePLInput := by
  intro G _ _ p B Bs x L D J hC hID hp y K hK hlab labJ labL hlabJ hlabL hhasJ hhasL
  subst hp
  rcases hlab with hKA8 | hKE6
  ·
    obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
      ggForkA8TableP_clauseK_of_tpOn h6 h5 hTCJ hRig hC hID hK (Or.inl hKA8) labJ hlabJ hhasJ
    obtain ⟨lab, labJ', hlab', hsplit, hhasL', hlabJ'2, hdvd, hhasJ'⟩ :=
      ggNbr_label_J_of_tcj hTCJ hC hK
    have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
    have hn1 : 1 ≤ lab.n := hlab'.1
    have hkA : klab = ⟨.A, 8, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inl rfl)
      (hRig klab ⟨.A, 8, 1⟩ _ hkΛ largeEvenInLambda2_a8 hhasK1 hKA8)
    subst hkA
    obtain ⟨t, r, n⟩ := jlab
    rcases ggTablePRow_a8_left hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    ·
      have hLlab := hA G B Bs x L D J hC hID y K hK hKA8 hhasJ1
      rcases hLlab with hL | hL | hL
      · refine ⟨⟨.A, 2, 3⟩, ⟨.A, 3, 3⟩, by simp [LargeEvenInLambda2],
          by simp [LargeEvenInLambda2], ?_, hhasJ1, hL⟩
        exact Or.inl ⟨rfl, by norm_num, by norm_num, Or.inl rfl⟩
      · refine ⟨⟨.A, 2, 3⟩, ⟨.C, 3, 3⟩, by simp [LargeEvenInLambda2],
          by simp [LargeEvenInLambda2], ?_, hhasJ1, hL⟩
        exact Or.inl ⟨rfl, by norm_num, by norm_num, Or.inr (Or.inr (Or.inl rfl))⟩
      · refine ⟨⟨.A, 2, 3⟩, ⟨.twD, 4, 3⟩, by simp [LargeEvenInLambda2],
          by simp [LargeEvenInLambda2], ?_, hhasJ1, hL⟩
        exact Or.inl ⟨rfl, by norm_num, by norm_num,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    ·
      exfalso
      rcases ggLabelIso_typeA_cases hRig (r := 5) (f := 1) (by norm_num) hlabJ'2 hjΛ hhasJ'
        hhasJ1 with rfl | ⟨h53, -⟩
      · have hle : lab.n ≤ 1 := Nat.le_of_dvd one_pos hdvd
        have h3le : 3 ≤ lab.n := Nat.le_of_dvd hn1 h3
        omega
      · omega
  ·
    exact (ggForkA8_not_e6Nbr h5 hTCJ hRig hC hID hK hKE6).elim

theorem ggForkA8TablePLInput_holds
    (h6 : GGNbrTablePNbrInputOn GGRegimeA8Seven) (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) : GGForkA8TablePLInput :=
  ggForkA8TablePLInput_of_a28 h6 h5 hTCJ hRig (ggForkA8TablePLA28_holds hTCJ hRig)

end CFSG.StandardType

end
