module

public import CFSG.Quasithin.Background.SimsE215KF1Star

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

theorem kf1All_of_packages (h22 : E2.E22StatementNoN) (hsolv : SolvableKF1)
    (h1 : PkgL2PairedKF1) (h2 : PkgSzPairedKF1) (h3 : PkgOddPairedKF1) (h4 : PkgBenderSingleKF1)
    (h5 : PkgL3KF1) (h6 : PkgSp4TwoKF1) (h6' : PkgSp4OneKF1) (h7 : PkgOddSingleKF1)
    (h8 : PkgOddL3KF1) {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}
    (hyp : E2.Hyp28 H T M V) (hchar : CharTwo H) : KF1All H T M V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hns : Group.IsSolvable H
  · exact hsolv G H T M V hyp hchar hns
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hyp.elem)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hv ▸ Subgroup.relIndex_dvd_card (V ⊓ pCoreOf 2 H) V)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hyp.not_le_pCoreOf (le_inf_iff.1 hj).2
  by_cases hj1 : j = 1
  · subst hj1
    exact kf1All_of_relIndex_eq_two hyp (by rw [hj, pow_one])
  have h4le : 4 ≤ (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [hj]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
  obtain ⟨⟨K, hK, hHK, hq, hcases⟩, hsq⟩ := h22 G H T M hyp.minParabolic hyp.sqtk hns
  have hS : Setting H T M V K := ⟨hyp, hchar, hns, h4le, hK, hHK, hq, hsq⟩
  dsimp only [E2.E22CasesNoN] at hcases
  rcases hcases with
    ⟨hJ, t, ht, hKt, hM, ⟨n, hn, hPS | hSz, hB⟩ |
      ⟨p, hp, hp8, hPSL, hMK, haut⟩⟩ |
    ⟨hTK, hker, ⟨n, hBe, hB⟩ | ⟨n, hn, hL3 | hSp, hD, hB⟩ |
      ⟨p, e, hp, hp3, he, hpe, hPSL, hMK, haut⟩ | ⟨p, hp, hp2, hcase, hMK⟩⟩
  · exact kf1All_of_starCentral hyp
      (h1 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ n hn hPS hB)
  · exact kf1All_of_starCentral hyp
      (h2 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ n hn hSz hB)
  · exact kf1All_of_starCentral hyp
      (h3 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ p hp hp8 hPSL hMK haut)
  · exact kf1All_of_starCentral hyp (h4 G H T M V K hS ⟨hTK, hker⟩ n hBe hB)
  · exact kf1All_of_starCentral hyp
      (h5 G H T M V K hS ⟨hTK, hker⟩ n hn hL3 hD hB)
  · by_cases hn1 : n = 1
    · subst n
      exact kf1All_of_starCentral hyp
        (h6' G H T M V K hS ⟨hTK, hker⟩ hSp hD hB)
    · have hn2 : 2 ≤ n := by omega
      exact kf1All_of_starCentral hyp
        (h6 G H T M V K hS ⟨hTK, hker⟩ n hn2 hSp hD hB)
  · exact kf1All_of_starCentral hyp
      (h7 G H T M V K hS ⟨hTK, hker⟩ p e hp hp3 he hpe hPSL hMK haut)
  · exact kf1All_of_starCentral hyp
      (h8 G H T M V K hS ⟨hTK, hker⟩ p hp hp2 hcase hMK)

theorem e215_two_printed_of_packages
    (h22 : E2.E22StatementNoN) (hsolv : SolvableKF1)
    (h1 : PkgL2PairedKF1) (h2 : PkgSzPairedKF1) (h3 : PkgOddPairedKF1) (h4 : PkgBenderSingleKF1)
    (h5 : PkgL3KF1) (h6 : PkgSp4TwoKF1) (h6' : PkgSp4OneKF1) (h7 : PkgOddSingleKF1)
    (h8 : PkgOddL3KF1) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V),
      CharTwo H → IsTISetIn V M →
      ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
        ∀ A : Subgroup Γ, A = conjSubgroup V g ⊓ pCoreOf 2 H → rAV (autI h.elem A) < 2 := by
  intro Γ _ _ H T M V h hc hTI I g hI hg hgen A hA
  have hK : KF1All H T M V :=
    kf1All_of_packages h22 hsolv h1 h2 h3 h4 h5 h6 h6' h7 h8 h hc
  have hlt := rAV_lt_two_of_kf1 h hc hTI hI hg hgen (hK I g hI hg hgen)
  subst A
  exact hlt

end CFSG.Quasithin.SimsE2.KF1
