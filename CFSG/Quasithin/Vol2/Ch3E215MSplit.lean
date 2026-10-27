module

public import CFSG.Quasithin.Vol2.Ch3E215MG
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

theorem e215Concl_of_packages (h22 : E2.E22StatementNoN) (h1 : PkgL2Paired215)
    (h2 : PkgSzPaired215) (h3 : PkgOddPaired215) (h4 : PkgBenderSingle215) (h5 : PkgL3215)
    (h6 : PkgSp4215) (h7 : PkgOddSingle215) (h8 : PkgOddL3215) {G : Type} [Group G] [Finite G]
    {H T M V : Subgroup G} (hyp : E2.Hyp28 H T M V) (hchar : CharTwo H)
    (hns : ¬ Group.IsSolvable H) : E215Concl H T M V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hyp.elem)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hv ▸ Subgroup.relIndex_dvd_card (V ⊓ pCoreOf 2 H) V)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hyp.not_le_pCoreOf (le_inf_iff.1 hj).2
  by_cases hj1 : j = 1
  · subst hj1
    exact e215Concl_of_relIndex_eq_two hyp hchar (by rw [hj, pow_one])
  have h4le : 4 ≤ (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [hj]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
  obtain ⟨⟨K, hK, hHK, hq, hcases⟩, hsq⟩ := h22 G H T M hyp.minParabolic hyp.sqtk hns
  have hS : Setting H T M V K := ⟨hyp, hchar, hns, h4le, hK, hHK, hq, hsq⟩
  dsimp only [E2.E22CasesNoN] at hcases
  rcases hcases with ⟨hJ, t, ht, hKt, hM, ⟨n, hn, hPS | hSz, hB⟩ | ⟨p, hp, hp8, hPSL, hMK, haut⟩⟩ |
    ⟨hTK, hker, ⟨n, hBe, hB⟩ | ⟨n, hn, hL3 | hSp, hD, hB⟩ |
      ⟨p, e, hp, hp3, he, hpe, hPSL, hMK, haut⟩ | ⟨p, hp, hp2, hcase, hMK⟩⟩
  · exact h1 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ n hn hPS hB
  · exact h2 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ n hn hSz hB
  · exact h3 G H T M V K hS ⟨hJ, t, ht, hKt, hM⟩ p hp hp8 hPSL hMK haut
  · exact h4 G H T M V K hS ⟨hTK, hker⟩ n hBe hB
  · exact h5 G H T M V K hS ⟨hTK, hker⟩ n hn hL3 hD hB
  · exact h6 G H T M V K hS ⟨hTK, hker⟩ n hn hSp hD hB
  · exact h7 G H T M V K hS ⟨hTK, hker⟩ p e hp hp3 he hpe hPSL hMK haut
  · exact h8 G H T M V K hS ⟨hTK, hker⟩ p hp hp2 hcase hMK

theorem e215Member_of_packages (h22 : E2.E22StatementNoN) (h1 : PkgL2Paired215)
    (h2 : PkgSzPaired215) (h3 : PkgOddPaired215) (h4 : PkgBenderSingle215) (h5 : PkgL3215)
    (h6 : PkgSp4215) (h7 : PkgOddSingle215) (h8 : PkgOddL3215) : Ch3n.E215Member := by
  intro G _ _ H T M V hyp hchar hTI hns
  obtain ⟨g, hg, hP, hcI, hIV, hrank, hdata⟩ :=
    e215Concl_of_packages h22 h1 h2 h3 h4 h5 h6 h7 h8 hyp hchar hns
  exact ⟨g, hg, hP, hcI, hIV, count_lt_of_e215DataOf hP hcI hIV hrank
    (fun hZ => le_normalizer_of_isTISetIn hP inf_le_left hTI hZ) hdata⟩

end CFSG.Quasithin.Ch3E215M
