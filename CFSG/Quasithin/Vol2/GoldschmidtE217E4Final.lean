module

public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Main
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Paired1a
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4One
public import CFSG.Quasithin.Vol2.GoldschmidtE217Bender
public import CFSG.Quasithin.Vol2.GoldschmidtE217Odd
public import CFSG.Quasithin.Vol2.GoldschmidtE217Paired
public import CFSG.Quasithin.Vol2.GoldschmidtE217PairedSz
public import CFSG.Quasithin.Vol2.GoldschmidtE217R1
public import CFSG.Quasithin.Vol2.GoldschmidtE217Sp4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M E217R1 E217R3 CFSG.GH74.GLS.IVK CFSG.GH74.GLS

namespace E217R4

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem r1_odd4
    (hL : R1Leaves) (h22 : E2.E22StatementNoN) (hyp : Hyp28 H T M V) (hchar : CharTwo H)
    (hns : ¬ Group.IsSolvable H) (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G))
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H)) :
    (V ⊓ pCoreOf 2 H).relIndex V = 2 ∨
      ∃ K : Subgroup G, Setting4 H T M V K ∧ Case1 H T M K ∧ ∃ p : ℕ, p.Prime ∧
        (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥(E2.star M H K) ∧
        E2.star M H (M ⊓ K) =
          E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) ∧
        8 < E2.autCard (E2.star M H T) (E2.star M H K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hyp.elem)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hv ▸ Subgroup.relIndex_dvd_card (V ⊓ pCoreOf 2 H) V)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hyp.not_le_pCoreOf (le_inf_iff.1 hj).2
  by_cases hj1 : j = 1
  · left
    rw [hj, hj1, pow_one]
  right
  have h4le : 4 ≤ (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [hj]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
  obtain ⟨⟨K, hK, hHK, hq', hcases⟩, hsq⟩ := h22 G H T M hyp.minParabolic hyp.sqtk hns
  have hS : Setting H T M V K := ⟨hyp, hchar, hns, h4le, hK, hHK, hq', hsq⟩
  refine ⟨K, ⟨hS, hV16, hq, hres⟩, ?_⟩
  dsimp only [E2.E22CasesNoN] at hcases
  rcases hcases with ⟨hJ, t, ht, hKt, hM, ⟨n, hn, hPS | hSz, hB⟩ | ⟨p, hp, hp8, hPSL, hMK, haut⟩⟩ |
    ⟨hTK, hker, ⟨n, hBe, hB⟩ | ⟨n, hn, hL3 | hSp, hD, hB⟩ |
      ⟨p, e, hp, hp3, he, hpe, hPSL, hMK, haut⟩ | ⟨p, hp, hp2, hcase, hMK⟩⟩
  · exact (false_of_pairedL2 hL.a38 hS ⟨hJ, t, ht, hKt, hM⟩ hn hPS hres).elim
  · exact (false_of_pairedSz hL.a38 hS ⟨hJ, t, ht, hKt, hM⟩ hSz hres).elim
  · exact ⟨⟨hJ, t, ht, hKt, hM⟩, p, hp, hp8, hPSL, hMK, haut⟩
  · obtain ⟨hn2, hLi | hSz | hU⟩ := hBe
    · exact (false_of_benderL2Sz hS ⟨hTK, hker⟩ hn2 (Or.inl hLi) hV16 hq).elim
    · exact (false_of_benderL2Sz hS ⟨hTK, hker⟩ hn2 (Or.inr hSz) hV16 hq).elim
    · exact (false_of_benderU3 hS ⟨hTK, hker⟩ hn2 hU hV16 hq).elim
  · exact (false_of_l3 hS ⟨hTK, hker⟩ hn hL3 hD hB hV16 hq).elim
  · exact (false_of_sp4 hL.irr hL.g41 hL.cTwo hS ⟨hTK, hker⟩ hn hSp hD hB hV16 hq).elim
  · exact (OS.false_of_oddSingle hL.ivk12 hL.ivk13a hL.ivk13b hL.coat hS ⟨hTK, hker⟩ hp hp3 he
      hPSL hMK haut).elim
  · exact (false_of_oddL3 hL.outerInv hL.noQuad hS ⟨hTK, hker⟩ hp hp2 hcase hMK).elim

theorem e217NonsolvableNarrow_of_packages_odd4
    (hL : R1Leaves)
    (h22 : E2.E22StatementNoN) (p1a : R3Pkg1a) (p1b : R3Pkg1b) (p2a : R3Pkg2a) (p2b : R3Pkg2b)
    (p2c : R3Pkg2c) (p2d : R3Pkg2d) (pOdd4 : R4PkgOdd4) : E2.E217NonsolvableNarrow := by
  intro Γ _ _ H T M V hyp hchar _ hq hres hV16 hns hlt
  exfalso
  have hq' : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H) := hq.symm.le
  rcases r1_odd4 hL h22 hyp hchar hns hres hV16 hq' with h2 |
    ⟨K, hS, h1, p, hp, hp8, hPSL, hMK, haut⟩
  · obtain ⟨⟨K, hK, hHK, hqs, hcases⟩, hsq⟩ := h22 Γ H T M hyp.minParabolic hyp.sqtk hns
    have hS2 : Setting2 H T M V K := ⟨⟨hyp, hchar, h2, hV16, hq', hres⟩, hns, hK, hHK, hqs, hsq⟩
    dsimp only [E2.E22CasesNoN] at hcases
    rcases hcases with
      ⟨hJ, t, ht, hKt, hM, ⟨n, hn, hPS | hSz, hB⟩ | ⟨p, hp, hp8, hPSL, hMK, haut⟩⟩ |
      ⟨hTK, hker, ⟨n, hBe, hB⟩ | ⟨n, hn, hL3 | hSp, hD, hB⟩ |
        ⟨p, e, hp, hp3, he, hpe, hPSL, hMK, haut⟩ | ⟨p, hp, hp2, hcase, hMK⟩⟩
    · exact p1a Γ H T M V K hS2 hlt ⟨hJ, t, ht, hKt, hM⟩ n hn (Or.inl hPS) hB
    · exact p1a Γ H T M V K hS2 hlt ⟨hJ, t, ht, hKt, hM⟩ n hn (Or.inr hSz) hB
    · exact p1b Γ H T M V K hS2 hlt ⟨hJ, t, ht, hKt, hM⟩ p hp hp8 hPSL hMK haut
    · exact p2a Γ H T M V K hS2 hlt ⟨hTK, hker⟩ n hBe hB
    · exact p2b Γ H T M V K hS2 hlt ⟨hTK, hker⟩ n hn (Or.inl hL3) hD hB
    · exact p2b Γ H T M V K hS2 hlt ⟨hTK, hker⟩ n hn (Or.inr hSp) hD hB
    · exact p2c Γ H T M V K hS2 hlt ⟨hTK, hker⟩ p e hp hp3 he hpe hPSL hMK haut
    · exact p2d Γ H T M V K hS2 hlt ⟨hTK, hker⟩ p hp hp2 hcase hMK
  · exact pOdd4 Γ H T M V K hS hlt h1 p hp hp8 hPSL hMK haut

theorem e217NonsolvableNarrow_of_three_leaves
    (hL : R1Leaves)
    (h22 : E2.E22StatementNoN) (hNot : KFactL3U3NotOddCube) (p2b : R3Pkg2bOne)
    (p2c : R3Pkg2c7) (p2d : R3Pkg2d3) : E2.E217NonsolvableNarrow :=
  e217NonsolvableNarrow_of_packages_odd4 hL h22 (r3Pkg1a hL.a38)
    (r3Pkg1b_of_seven hL.a38 (r3Pkg1b7 hL.a38)) r3Pkg2a (r3Pkg2b_of_one p2b)
    (r3Pkg2c_of_seven hL.ivk12 hL.ivk13a hL.ivk13b hL.coat p2c)
    (r3Pkg2d_of_three hL.outerInv hNot p2d) (r4PkgOdd4 hL.a38)

end E217R4

end CFSG.Quasithin
