module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedLinear
public import CFSG.LocalAnalysis.StandardType.GGAllFixedTwA
public import CFSG.LocalAnalysis.StandardType.GGAllFixedSymplectic
public import CFSG.LocalAnalysis.StandardType.GGAllFixedOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalRegular
public import CFSG.LocalAnalysis.StandardType.GGAllFixedF4Three
public import CFSG.LocalAnalysis.StandardType.GGAllFixedE7Three
public import CFSG.LocalAnalysis.StandardType.GGAllFixedE6Three
public import CFSG.LocalAnalysis.StandardType.GGAllFixedTwE6
public import CFSG.LocalAnalysis.StandardType.GGAllFixedE8Five
public import CFSG.LocalAnalysis.StandardType.GGAllFixedE6Seven
public import CFSG.LocalAnalysis.StandardType.GGCSRLabels
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1SolvDefs

public section
namespace CFSG.StandardType
open CFSG.Assembly


theorem isSolvable_inf_centralizer_of_ggConfig
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hAll : GGInnerDiagAll p B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hperf, lab, hlab, hdatum⟩ := ggAllFixedArithMarking_no_small_twisted
    ggLabelRigidInput_holds ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest
      (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)) hcfg hAll hX
  obtain ⟨_, _, _, _, _, _, _, htw, hhalf, _⟩ := largeEvenRawDatum_exists hdatum
  have hOne : LargeEvenMarking ↥X fun lab' R _ I _ θ =>
      lab' = lab ∧ ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) ∧
        IsElemAbelian p (ggBeta X θ hN).range ∧
        ((ggBeta X θ hN).range : Set (MulAut R)) ⊆ I ∧
        p ^ 3 ≤ Nat.card (ggBeta X θ hN).range := by
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hdatum⟩
    rintro R _ I F ⟨hs, hna, θ, -, -, hN, hInv, -, hE, hEI, hcard⟩
    exact ⟨hs, hna, θ, rfl, hN, hInv, hE, hEI, hcard⟩
  rcases largeEvenHalfSplit_dvd hlab hhalf with hdvd | ⟨hp7, hexc⟩
  · have hsmall : ¬ GGRootGenSmallRankLabel p lab := by
      intro hs
      apply not_largeEvenMarking_smallRank (X := ↥X) hp hp2
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
      exact ⟨hs, (ggBeta X θ hN).range, hEI, hE, hcard⟩
    have hexc : ¬ GGRootGenSmallExcLabel p lab := by
      intro hs
      have hopen : GGRootGenOpenLabel p lab := by
        refine ⟨?_, ?_⟩
        · have heq : (2 ^ lab.n) ^ 2 = 4 ^ lab.n := by
            rw [← pow_mul, Nat.mul_comm, pow_mul]
            norm_num
          change p ∣ 4 ^ lab.n - 1
          rwa [heq] at hdvd
        · rcases hs with h | h | h <;> simp [GGTypeALabel, h]
      apply not_largeEvenMarking_smallExc (X := ↥X) hp hp2
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
      exact ⟨⟨hs, hopen⟩, (ggBeta X θ hN).range, hEI, hE, hcard⟩
    have hG2der : lab.tag ≠ .G2der := by
      intro ht
      apply ggInndiag_pRank_le_two_G2der (X := ↥X) hp hp2
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
      exact ⟨ht, (ggBeta X θ hN).range, hEI, hE, hcard⟩
    obtain ⟨tag, rank, n⟩ := lab
    cases tag with
    | A =>
      apply isSolvable_inf_centralizer_of_regular_A_marking hcfg
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
      exact ⟨rfl, hdvd, hN, hEI, hE.isPGroup⟩
    | twA =>
      have hr : 3 ≤ rank := by
        have hlow : 2 ≤ rank := hlab.2.1
        have hne : rank ≠ 2 := fun h => hsmall (by simp [GGRootGenSmallRankLabel, h])
        omega
      apply isSolvable_inf_centralizer_of_unitary_marking hcfg
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
      exact ⟨Or.inl ⟨rfl, hr⟩, hdvd, hN, hEI, hE⟩
    | B | C =>
      apply isSolvable_inf_centralizer_of_symplectic_marking hcfg
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
      exact ⟨by simp, hdvd, hN, hEI, hE.isPGroup⟩
    | D | twD =>
      have hr : 3 ≤ rank := by
        first
        | exact hlab.2
        | have hlow : 2 ≤ rank := hlab.2
          have hne : rank ≠ 2 := fun h => hsmall (by simp [GGRootGenSmallRankLabel, h])
          omega
      apply isSolvable_inf_centralizer_of_orthogonal_marking hcfg
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
      exact ⟨⟨by simp, hr⟩, hdvd, hN, hEI, hE⟩
    | E6 =>
      have hr : rank = 0 := hlab.2
      subst rank
      by_cases hp3 : p = 3
      · subst p
        apply isSolvable_inf_centralizer_of_E6_three_rank_three_marking hcfg
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
        exact ⟨rfl, rfl, hdvd, hN, hEI, hE, hcard⟩
      · apply isSolvable_inf_centralizer_of_nonTorsion_marking hcfg hp hpodd hp3
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨by simp, rfl, by simp, hdvd, hN, hEI, hE⟩
    | E7 =>
      have hr : rank = 0 := hlab.2
      subst rank
      by_cases hp3 : p = 3
      · subst p
        apply isSolvable_inf_centralizer_of_E7Three_marking hcfg
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨rfl, rfl, rfl, hN, hEI, hE⟩
      · apply isSolvable_inf_centralizer_of_nonTorsion_marking hcfg hp hpodd hp3
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨by simp, rfl, by simp, hdvd, hN, hEI, hE⟩
    | E8 =>
      have hr : rank = 0 := hlab.2
      subst rank
      by_cases hp3 : p = 3
      · subst p
        apply isSolvable_inf_centralizer_of_E8Three_marking hcfg hX
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨rfl, rfl, rfl, hdvd, hN, hEI, hE⟩
      · by_cases hp5 : p = 5
        · subst p
          apply isSolvable_inf_centralizer_of_E8Five_marking hcfg
          refine largeEvenMarking_mono ?_ hOne
          rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
          exact ⟨rfl, rfl, rfl, hdvd, hN, hEI, hE, hcard⟩
        · apply isSolvable_inf_centralizer_of_nonTorsion_marking hcfg hp hpodd hp3
          refine largeEvenMarking_mono ?_ hOne
          rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
          exact ⟨by simp, rfl, fun _ => hp5, hdvd, hN, hEI, hE⟩
    | F4 =>
      have hr : rank = 0 := hlab.2
      subst rank
      by_cases hp3 : p = 3
      · subst p
        apply isSolvable_inf_centralizer_of_F4Three_marking hcfg
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
        exact ⟨rfl, rfl, rfl, hdvd, hN, hEI, hE, hcard⟩
      · apply isSolvable_inf_centralizer_of_nonTorsion_marking hcfg hp hpodd hp3
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨by simp, rfl, by simp, hdvd, hN, hEI, hE⟩
    | twE6 =>
      by_cases hp3 : p = 3
      · subst p
        apply isSolvable_inf_centralizer_of_twE6_three_rank_three_marking hcfg
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
        exact ⟨rfl, hdvd, hN, hEI, hE, hcard⟩
      · apply isSolvable_inf_centralizer_of_twE6_nonTorsion_marking hcfg hp hpodd hp3
        refine largeEvenMarking_mono ?_ hOne
        rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, -⟩
        exact ⟨rfl, hdvd, hN, hEI, hE⟩
    | G2 | triD4 | twF4 => exact False.elim (hexc (by simp [GGRootGenSmallExcLabel]))
    | twB2 | twF4der => exact False.elim (htw (by simp))
    | B2der => exact False.elim (hsmall (by simp [GGRootGenSmallRankLabel]))
    | G2der => exact False.elim (hG2der rfl)
  · subst p
    rcases hexc with hA | hE6
    · apply isSolvable_inf_centralizer_of_A8Seven_marking
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, hInv, hE, hEI, hcard⟩
      exact ⟨hA, hN, hInv, hE, hEI, hcard⟩
    · apply isSolvable_inf_centralizer_of_E6Seven_marking
      refine largeEvenMarking_mono ?_ hOne
      rintro lab' R _ I F θ ⟨rfl, hN, -, hE, hEI, hcard⟩
      exact ⟨hE6, hN, hEI, hE, hcard⟩

theorem ggSecFiveAllFixedSolvInput_holds : GGSecFiveAllFixedSolvInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg X hX
  exact isSolvable_inf_centralizer_of_ggConfig hcfg.1.1 hcfg.1.2.2.1 hX

end CFSG.StandardType
