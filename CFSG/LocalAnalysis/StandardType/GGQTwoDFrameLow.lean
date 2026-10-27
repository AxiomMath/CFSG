module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
public import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoD_four_le_rank
    (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hn : lab.n = 1)
    (htag : lab.tag = .D ∨ lab.tag = .twD) : 4 ≤ lab.rank := by
  have hp3 : p = 3 := ggQTwoD_p_eq_three hRig hcfg hΛ hhas hn
  subst hp3
  by_contra hlt
  have hle : lab.rank ≤ 3 := not_lt.1 hlt
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hM : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  have hrel := ggInnerDiagOn_relabel hRig hM hΛ hhas
  have hK : commutator ↥L = ⊤ := hrel.1
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag hn hle
  subst hn
  rcases htag with ht | ht <;> subst ht
  ·
    dsimp only [LargeEvenInLambda2] at hΛ
    have hr : r = 3 := le_antisymm hle hΛ.2
    subst hr
    have hbad : LargeEvenMarking ↥L (fun lab' R _ I _ _ => lab' = ⟨.D, 3, 1⟩ ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
          3 ^ 3 ≤ Nat.card E) :=
      largeEvenMarking_mono (fun lab' R _ I F θ hP => by
        obtain ⟨hN, hI⟩ := hP.2
        have hres := ggBeta_range_rank_three_of_innerDiag hconf (Or.inl rfl) I θ hN hK hI
        exact ⟨hP.1, _, hres.2.1, hres.1, hres.2.2⟩) hrel
    have hall : ∀ lab, LargeEvenInLambda2 lab → lab = ⟨.D, 3, 1⟩ →
        LargeEvenLabelAll lab (fun R _ I _ => IsSimpleGroup R →
          (∃ a b : R, a * b ≠ b * a) → ∀ E : Subgroup (MulAut R),
            (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E → Nat.card E < 3 ^ 3) := by
      intro lab hlab heq
      subst heq
      refine (largeEvenLabelAll_card_lt_linear_of_ord (p := 3) Nat.prime_three (by norm_num)
        (Or.inr ⟨rfl, rfl⟩) ?_).mono ?_
      · intro j hj hj4
        have hj4' : 3 * j ≤ 4 := by simpa using hj4
        have hj1 : j = 1 := by omega
        subst hj1
        norm_num
      · intro R _ I F hX _ _ E hEI hE
        exact hX E hEI hE
    exact (not_largeEvenMarking_of_labelAll_card_lt hall) hbad
  ·
    dsimp only [LargeEvenInLambda2] at hΛ
    have h2r : 2 ≤ r := hΛ.2
    interval_cases r
    ·
      have hbad : LargeEvenMarking ↥L (fun lab' R _ I _ _ =>
          (lab'.tag = .twD ∧ lab'.rank = 2) ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
            3 ^ 3 ≤ Nat.card E) :=
        largeEvenMarking_mono (fun lab' R _ I F θ hP => by
          obtain ⟨hN, hI⟩ := hP.2
          have hres := ggBeta_range_rank_three_of_innerDiag hconf (Or.inl rfl) I θ hN hK hI
          exact ⟨⟨by rw [hP.1], by rw [hP.1]⟩, _, hres.2.1, hres.1,
            hres.2.2⟩) hrel
      exact (ggInndiag_pRank_le_two_twD2 (X := ↥L) Nat.prime_three (by norm_num)) hbad
    ·
      have hbad : GGInnerDiagOnLabel
          (fun p lab => (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧
            p ∣ 2 ^ lab.n + 1) 3 Bs L :=
        largeEvenMarking_mono (fun lab' R _ I F θ hP =>
          ⟨⟨by rw [hP.1]; exact Or.inr rfl, by rw [hP.1], by rw [hP.1]; norm_num⟩,
            hP.2.1, hP.2.2⟩) hrel
      exact (not_ggInnerDiagOnLabel_unitary_four hconf) hbad

end CFSG.StandardType.QTwo

end
