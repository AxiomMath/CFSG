module

public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
public import CFSG.LocalAnalysis.StandardType.GGResE6TwoUnitaryK3
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CenterE6
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem not_ggSingularWeylOrder_three_1152 : ¬ ggSingularWeylOrder 3 1152 := by
  rintro (⟨k, -, -, hk⟩ | ⟨-, hk⟩)
  · exact factorial_succ_ne_of_between (a := 6) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hk.symm
  · norm_num at hk

private theorem not_ggLabelIso_e6TwoCompLabelW {lab lab' : LargeEvenLabel}
    (hW : TablePThreeKG.E6TwoCompLabelW lab)
    (h' : (lab'.tag = .twA ∧ lab'.rank = 5) ∨ lab'.tag = .twE6) : ¬ GGLabelIso lab lab' := by
  obtain ⟨t', r', n'⟩ := lab'
  dsimp only at h'
  rcases hW with rfl | rfl | rfl <;> rcases h' with ⟨rfl, rfl⟩ | rfl <;> simp [GGLabelIso]

section E6Two


theorem GGResHyp.false_of_exact2_L_e6Two_three
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 3)] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) : False := by
  obtain ⟨_, _, _, _, _, _, _, θ, -, hlift⟩ := largeEvenMarking_exists_hasLabel
    (largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .E6 ∧ lab.n = 1)
      (fun _ _ h => largeEvenLabelAll_torusLift_E6_two h) (fun _ _ _ _ _ _ hP => hP.1) hM)
  have hm5 : 5 ≤ LargeEvenTwoLocalRank 3 G := by
    have := hH.succ_le_twoLocalRank_of_torusLift_L hM.1 θ hlift
    omega
  have hBs : Nat.card Bs = 3 ^ 5 := (hH.card_Bs_of_e6Two_L hm5 hM).1
  have hcardL : Nat.card ↥(ggAutomizer L Bs) = 1152 :=
    card_ggAutomizer_of_e6Two hH.1 hH.2.2.2.1 hM
  by_cases hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D
  swap
  · obtain ⟨-, hγ⟩ :=
      hH.card_range_gamma_J_of_exactThree_centralizer hBs (hH.card_eq_p3_of_ne hI1)
    have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
      (hH.pow_le_card_gamma_J.trans hγ.le)
    omega
  have hMc : GGInnerDiagOnLabel (fun p lab => S2MathAs51642Interfaces.CenterPrimeTo p lab ∧
      (lab.tag = .E6 ∨ lab.tag = .twE6)) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨ht, hn⟩ := h
        refine ⟨⟨?_, ?_⟩, Or.inl ht⟩
        · simp [S2MathAs51642Interfaces.SmallDerived, ht]
        · simp [ht, hn]) hM
  have hJ : GGInnerDiagOn Bs J := q1CenterPrimeE6TwE6_holds G 3 B Bs x L D J hH.1 hMc
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) 3 hJ).mono_label (fun _ _ => trivial)
  obtain ⟨labJ, hΛJ, hhasJ, hW, -⟩ := hH.exists_e6_two_original_J_label_table hM
  rcases hH.fix_mem_centralizer_J_or_low_of_tcj (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm5 hJlab with
    hfwd | ⟨-, hlow⟩ | ⟨-, hlow⟩
  ·
    have hfixJ : ∀ b : ↥Bs,
        (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ (b : G) ∈ Subgroup.centralizer (J : Set G) := by
      intro b
      refine ⟨hfwd b, fun hb φ hφ => ?_⟩
      apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b) _ hφ
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_iff] at hb
      exact hb j hj
    have hsing := GGResLeviDatumCard.singular_card
      (ggResExact2_typed_dichotomy_L_of_fixed hH hI1 hfixJ hD)
    rw [hcardL] at hsing
    exact not_ggSingularWeylOrder_three_1152 hsing
  ·
    obtain ⟨labJ', hΛJ', hhasJ', _, _, _, _, _, ⟨-, htag, hrank, -⟩, -⟩ :=
      largeEvenMarking_exists_hasLabel hlow
    exact not_ggLabelIso_e6TwoCompLabelW hW (Or.inl ⟨htag, hrank⟩)
      (ggLabelRigidInput_holds labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ')
  ·
    obtain ⟨labJ', hΛJ', hhasJ', _, _, _, _, _, ⟨-, htag, -⟩, -⟩ :=
      largeEvenMarking_exists_hasLabel hlow
    exact not_ggLabelIso_e6TwoCompLabelW hW (Or.inr htag)
      (ggLabelRigidInput_holds labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ')

theorem ggResMultiNodeRestTwoCellInput_e6_qTwo_three :
    GGResMultiNodeRestTwoCellInput (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ lab.n = 1) := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hL hD
  obtain ⟨_, _, _, _, _, _, _, _, ⟨-, hp3, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hL
  subst hp3
  exact hH.false_of_exact2_L_e6Two_three
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.2⟩) hL) hD

end E6Two

end CFSG.StandardType

end
