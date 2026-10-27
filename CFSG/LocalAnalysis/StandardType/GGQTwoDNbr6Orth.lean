module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrOrth
public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section


theorem qtwoDNbr6_orth (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) {m : ℕ} (hcard : Nat.card ↥Bs = 3 ^ m)
    (hm : 6 ≤ m ∨ 3 ≤ m ∧ B < Bs)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2)
    (hmark : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) 3 Bs X) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs X, Nat.card Φ.F = 2 ∧ 4 ≤ Φ.r ∧ (Φ.r = 4 → B < Bs) ∧
      Subgroup.center ↥X = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hperf : commutator ↥X = ⊤ := hmark.1
  haveI : Group.IsPerfect ↥X := Group.IsPerfect.mk hperf
  have hmarkK : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hlt4 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) →
      ((ggRowP_EOmP 3 lab ∨ ggRowP_EOmM 3 lab) ∧ lab.n = 1) → lab.rank = 4 → B < Bs := by
    intro lab hΛ hhas ⟨hrow, hn⟩ h4
    refine hm.elim (fun hm => ?_) fun h => h.2
    have hrank4 : 4 ≤ lab.rank ∧ ((lab.tag = .D ∧ Even lab.rank) ∨
        (lab.tag = .twD ∧ Odd lab.rank)) ∧ 3 ∣ 2 ^ lab.n + 1 := by
      rcases hrow with ⟨h, h4', he, hd⟩ | ⟨h, h5, ho, hd⟩
      · exact ⟨h4', Or.inl ⟨h, he⟩, hd⟩
      · exact ⟨by omega, Or.inr ⟨h, ho⟩, hd⟩
    have hle := qtwoDNbr_card_le_orth (p := 3) hRig (by norm_num) hBs hSC hmarkK hperf hΛ hhas
      hrank4.1 hrank4.2.2 hrank4.2.1
    rw [hcard, h4] at hle
    refine lt_of_le_of_ne hcfg.2.1.1 fun hBeq => ?_
    have h3 := ggNSPosPD_routeCfg_cent_K Nat.prime_three hnbr
    rw [hBeq] at h3
    have h6 : 3 ^ 6 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hZ : Subgroup.center ↥X = ⊥ := by
    have hsplit : GGInnerDiagOnLabel (fun p lab =>
        (ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) ∨
        ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1 ∧ 5 ≤ lab.rank)) 3 Bs X :=
      hmark.mono' fun lab ⟨hrow, hn⟩ => by
        rcases hrow with hr | hr
        · by_cases h4 : lab.rank = 4
          · exact Or.inl ⟨hr, hn, h4⟩
          · refine Or.inr ⟨Or.inl hr, hn, ?_⟩
            obtain ⟨-, h4', -, -⟩ := hr
            omega
        · refine Or.inr ⟨Or.inr hr, hn, ?_⟩
          obtain ⟨-, h5, -, -⟩ := hr
          exact h5
    rcases GGInnerDiagOnLabel.elim_or hsplit with hD4 | h5
    · obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨hrow4, hn, hr4⟩, -, -⟩⟩ :=
        largeEvenMarking_exists_hasLabel hD4
      exact hcfg.center_eq_bot_of_D4two_of_lt (hlt4 lab hΛ hhas ⟨Or.inl hrow4, hn⟩ hr4) hD4
    · obtain ⟨lab, -, hhas, -, -, -, -, -, ⟨⟨hrow, hn, h5'⟩, -, -⟩⟩ :=
        largeEvenMarking_exists_hasLabel h5
      refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
      rcases hrow with ⟨ht, -, -, -⟩ | ⟨ht, -, -, -⟩
      · exact Or.inl ⟨ht, h5'⟩
      · exact Or.inr ⟨ht, by omega⟩
  have hact : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
    intro hN
    by_contra hall
    push Not at hall
    have hle : Bs ≤ Subgroup.centralizer (X : Set G) := fun b hb =>
      (ggGamma_eq_one_iff X hN ⟨b, hb⟩).mp (hall ⟨b, hb⟩)
    have h1 : Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
      Subgroup.card_le_of_le (le_inf le_rfl hle)
    have h2 : 3 ^ 3 ≤ 3 ^ m :=
      Nat.pow_le_pow_right (by norm_num) (hm.elim (fun h => by omega) fun h => h.1)
    rw [hcard] at h1
    omega
  have hmarkP : GGInnerDiagOnLabel (fun p lab =>
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) ∧ (lab.rank = 4 → B < Bs)) 3 Bs X :=
    GGInnerDiagOnLabel.mono_label_of_hasLabel
      (fun lab hΛ hhas hrow => ⟨hrow, hlt4 lab hΛ hhas hrow⟩) hmark
  obtain ⟨lab, hP, hhas, Φ, hr, hF, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig (by norm_num) hBs hSC
      (P := fun p lab => ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) ∧
        (lab.rank = 4 → B < Bs))
      (fun lab hl => hl.1.1) hmarkP (fun _ _ _ => hZ) hact
  refine ⟨Φ, ?_, ?_, ?_, hZ⟩
  · rw [hF, hP.1.2, pow_one]
  · rw [hr]
    rcases hP.1.1 with ⟨-, h4, -, -⟩ | ⟨-, h5, -, -⟩ <;> omega
  · intro h4
    exact hP.2 (hr.symm.trans h4)

end

end CFSG.StandardType.QTwo

end
