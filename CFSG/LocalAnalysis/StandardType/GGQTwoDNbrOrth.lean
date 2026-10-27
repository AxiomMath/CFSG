module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrOrthRank
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section


theorem qtwoDNbr_orth (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {X : Subgroup G} {m : ℕ}
    (hcard : Nat.card ↥Bs = 3 ^ m) (hm : 7 ≤ m)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2)
    (hmark : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) 3 Bs X) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs X, Nat.card Φ.F = 2 ∧ 5 ≤ Φ.r ∧
      Subgroup.center ↥X = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hperf : commutator ↥X = ⊤ := hmark.1
  haveI : Group.IsPerfect ↥X := Group.IsPerfect.mk hperf
  have hmarkK : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hmark5 : GGInnerDiagOnLabel (fun p lab =>
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) ∧ 5 ≤ lab.rank) 3 Bs X := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ hhas hrow => ⟨hrow, ?_⟩) hmark
    obtain ⟨hrow', hn⟩ := hrow
    have hrank4 : 4 ≤ lab.rank ∧ ((lab.tag = .D ∧ Even lab.rank) ∨
        (lab.tag = .twD ∧ Odd lab.rank)) ∧ 3 ∣ 2 ^ lab.n + 1 := by
      rcases hrow' with ⟨h, h4, he, hd⟩ | ⟨h, h5, ho, hd⟩
      · exact ⟨h4, Or.inl ⟨h, he⟩, hd⟩
      · exact ⟨by omega, Or.inr ⟨h, ho⟩, hd⟩
    have hle := qtwoDNbr_card_le_orth (p := 3) hRig (by norm_num) hBs hSC hmarkK hperf hΛ hhas
      hrank4.1 hrank4.2.2 hrank4.2.1
    rw [hcard] at hle
    by_contra hlt
    have hlt' : lab.rank ≤ 4 := by omega
    have h9 : 3 ^ m ≤ 3 ^ 2 * 3 ^ 4 :=
      hle.trans (Nat.mul_le_mul hcent (Nat.pow_le_pow_right (by norm_num) hlt'))
    have h6 : 3 ^ 7 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hZK : ∀ lab : LargeEvenLabel, (((ggRowP_EOmP 3 lab ∨ ggRowP_EOmM 3 lab) ∧ lab.n = 1) ∧
      5 ≤ lab.rank) → GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → Subgroup.center ↥X = ⊥ := by
    intro lab ⟨⟨hrow, hn⟩, h5⟩ hhas
    refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
    rcases hrow with ⟨ht, -, -, -⟩ | ⟨ht, -, -, -⟩
    · exact Or.inl ⟨ht, h5⟩
    · exact Or.inr ⟨ht, by omega⟩
  have hact : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
    intro hN
    by_contra hall
    push Not at hall
    have hle : Bs ≤ Subgroup.centralizer (X : Set G) := fun b hb =>
      (ggGamma_eq_one_iff X hN ⟨b, hb⟩).mp (hall ⟨b, hb⟩)
    have h1 : Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
      Subgroup.card_le_of_le (le_inf le_rfl hle)
    have h2 : 3 ^ 7 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hcard] at h1
    omega
  obtain ⟨lab, hP, hhas, Φ, hr, hF, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig (by norm_num) hBs hSC
      (P := fun p lab => ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) ∧ 5 ≤ lab.rank)
      (fun lab hl => hl.1.1) hmark5 hZK hact
  refine ⟨Φ, ?_, ?_, hZK lab hP hhas⟩
  · rw [hF, hP.1.2, pow_one]
  · rw [hr]
    exact hP.2

end

end CFSG.StandardType.QTwo

end
