module

public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.Lanes
import CFSG.RankThree.GF2n.Smith81.Lin22
import CFSG.RankThree.GF2n.Smith81.LinOuterCount
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

@[expose] def LinRootClassStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → StrothConclusion M Q Z B → TypeE6 M Q Z B n →
    LinSetup M Q Z B n V₁ V₂ → 4 ≤ n → Lin3Facts M Q Z B n V₁ V₂ → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g} ∧
      ∀ w : G, IsConj z w → ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹

@[expose] def LinInspectStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 4 ≤ n → Lin3Facts M Q Z B n V₁ V₂ →
    ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g} →
    (∀ w : G, IsConj z w → ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹) →
    Timmesfeld.Outcome ↥(Subgroup.normalClosure ({z} : Set G)) →
      ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        CFSG.Blueprint.LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .PSL (n + 2) 2 f

@[expose] def LinTIIdentifyStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → StrothConclusion M Q Z B → TypeE6 M Q Z B n →
      LinSetup M Q Z B n V₁ V₂ → (n = 2 ∨ n = 3) → Lin3Facts M Q Z B n V₁ V₂ →
        ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f

@[expose] def LaneLinStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Smith1981Below (Nat.card G) →
    ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
      ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
        StrothConclusion M Q Z B → SmithLaneLin M Q Z B

@[expose] def TiLinearD2Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Smith1981Below (Nat.card G) →
    ∀ (M Q Z B : Subgroup G), StrothHyp M Q Z → (∃ g : G, B = conjSubgroup g Z) → B ≤ Q →
      B ≠ Z → CaseD2 M Q Z B → ¬ NoA2 Q Z (LB M Q B) → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        CFSG.Blueprint.LieModel (FStar G) .PSL 4 2 f ∧ OuterOnFStar G

section Assembly

variable [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
  {V₁ V₂ : Subgroup G}

theorem exists_ne_one_mem_Z (H : StrothHyp M Q Z) : ∃ z ∈ Z, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h4 := H.q4
  have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
  rw [this, Subgroup.card_bot] at h4
  omega

theorem lin_identify (hOutcome : TimmesfeldOutcomeStatement) (hRoot : LinRootClassStatement)
    (hInspect : LinInspectStatement) (hTI : LinTIIdentifyStatement)
    (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B) (hC : StrothConclusion M Q Z B)
    (hE6 : TypeE6 M Q Z B n) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 2 ≤ n)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f := by
  rcases lt_or_ge n 4 with h4 | h4
  · exact hTI G M Q Z B n V₁ V₂ hb hc hC hE6 hS (by omega) h3
  · obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z hc.hyp
    obtain ⟨hroot, hconj⟩ := hRoot G M Q Z B n V₁ V₂ hb hc hC hE6 hS h4 h3 z hz hz1
    have hnd : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4 := by
      obtain ⟨d, hd, e, he, h4'⟩ := exists_orderOf_mul_eq_four hc.hyp hz hz1
      exact ⟨d, e, hd, he, h4'⟩
    have hodd : pPrimeCore 2 G = ⊥ := hc.hyp.toTim81Hyp.pPrimeCore_eq_bot hc.hyp.q4
    have hout := outcome_normalClosure hOutcome hroot hconj hodd hc.hyp.o2 hnd
    obtain ⟨f, hf, hL⟩ := hInspect G M Q Z B n V₁ V₂ hc hS h4 h3 z hz hz1 hroot hconj hout
    refine ⟨f, hf, ?_⟩
    obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure hc.hyp hz hz1
    exact CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL

theorem lin_conclusion (hOutcome : TimmesfeldOutcomeStatement) (hRoot : LinRootClassStatement)
    (hInspect : LinInspectStatement) (hTI : LinTIIdentifyStatement)
    (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B) (hC : StrothConclusion M Q Z B)
    (hE6 : TypeE6 M Q Z B n) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 2 ≤ n)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f ∧
      OuterOnFStar G := by
  obtain ⟨f, hf, hL⟩ := lin_identify hOutcome hRoot hInspect hTI hb hc hC hE6 hS hn h3
  exact ⟨f, hf, hL, outerOnFStar_of_lieModel_psl hc (by omega) h3.h31 hf hL⟩

theorem smithLaneLin_of_inputs (hOutcome : TimmesfeldOutcomeStatement) (h3 : Lin3Statement)
    (hRoot : LinRootClassStatement) (hInspect : LinInspectStatement)
    (hTI : LinTIIdentifyStatement) : LaneLinStep := by
  intro G _ _ hb M Q Z hH B hB hBQ hBZ hC hnTI n hE6
  have hc : Ctx M Q Z B := ⟨hH, hB, hBQ, hBZ⟩
  have hn : 2 ≤ n := CaseE6.two_le hc hnTI hE6
  obtain ⟨V₁, V₂, hS⟩ := hE6.exists_linSetup
  exact lin_conclusion hOutcome hRoot hInspect hTI hb hc hC (Or.inl ⟨hnTI, hE6⟩) hS hn
    (h3 G M Q Z B n V₁ V₂ hb hc hS hn)

theorem tiLinearD2_of_inputs (hOutcome : TimmesfeldOutcomeStatement) (h3 : Lin3Statement)
    (hRoot : LinRootClassStatement) (hInspect : LinInspectStatement)
    (hTI : LinTIIdentifyStatement) : TiLinearD2Step := by
  intro G _ _ hb M Q Z B hH hB hBQ hBZ hD2 hno
  have hc : Ctx M Q Z B := ⟨hH, hB, hBQ, hBZ⟩
  obtain ⟨V₁, V₂, hS⟩ := lin22Statement_holds G M Q Z B hc hD2 hno
  exact lin_conclusion hOutcome hRoot hInspect hTI hb hc
    ⟨Or.inr (Or.inl hD2), stroth_frobClause hH⟩ (Or.inr ⟨rfl, hD2, hno⟩) hS le_rfl
    (h3 G M Q Z B 2 V₁ V₂ hb hc hS le_rfl)

end Assembly

end CFSG.RankThree.GF2n.Smith81
