module

public import CFSG.RankThree.GF2n.Smith81.Statement
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.GF2n.Tim78Bridge
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.GF2n.Stroth80.Consumers

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem generalizedFitting_eq_top_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : generalizedFitting G = ⊤ := by
  rw [generalizedFitting.eq_sup, CFSG.WholeGroup.layer_eq_top_of_isSimpleGroup hnonab, sup_top_eq]

theorem not_outerOnFStar (hTop : generalizedFitting G = ⊤) : ¬ OuterOnFStar G := by
  rintro ⟨g, hg⟩
  rw [hTop] at hg
  obtain ⟨x, -, hx⟩ := hg g (Subgroup.mem_top g)
  exact hx rfl

theorem lieModel_of_fstar_eq_top (hTop : generalizedFitting G = ⊤) {t : StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel (FStar G) t n p f) :
    CFSG.Blueprint.LieModel G t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    ((MulEquiv.subgroupCongr hTop).trans Subgroup.topEquiv) h

theorem finish_strothSmith {B : Subgroup G} (h4 : 4 ≤ Nat.card B) {f : ℕ}
    (hf : Nat.card B = 2 ^ f) (hl : StrothSmithList G f) :
    ∃ f : ℕ, Nat.card B = 2 ^ f ∧ 2 ≤ f ∧ StrothSmithList G f := by
  refine ⟨f, hf, ?_, hl⟩
  by_contra hlt
  push Not at hlt
  interval_cases f <;> omega

section Derivation

theorem strothSmith_of_stroth_smith (hStroth : Stroth1980Statement)
    (hSmith : Smith1981Statement) : StrothSmithStatement := by
  intro G _ _ _ hnonab _hK M hM hF B hB hTI h4 hgen hspec
  have hmaxAb := Tim78.maximalAbelian_of_maximalElemAbelian hnonab hM hF hB hTI h4
  have hne : inSubgroup (pCore 2) M ≠ B := by
    intro hQB
    have h1 := hspec.1
    rw [hQB] at h1
    have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hB.prop.2.2.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hbot : ⁅B, B⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm
    rw [hbot] at h1
    have : Nat.card B = 1 := by rw [← h1]; exact Subgroup.card_bot
    omega
  have H79 : Tim79.Hyp79 M B (inSubgroup (pCore 2) M) :=
    ⟨hM, hF, hmaxAb, hB.prop.2.2.2, hTI, h4, rfl, hgen, hne⟩
  have hSH : StrothHyp M (inSubgroup (pCore 2) M) B := stroth_hyp_of_simple hnonab H79
  obtain ⟨g, hgB, hgQ⟩ := H79.exists_opposite
  have hSC := hStroth G M (inSubgroup (pCore 2) M) B hSH (conjSubgroup g B) ⟨g, rfl⟩ hgQ hgB
  have hSM := hSmith G M (inSubgroup (pCore 2) M) B hSH (conjSubgroup g B) ⟨g, rfl⟩ hgQ hgB hSC
  have hTop := generalizedFitting_eq_top_of_simple hnonab
  have hOut := not_outerOnFStar hTop
  obtain ⟨hcases, -⟩ :=
    (strothConclusion_iff_cases M (inSubgroup (pCore 2) M) B (conjSubgroup g B)).mp hSC
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ := hSM
  rcases hcases with ⟨n, hD1⟩ | hD2 | hD3 | ⟨hTI4, ⟨-, t, htL, htQ, hCT, hE⟩ | ⟨n, hVI⟩⟩
  · exact (hOut (s1 n hD1).2).elim
  · obtain ⟨hG2, hL4⟩ := s2 hD2
    obtain ⟨f, hf, hL⟩ := hG2 <| Classical.byContradiction fun hno =>
      (hL4 hno).elim fun _ h => hOut h.2.2
    exact finish_strothSmith h4 hf
      (Or.inr (Or.inr ⟨.G2, by simp, lieModel_of_fstar_eq_top hTop hL⟩))
  · obtain ⟨f, hf, hL⟩ := s3 hD3
    exact finish_strothSmith h4 hf
      (Or.inr (Or.inr ⟨.trialityD4, by simp, lieModel_of_fstar_eq_top hTop hL⟩))
  · have hCtx : CtxD4 M (inSubgroup (pCore 2) M) B (conjSubgroup g B) t :=
      ⟨hTI4, htL, htQ, hCT⟩
    rcases hE with hE1 | ⟨m, hE2⟩ | hE3 | hE4 | hE5
    · rcases (caseE1_iff _ _ _ _ t).mp hE1 with h | h
      · obtain ⟨f, hf, hl⟩ := s4 t hCtx h
        exact finish_strothSmith h4 hf (Or.inr (Or.inl
          ⟨.POmegaPlus, 4, by simp, le_refl _, lieModel_of_fstar_eq_top hTop hl⟩))
      · obtain ⟨f, hf, hl⟩ := s5 t hCtx h
        exact finish_strothSmith h4 hf (Or.inr (Or.inl
          ⟨.POmegaMinus, 4, by simp, le_refl _, lieModel_of_fstar_eq_top hTop hl⟩))
    · rcases (caseE2_iff _ _ _ _ t m).mp hE2 with h | h
      · obtain ⟨f, hf, hl⟩ := s6 t m hCtx h
        exact finish_strothSmith h4 hf (Or.inr (Or.inl
          ⟨.POmegaPlus, m + 2, by simp, hl.admissible.2.2, lieModel_of_fstar_eq_top hTop hl⟩))
      · obtain ⟨f, hf, hl⟩ := s7 t m hCtx h
        exact finish_strothSmith h4 hf (Or.inr (Or.inl
          ⟨.POmegaMinus, m + 2, by simp, hl.admissible.2.2, lieModel_of_fstar_eq_top hTop hl⟩))
    · rcases (caseE3_iff _ _ _ _).mp hE3 with h | h
      · obtain ⟨f, hf, hl⟩ := s8 t hCtx h
        exact finish_strothSmith h4 hf
          (Or.inr (Or.inr ⟨.twistedE6, by simp, lieModel_of_fstar_eq_top hTop hl⟩))
      · obtain ⟨f, hf, hl⟩ := s9 t hCtx h
        exact finish_strothSmith h4 hf
          (Or.inr (Or.inr ⟨.E6, by simp, lieModel_of_fstar_eq_top hTop hl⟩))
    · obtain ⟨f, hf, hl⟩ := s10 t hCtx hE4
      exact finish_strothSmith h4 hf
        (Or.inr (Or.inr ⟨.E7, by simp, lieModel_of_fstar_eq_top hTop hl⟩))
    · obtain ⟨f, hf, hl⟩ := s11 t hCtx hE5
      exact finish_strothSmith h4 hf
        (Or.inr (Or.inr ⟨.E8, by simp, lieModel_of_fstar_eq_top hTop hl⟩))
  · obtain ⟨f, -, -, hO⟩ := s12 hTI4 n hVI
    exact (hOut hO).elim

end Derivation

end CFSG.RankThree.GF2n.Smith81
