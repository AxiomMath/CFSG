module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.StronglyEmbedded.BenderRootModel

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open CFSG.StronglyEmbedded.BenderCentre (benderRoot_pCoreOf_normalizer
  eq_sylowCenter_or_eq_of_normalized eq_conj_sylow eq_conj_sylowCenter
  not_mem_normalizer_of_not_commute sylow_sup_zpowers_eq_top mul_self_mem_sylowCenter)

variable {K : Type} [Group K] [Finite K] {A : Subgroup K}

theorem benderRoot_irrModel
    (h : BenderRoot K A) : RootIrrModel K A := by
  obtain ⟨hK, S, rfl⟩ := h
  obtain ⟨hN, hO⟩ := benderRoot_pCoreOf_normalizer (S := S) hK rfl
  intro R hAR hRO hR
  rw [hO] at hRO ⊢
  rw [hN] at hR
  exact eq_sylowCenter_or_eq_of_normalized hK S hAR hRO hR

theorem benderRoot_innerModel
    (h : BenderRoot K A) : RootInnerModel K A := by
  obtain ⟨hK, S, rfl⟩ := h
  obtain ⟨hN, -⟩ := benderRoot_pCoreOf_normalizer (S := S) hK rfl
  intro α hα hb
  rw [hN] at hb
  exact eq_conj_sylowCenter hK S α hα hb

theorem benderRoot_s2Model (h : BenderRoot K A) :
    RootS2Model K A := by
  obtain ⟨hK, S, rfl⟩ := h
  obtain ⟨-, hO⟩ := benderRoot_pCoreOf_normalizer (S := S) hK rfl
  intro α hα hb
  rw [hO] at hb ⊢
  exact eq_conj_sylow hK S α hα hb

theorem benderRoot_s1Model
    (h : BenderRoot K A) : RootS1Model K A := by
  obtain ⟨hK, S, rfl⟩ := h
  obtain ⟨-, hO⟩ := benderRoot_pCoreOf_normalizer (S := S) hK rfl
  intro g hg a ha ha1
  rw [hO]
  exact sylow_sup_zpowers_eq_top hK S (not_mem_normalizer_of_not_commute S hg) ha ha1

theorem rootIrrAll_of_classical
    (h : ClassicalRootIrrStatement) : RootIrrAll := by
  intro K _ _ A hA
  rcases hA with hB | hC
  · exact benderRoot_irrModel hB
  · exact h K A hC

theorem rootInnerAll_of_classical
    (h : ClassicalRootInnerStatement) : RootInnerAll := by
  intro K _ _ A hA
  rcases hA with hB | hC
  · exact benderRoot_innerModel hB
  · exact h K A hC

theorem rootS2All_of_classical (h : ClassicalRootS2Statement) :
    RootS2All := by
  intro K _ _ A hA
  rcases hA with hB | hC
  · exact benderRoot_s2Model hB
  · exact h K A hC

theorem rootS1All_of_classical
    (h : ClassicalRootS1Statement) : RootS1All := by
  intro K _ _ A hA
  rcases hA with hB | hC
  · exact benderRoot_s1Model hB
  · exact h K A hC

end CFSG.RankThree.GF2n.Tim79a
