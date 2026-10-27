module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Cases
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512CalL1Torus
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrSect
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Open (WreathedTwoGroup)

theorem sylow_wreathed_of_lieModel_l3Eps {E : Type} [Group E] [Finite E] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : (LieModel E .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel E .PSU 3 p f ∧ p ^ f % 4 = 3))
    (S : Sylow 2 E) : ∃ m : ℕ, Nonempty (↥S ≃* WreathedTwoGroup m) := by
  rcases hE with ⟨h, hq⟩ | ⟨h, hq⟩
  · obtain ⟨⟨-, hf, -⟩, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
    obtain ⟨m, -, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_wr hp hp2
      (Or.inl ⟨rfl, F, iF, hfin, hF, he⟩) hq (Nat.one_lt_pow (by omega) hp.one_lt) S
    exact ⟨m, hS⟩
  · obtain ⟨-, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
    obtain ⟨m, -, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr hp hp2
      (Or.inr ⟨rfl, F, iF, hfin, hF, he⟩) hq S
    exact ⟨m, hS⟩

theorem isCalL1_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') (h : IsCalL1 X) :
    IsCalL1 X' := by
  obtain ⟨n, hn, h1, h | h | h⟩ := h
  · exact ⟨n, hn, h1, .inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)⟩
  · exact ⟨n, hn, h1, .inr (.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))⟩
  · exact ⟨n, hn, h1, .inr (.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h))⟩

private theorem l3Wr_relIndex_subgroup {E : Type} [Group E]
    (h1 : ∀ P : Subgroup E, IsPGroup 2 P → ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2)
    (X : Subgroup E) (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2 := by
  obtain ⟨A, hAP, hAc, hAi⟩ := h1 (P.map X.subtype) (hP.map X.subtype)
  refine ⟨A.comap X.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.comap_mono hAP).trans
      (Subgroup.comap_map_eq_self_of_injective X.subtype_injective P).le
  · exact Subgroup.comap_injective_isMulCommutative A X.subtype_injective
  · rw [Subgroup.relIndex_comap]
    exact hAi

private theorem l3Wr_closure_two_subgroup {E : Type} [Group E]
    (h2 : ∀ A : Subgroup E, IsPGroup 2 A → IsMulCommutative A →
      ∃ s : Finset E, s.card ≤ 2 ∧ Subgroup.closure (s : Set E) = A)
    (X : Subgroup E) (A : Subgroup X) (hA : IsPGroup 2 A) (hAc : IsMulCommutative A) :
    ∃ s : Finset X, s.card ≤ 2 ∧ Subgroup.closure (s : Set X) = A := by
  obtain ⟨s, hs, hcl⟩ := h2 (A.map X.subtype) (hA.map X.subtype) inferInstance
  refine ⟨s.preimage X.subtype X.subtype_injective.injOn, ?_, ?_⟩
  · refine le_trans (Finset.card_le_card_of_injOn X.subtype (fun a ha => ?_)
      X.subtype_injective.injOn) hs
    simpa using ha
  · apply Subgroup.map_injective X.subtype_injective
    have hsub : (s : Set E) ⊆ Set.range X.subtype := by
      intro y hy
      have : y ∈ A.map X.subtype := hcl ▸ Subgroup.subset_closure hy
      obtain ⟨a, -, rfl⟩ := this
      exact ⟨a, rfl⟩
    rw [MonoidHom.map_closure, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
      Set.inter_eq_left.mpr hsub, hcl]

theorem l3EpsWreathedNoCalL1_holds : L3EpsWreathedNoCalL1 := by
  intro E _ _ p f hp hp2 hE X
  rintro ⟨L, _, hcf, hL⟩
  have : Finite L := isCompositionFactor_finite hcf
  obtain ⟨N, M, hNM, -, -, -, -, ⟨e⟩⟩ := hcf
  have := hNM
  have hW := sylow_wreathed_of_lieModel_l3Eps hp hp2 hE
  obtain ⟨V, hVc, hV2, hV8, hc⟩ :=
    exists_elemAbelian_irred_of_isCalL1 (isCalL1_of_mulEquiv e.symm hL)
  exact false_of_section_elemAbelian_of_wreathLike
    (l3Wr_relIndex_subgroup (exists_isCommutative_relIndex_le_two_of_sylow_wreathed hW) X)
    (l3Wr_closure_two_subgroup (isCommutative_closure_two_of_sylow_wreathed hW) X)
    M (N.subgroupOf M) V hVc hV2 hV8 hc

end CFSG.LocalAnalysis.WeakClosure81

end
