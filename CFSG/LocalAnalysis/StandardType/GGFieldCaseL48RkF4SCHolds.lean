module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Facts
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.SeitzReduction.F4Pilot
  TableBF4TwoInputs

private def SC3 {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  ∀ g : G, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E

private theorem sc3_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {E : Subgroup G}
    (hE : SC3 E) : SC3 (E.map φ.toMonoidHom) := by
  intro h h3 hcomm
  set g : G := φ.symm h with hg
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← map_pow, h3, map_one]
  have hgc : ∀ a ∈ E, g * a = a * g := by
    intro a ha
    apply φ.injective
    rw [map_mul, map_mul]
    have hφa : φ a ∈ E.map φ.toMonoidHom := ⟨a, ha, rfl⟩
    have hh := hcomm (φ a) hφa
    simpa [hg] using hh
  have hgE : g ∈ E := hE g hg3 hgc
  exact ⟨g, hgE, by simp [hg]⟩

theorem ggF4TwoSCNoTwoLocal_holds :
    GGF4TwoSCNoTwoLocal := by
  intro R _ _ hR E hE hcard hsc S hS hnorm
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc.exists_mulEquiv_adjointGroup hR
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  by_contra hSne
  have hE' : IsElemAbelian 3 (E.map e.toMonoidHom) := TableB.isElemAbelian_map hE _
  have hcard' : Nat.card (E.map e.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  have hS' : IsPGroup 2 (S.map e.toMonoidHom) := hS.map e.toMonoidHom
  have hS'ne : S.map e.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact hSne
  have hnorm' : E.map e.toMonoidHom ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set (adjointGroup .F4 K)) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hnorm
  have hsc' : SC3 (E.map e.toMonoidHom) := sc3_map e hsc
  have hex : ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      (E.map e.toMonoidHom).map α.toMonoidHom ≤ C3Levi K := by
    obtain ⟨g, hg⟩ := exists_conj_le_C3Levi_or_B3Levi hK hS'ne hS' hnorm'
      (TableB.isPGroup_of_isElemAbelian hE') (by rw [hcard'])
    rcases hg with hC | hB
    · exact ⟨MulAut.conj g, hC⟩
    · refine ⟨(graphAutF4 K).symm * MulAut.conj g, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      change (graphAutF4 K).symm ((MulAut.conj g) a) ∈ C3Levi K
      have h1 : (MulAut.conj g) a ∈ B3Levi K := hB ⟨a, ha, rfl⟩
      rw [← map_graphAutF4_C3Levi] at h1
      obtain ⟨d, hd, hde⟩ := h1
      rw [← hde]
      simpa using hd
  obtain ⟨α, hα⟩ := hex
  have hscα : SC3 ((E.map e.toMonoidHom).map α.toMonoidHom) := sc3_map α hsc'
  have not_sc3 : ∀ {A : Subgroup (adjointGroup .F4 K)}, A ≤ C3Levi K → ¬ SC3 A := by
    intro A hA hscA
    have hX := centralizer_nonsplit (zpowers_nodeElt_le (K := K))
      (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt (K := K) hK)
    have hcomm : ∀ a ∈ A, nodeElt K * a = a * nodeElt K := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.1
        (hX.2.2 (Subgroup.mem_zpowers (nodeElt K))) a (hA ha)).symm
    have hmem : nodeElt K ∈ A := hscA _ (nodeElt_pow_three (K := K)) hcomm
    have h1 : nodeElt K ∈ Subgroup.zpowers (nodeElt K) := Subgroup.mem_zpowers _
    have h2 : nodeElt K ∈ C3Levi K := hA hmem
    exact nodeElt_ne_one (K := K) (Subgroup.disjoint_def.1 hX.2.1 h1 h2)
  exact not_sc3 hα hscα

end CFSG.StandardType

end
