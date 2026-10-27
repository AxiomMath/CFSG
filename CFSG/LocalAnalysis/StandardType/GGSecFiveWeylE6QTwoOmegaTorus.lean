module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaTorusPairs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentPlanes
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel

public section

namespace CFSG.StandardType.E6QTwo

open Module QuadraticMap CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
open CFSG.ClassicalGroups.Orthogonal (PolarNondegOn polar_smul_right_eq polar_smul_left_eq
  elementaryGroup elementaryGroup_le_orthogonalGroup)
open CFSG.AGLEmbedding.OmegaMinusCent (MinusSpace minusForm AnisoPair
  nondegenerate_minusForm finrank_minusSpace finrank_le_minusForm
  exists_aniso_pair_of_two_le exists_aniso_pairs_nondeg exists_totSing_of_pairs
  finite_linearEquiv exists_orth_hypPair mem_elementaryGroup_of_pow_three
  exists_pullback_subgroup)

theorem card_eq_of_maximal_minusForm
    {E : Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5)) (hE : IsElemAbelian 3 E)
    (hmax : ∀ F : Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5), E ≤ F →
      F ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) → IsElemAbelian 3 F → F = E) :
    Nat.card E = 3 ^ 5 := by
  classical
  have hQ : (polarBilin (minusForm 5)).Nondegenerate := nondegenerate_minusForm 5
  have hV : finrank (ZMod 2) (MinusSpace 5) = 10 := by
    rw [finrank_minusSpace (by norm_num : 1 ≤ 5)]
  have horth : LinearMap.BilinForm.orthogonal (polarBilin (minusForm 5)) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact hQ.2 x (fun y => hx y (Submodule.mem_top))
  have hEU : E ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) ⊓
      ptw (LinearMap.BilinForm.orthogonal (polarBilin (minusForm 5)) ⊤) := by
    refine le_inf hEO ?_
    rw [horth]
    intro g _
    rw [mem_ptw]
    intro x hx
    rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]
  have hmax' : ∀ F : Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5), E ≤ F →
      F ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) ⊓
        ptw (LinearMap.BilinForm.orthogonal (polarBilin (minusForm 5)) ⊤) →
      IsElemAbelian 3 F → F = E := by
    intro F hEF hF hFea
    exact hmax F hEF (hF.trans inf_le_left) hFea
  obtain ⟨Ps, hPsorth, hPsU, hcard, U', hU'U, hU'nd, hU'dim, hU'perp, hU'noPair⟩ :=
    exists_pairs_of_maximal hQ 10 ⊤ (by rw [finrank_top, hV])
      (nondeg_top (polarBilin_symm (minusForm 5)) hQ) E hEU hE hmax'
  have hfinU' : finrank (ZMod 2) U' ≤ 3 := by
    by_contra h
    push Not at h
    have heven : Even (finrank (ZMod 2) U') := by
      use 5 - Ps.length
      omega
    obtain ⟨c, hc⟩ := heven
    have hc2 : 2 ≤ c := by omega
    have hc' : finrank (ZMod 2) U' = 2 * c := by omega
    obtain ⟨P, ha, hb⟩ := exists_aniso_pair_of_two_le hU'nd hc2 hc'
    exact hU'noPair P ha hb
  have hfinU'0 : finrank (ZMod 2) U' = 0 := by
    by_contra h0
    have heven : Even (finrank (ZMod 2) U') := by
      use 5 - Ps.length
      omega
    obtain ⟨c, hc⟩ := heven
    have hc1 : c = 1 := by omega
    have hdim2 : finrank (ZMod 2) U' = 2 * 1 := by omega
    obtain ⟨Ps', hPs'orth, hPs'U', hcases⟩ := exists_aniso_pairs_nondeg 1 U' hdim2 hU'nd
    rcases hcases with hlen | ⟨hlen, e, heU', he0, heQ, heperp⟩
    · have hpos : 0 < Ps'.length := by omega
      obtain ⟨P, hP⟩ := List.exists_mem_of_length_pos hpos
      exact hU'noPair P (hPs'U' P hP).1 (hPs'U' P hP).2
    · have hPslen : Ps.length = 4 := by omega
      have hspan : ∀ y ∈ Submodule.span (ZMod 2) {e}, (minusForm 5) y = 0 := by
        intro y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rw [QuadraticMap.map_smul, heQ, smul_zero]
      have hperp : ∀ y ∈ Submodule.span (ZMod 2) {e}, ∀ P ∈ Ps,
          polar (minusForm 5) P.a y = 0 ∧ polar (minusForm 5) P.b y = 0 := by
        intro y hy P hP
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
        exact ⟨by rw [polar_smul_right_eq, (hU'perp e heU' P hP).1, mul_zero],
          by rw [polar_smul_right_eq, (hU'perp e heU' P hP).2, mul_zero]⟩
      obtain ⟨T, hT, hdim⟩ :=
        exists_totSing_of_pairs Ps (Submodule.span (ZMod 2) {e}) hspan hPsorth hperp
      have hle := finrank_le_minusForm (m := 5) (T := T) hT
      rw [finrank_span_singleton he0] at hdim
      have hdiv : Ps.length / 2 = 2 := by omega
      rw [hdiv] at hdim
      omega
  have hPslen : Ps.length = 5 := by omega
  rw [hcard, hPslen]

theorem exists_le_elemAbelian_card_of_pomegaMinus_five {X : Type} [Group X] [Finite X]
    (hX : StatedClassicalModel X .POmegaMinus 5 2 1) {E : Subgroup X} (hE : IsElemAbelian 3 E) :
    ∃ T : Subgroup X, E ≤ T ∧ IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 5 := by
  classical
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.exists_mulEquiv_zmod_of_lieModel
      (Or.inl ⟨by decide, hX⟩ : CFSG.Blueprint.LieModel X .POmegaMinus 5 2 1)
  let f : X →* (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5) :=
    (elementaryGroup (minusForm 5)).subtype.comp e.toMonoidHom
  have hf_inj : Function.Injective f := by
    intro a b h
    exact e.injective (Subtype.ext h)
  let E₀ : Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5) := E.map f
  have hE₀ea : IsElemAbelian 3 E₀ := IsElemAbelian.map hE f
  have hE₀_elem : E₀ ≤ elementaryGroup (minusForm 5) := by
    rintro _ ⟨g, -, rfl⟩
    exact (e g).2
  have hE₀O : E₀ ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) :=
    hE₀_elem.trans (elementaryGroup_le_orthogonalGroup (minusForm 5))
  let S : Set (Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5)) :=
    {F | E₀ ≤ F ∧ F ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) ∧ IsElemAbelian 3 F}
  have hSne : S.Nonempty := ⟨E₀, le_rfl, hE₀O, hE₀ea⟩
  obtain ⟨F, hFS, hFmax_card⟩ :=
    Set.exists_max_image S (fun F => Nat.card F) (Set.toFinite S) hSne
  obtain ⟨hE₀F, hFO, hFea⟩ := hFS
  have hFmax : ∀ F' : Subgroup (MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5), F ≤ F' →
      F' ≤ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) → IsElemAbelian 3 F' →
      F' = F := by
    intro F' hFF' hF'O hF'ea
    have hF'S : F' ∈ S := ⟨le_trans hE₀F hFF', hF'O, hF'ea⟩
    exact (Subgroup.eq_of_le_of_card_ge hFF' (hFmax_card F' hF'S)).symm
  have hFcard : Nat.card F = 3 ^ 5 :=
    card_eq_of_maximal_minusForm hFO hFea hFmax
  have hF_elem : F ≤ elementaryGroup (minusForm 5) := by
    intro g hg
    obtain ⟨P, P', hPP'⟩ := exists_orth_hypPair (m := 5) (by norm_num)
    exact mem_elementaryGroup_of_pow_three (nondegenerate_minusForm 5)
      (by rw [finrank_minusSpace (by norm_num : 1 ≤ 5)]; norm_num) hPP' (hFO hg) (hFea.2 g hg)
  obtain ⟨T, hTmem, hTcard⟩ := exists_pullback_subgroup e hF_elem
  refine ⟨T, ?_, ?_, ?_⟩
  · intro g hg
    rw [hTmem g]
    exact hE₀F (Subgroup.mem_map_of_mem f hg)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      apply hf_inj
      have ha : f a.1 ∈ F := (hTmem a.1).1 a.2
      have hb : f b.1 ∈ F := (hTmem b.1).1 b.2
      letI : IsMulCommutative F := hFea.1
      have hc : (⟨f a.1, ha⟩ : F) * ⟨f b.1, hb⟩ = ⟨f b.1, hb⟩ * ⟨f a.1, ha⟩ :=
        mul_comm' _ _
      simpa [map_mul] using congrArg Subtype.val hc
    · apply hf_inj
      have hyF : f y ∈ F := (hTmem y).1 hy
      simpa [map_pow] using hFea.2 (f y) hyF
  · rw [hTcard, hFcard]

end CFSG.StandardType.E6QTwo

end
