module

public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic
public import CFSG.Adapters.TauCetiExceptional.FrameworkTransport
public import CFSG.Adapters.TauCetiExceptional.GeckE8
public import CFSG.Adapters.TauCetiExceptional.GeckF4
public import CFSG.Adapters.TauCetiExceptional.GeckG2
public import CFSG.LieType.Chevalley.LangActualInvolutionReduction
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.TauCetiBridge TauCeti
open scoped MatrixGroups

theorem rootSL2_injective {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    Function.Injective (rootSL2 τ K β) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    exact (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K hβ).1
  · exact ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.2.1 h2).1

theorem exists_commuting_rootSL2 {K : Type} [Field K] (τ : Tag) {n : ℕ}
    (α : Fin n → Fin τ.rank → ℤ)
    (h : (∀ i, RootOps.isRootB τ (α i) = true) ∧
      ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB τ (α i + α j) = false ∧
        RootOps.isRootB τ (α i - α j) = false) :
    ∃ ι : Fin n → (SL2 K →* adjointGroup τ K), (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (h.1 i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  refine ⟨fun i => (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
    (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1, fun i A B hAB => ?_,
    fun i j hij A B => ?_⟩
  · exact rootSL2_injective (hroot i) (congrArg Subtype.val hAB)
  · obtain ⟨h0, hp, hm⟩ := h.2 i j hij
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot i) (hroot j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)

section Embedding

variable (d : ValidLieTypeIndex) {τ : Tag} (M : GeckMatch τ d.dynkinType d.dynkinType_valid)

@[expose] noncomputable def geckMatrixHom :
    ↥(adjointGroup τ d.fixedField) →*
      Matrix.GeneralLinearGroup (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure :=
  (M.toGeck d.Closure).toMonoidHom.comp
    ((baseChangeGL d.fixedField.subtype).comp (adjointGroup τ d.fixedField).subtype)

theorem geckMatrixHom_injective : Function.Injective (geckMatrixHom d M) :=
  (M.toGeck d.Closure).injective.comp
    ((baseChangeGL_injective d.fixedField.subtype).comp Subtype.val_injective)

theorem geckMatrixHom_mem_geckPoints (g : ↥(adjointGroup τ d.fixedField)) :
    geckMatrixHom d M g ∈ d.geckPoints :=
  M.map_toGeck_adjointGroup_le_geckPoints d.Closure
    ⟨baseChangeGL d.fixedField.subtype g,
      map_baseChangeGL_adjointGroup_le d.fixedField.subtype ⟨g, g.2, rfl⟩, rfl⟩

theorem geckMatrixHom_apply_mem (g : ↥(adjointGroup τ d.fixedField))
    (r s : Fin (d.dynkinType.geckDim d.dynkinType_valid)) :
    ((geckMatrixHom d M g : Matrix.GeneralLinearGroup _ d.Closure) :
      Matrix (Fin (d.dynkinType.geckDim d.dynkinType_valid))
        (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) r s ∈ d.fixedField := by
  change ((M.toGeck d.Closure (baseChangeGL d.fixedField.subtype g) :
      Matrix.GeneralLinearGroup _ d.Closure) : Matrix _ _ d.Closure) r s ∈ d.fixedField
  rw [GeckMatch.toGeck_apply, baseChangeGL_apply_single, Finsupp.mapRange_apply]
  refine d.fixedField.mul_mem (d.fixedField.mul_mem (d.fixedField.intCast_mem _) ?_)
    (d.fixedField.intCast_mem _)
  exact Subtype.prop _

@[expose] noncomputable def geckEmbed :
    ↥(adjointGroup τ d.fixedField) →* ↥(fixedSubgroup d.geckFrobenius) :=
  ((geckMatrixHom d M).codRestrict d.geckPoints (geckMatrixHom_mem_geckPoints d M)).codRestrict
    (fixedSubgroup d.geckFrobenius) fun g =>
      (ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff d _).2
        (geckMatrixHom_apply_mem d M g)

theorem geckEmbed_injective : Function.Injective (geckEmbed d M) := fun _ _ h =>
  geckMatrixHom_injective d M (congrArg Subtype.val (congrArg Subtype.val h))

include M

theorem four_le_twoLocalOddRank_geck_four
    [Finite (FixedPointCandidate d.geckFrobenius)]
    (hC : commutator ↥(adjointGroup τ d.fixedField) = ⊤) (hq : d.fieldOrder ≠ 2)
    (ι : Fin 4 → (SL2 d.fixedField →* adjointGroup τ d.fixedField))
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 d.fixedField, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius) := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  have hinj := toQuot_injective (geckEmbed_injective d M) hC center_adjointGroup_eq_bot
  refine four_le_twoLocalOddRank_of_four_commuting_SL2 (K := d.fixedField) ?_
    (fun i => (toQuot (geckEmbed d M) hC).comp (ι i)) (fun i => hinj.comp (hι i))
    (fun i j hij A B => ?_)
  · rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
    exact hq
  · simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem four_le_twoLocalOddRank_geck_five
    [Finite (FixedPointCandidate d.geckFrobenius)]
    (hC : commutator ↥(adjointGroup τ d.fixedField) = ⊤) (h2 : ringChar d.fixedField = 2)
    (ι : Fin 5 → (SL2 d.fixedField →* adjointGroup τ d.fixedField))
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 d.fixedField, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius) := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  have hinj := toQuot_injective (geckEmbed_injective d M) hC center_adjointGroup_eq_bot
  refine four_le_twoLocalOddRank_of_five_commuting_SL2 (K := d.fixedField) h2
    (fun i => (toQuot (geckEmbed d M) hC).comp (ι i)) (fun i => hinj.comp (hι i))
    (fun i j hij A B => ?_)
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem four_le_twoLocalOddRank_geck_two
    [Finite (FixedPointCandidate d.geckFrobenius)]
    (hC : commutator ↥(adjointGroup τ d.fixedField) = ⊤) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 2 ≤ f) (hq : d.fieldOrder = p ^ f)
    (ι : Fin 2 → (SL2 d.fixedField →* adjointGroup τ d.fixedField))
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 d.fixedField, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius) := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  have hinj := toQuot_injective (geckEmbed_injective d M) hC center_adjointGroup_eq_bot
  refine four_le_twoLocalOddRank_of_two_commuting_SL2 (K := d.fixedField) hp hp2 hf ?_
    (fun i => (toQuot (geckEmbed d M) hC).comp (ι i)) (fun i => hinj.comp (hι i))
    (fun i j hij A B => ?_)
  · rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
    exact hq
  · simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

end Embedding

theorem fintype_card_fixedField (d : ValidLieTypeIndex) [Fintype d.fixedField] :
    Fintype.card d.fixedField = d.fieldOrder := by
  rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]

theorem ringChar_fixedField_eq_two {d : ValidLieTypeIndex} (h : d.fieldOrder = 2) :
    ringChar d.fixedField = 2 := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  refine (FiniteField.even_card_iff_char_two (F := d.fixedField)).2 ?_
  rw [fintype_card_fixedField, h]

theorem four_le_twoLocalOddRank_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    [Finite (CFSGIndex.lie ⟨.E8 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  have : Finite (FixedPointCandidate d.geckFrobenius) := ‹Finite (CFSGIndex.lie d).Group›
  change 4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius)
  have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
    single_edge_perfect .E8 d.fixedField (by simp)
  by_cases hq : d.fieldOrder = 2
  · obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
      ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2]] (by decide +kernel)
    exact four_le_twoLocalOddRank_geck_five d geckMatchE8 hC (ringChar_fixedField_eq_two hq) ι
      hι hcomm
  · obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
      ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 1, 1, 0, 0, 0, 0]] (by decide +kernel)
    exact four_le_twoLocalOddRank_geck_four d geckMatchE8 hC hq ι hι hcomm

theorem four_le_twoLocalOddRank_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hq2 : ¬ (q.p = 2 ∧ q.exponent = 1)) [Finite (CFSGIndex.lie ⟨.F4 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.F4 q, hv⟩ with hd
  have : Finite (FixedPointCandidate d.geckFrobenius) := ‹Finite (CFSGIndex.lie d).Group›
  change 4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius)
  have hC : commutator ↥(adjointGroup .F4 d.fixedField) = ⊤ :=
    single_edge_perfect .F4 d.fixedField (by simp)
  have hq : d.fieldOrder ≠ 2 := by
    intro h
    have hc : q.p ^ q.exponent = 2 := by
      rw [← PrimePower.card_def, ← LieTypeIndex.fieldOrder_F4]
      exact h
    have hp2 : q.p = 2 := by
      have := (Nat.prime_two.eq_one_or_self_of_dvd q.p (hc ▸ dvd_pow_self q.p
        q.exponent_pos.ne'))
      rcases this with h1 | h1
      · exact absurd h1 q.prime_p.one_lt.ne'
      · exact h1
    refine hq2 ⟨hp2, ?_⟩
    rw [hp2] at hc
    exact Nat.pow_right_injective (le_refl 2) (hc.trans (pow_one 2).symm)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .F4
    ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]] (by decide +kernel)
  exact four_le_twoLocalOddRank_geck_four d geckMatchF4 hC hq ι hι hcomm

theorem four_le_twoLocalOddRank_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hp2 : q.p ≠ 2) (hf : 2 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.G2 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.G2 q, hv⟩ with hd
  have : Finite (FixedPointCandidate d.geckFrobenius) := ‹Finite (CFSGIndex.lie d).Group›
  change 4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.geckFrobenius)
  have hq : d.fieldOrder = q.p ^ q.exponent :=
    (LieTypeIndex.fieldOrder_G2 q).trans (PrimePower.card_def q)
  have h3 : 3 ≤ Nat.card d.fixedField := by
    rw [ValidLieTypeIndex.card_fixedField, hq]
    exact le_trans (by have := q.prime_p.two_le; omega) (Nat.le_self_pow (by omega) q.p)
  have hC : commutator ↥(adjointGroup .G2 d.fixedField) = ⊤ :=
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card d.fixedField
      h3).1.commutator_eq_top
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .G2
    ![![1, 0], ![1, 2]] (by decide +kernel)
  exact four_le_twoLocalOddRank_geck_two d geckMatchG2 hC q.prime_p hp2 hf hq ι hι hcomm

end CFSG.RankThree.PartTwo.Census.Exceptional
