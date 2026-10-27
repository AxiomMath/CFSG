module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34HypA
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardUT
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian

import CFSG.RankThree.GF2n.Parrott.CaseIIDouble

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.GF2n.Parrott.CaseIIDouble
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

local notation "C2" => Multiplicative (ZMod 2)

variable {K : Type} [Group K] [Finite K] {w : K}

omit [Finite K] in
private theorem mem_conjugate_iff_aux (S : Subgroup K) (g x : K) :
    x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    exact hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩

theorem hweak_of_isElemAbelian (h : Tim79a.ParrottHypA w)
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hIII : ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {E : Subgroup K} (hEH : E ≤ H w) (hEHJ : E ≤ ⁅H w, H w⁆ ⊔ J w) (hwE : w ∈ E)
    (hE2 : IsElemAbelian 2 E)
    (hcard : Nat.card E = 2 ^ 9) (hcardJ : Nat.card ↥(E ⊓ J w) = 2 ^ 5)
    (hECE : E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K))
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920) :
    ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E := by
  have hE := isParrottE_prod_top h hEH hEHJ hwE hE2 hcard hcardJ hECE hrel
  have h2 := parrottHyp_zz h
  have : ((J (zz w)).subgroupOf (H (zz w))).Normal := J_subgroupOf_normal (zz w)
  have hIII2 : ¬ ParrottEqualityBranch (z := zz w) (D := quotientDataZZ D) h2 :=
    fun hb => hIII ((parrottEqualityBranch_zz_iff h2 D).mp hb)
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h2 (quotientDataZZ D)).mp
    (generatorConjugacy_of_not_equalityBranch h2 (quotientDataZZ D) hIII2)
  have hP' : ∀ a : QA45.originalSubgroup,
      actionQA45 (z := zz w) h2 (quotientDataZZ D) a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  have hV1 := fixDimV_eq_four_of_conj_rep (quotientDataZZ D) h2 rhoA P hP'
    (fun a ha => spinFixedCard_ut a ha)
  have hEweak := eweak_of_fixDim_four (quotientDataZZ D) h2 hV1 qa45_elemAbelian_card_le_sixteen
    qa45_elemAbelian_pair_inf
  intro T hT hET g hg
  have hT2 : IsSylowOf 2 (T.prod (⊤ : Subgroup C2)) (H (zz w)) := by
    rw [H_zz]
    exact isSylowOf_prod_top hT
  have hET2 : E.prod (⊤ : Subgroup C2) ≤ T.prod (⊤ : Subgroup C2) :=
    Subgroup.prod_mono hET le_rfl
  have hg2 : CFSG.conjugate (E.prod (⊤ : Subgroup C2)) ((g, 1) : D2 K) ≤
      T.prod (⊤ : Subgroup C2) := by
    rintro ⟨a, c⟩ ha
    rw [mem_conjugate_iff_aux] at ha
    have e1 : (((g, 1) : D2 K) * (a, c) * ((g, 1) : D2 K)⁻¹) = (g * a * g⁻¹, c) := by
      refine Prod.ext (by simp) ?_
      simp
    rw [e1, Subgroup.mem_prod] at ha
    refine Subgroup.mem_prod.mpr ⟨hg ?_, Subgroup.mem_top c⟩
    rw [mem_conjugate_iff_aux]
    exact ha.1
  have heq := hEweak _ hE _ hT2 hET2 _ hg2
  ext x
  have := congrArg (fun S : Subgroup (D2 K) => ((x, (1 : C2)) : D2 K) ∈ S) heq
  simp only [mem_conjugate_iff_aux, Subgroup.mem_prod, Subgroup.mem_top, and_true] at this
  have e2 : (((g, 1) : D2 K) * (x, 1) * ((g, 1) : D2 K)⁻¹) = (g * x * g⁻¹, 1) := by
    refine Prod.ext (by simp) ?_
    simp
  rw [e2] at this
  simpa [mem_conjugate_iff_aux] using this

end CFSG.RankThree.GF2n.Parrott
