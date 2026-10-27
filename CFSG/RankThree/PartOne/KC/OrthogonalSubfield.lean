module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

open Matrix QuadraticMap CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.LocalRank
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ABGLocalTools (solvableRadical_normal solvableRadical_isSolvable)

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Assembly

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem solvableRadical_fixedGroup (hBY : HighWittSubfieldSemilinearPointwiseCentralizer)
    (S : SubfieldSetup k Q₀ Q σ p) :
    solvableRadical ↥(subfieldFixedGroup k Q₀ Q) = ⊥ := by
  set N := subfieldFixedGroup k Q₀ Q with hN
  set R₀ := solvableRadical ↥N with hR₀
  have hnorm : R₀.Normal := solvableRadical_normal
  have hsolv₀ : Group.IsSolvable R₀ := solvableRadical_isSolvable
  have hmap : R₀.map N.subtype = ⊥ := by
    refine solvable_normal_trivial hBY S (Subgroup.map_subtype_le R₀) ?_ ?_
    · change (Subgroup.comap N.subtype (R₀.map N.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
      exact hnorm
    · exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective R₀ N.subtype N.subtype_injective).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective R₀ N.subtype N.subtype_injective).symm.injective
  exact (Subgroup.map_eq_bot_iff_of_injective R₀ N.subtype_injective).mp hmap

end Assembly

end CFSG.RankThree.PartOne.KCOrthogonalSubfield

namespace CFSG.RankThree.PartOne

@[expose] def SubfieldConclusion {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}
    (Q₀ : QuadraticForm k (Fin d → k)) (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K) (p : ℕ)
    (hext : IsExtension k Q₀ Q) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) : Prop :=
  (Function.Injective (incl k hext) ∧ IsSimpleGroup ↥(subfieldDerivedImage k hext) ∧
    ∃ x y : ↥(subfieldDerivedImage k hext), x * y ≠ y * x) ∧
  orderOf (fieldAutT Q σ hQσ) = p ∧
  (∀ t, fieldAutT Q σ hQσ t = t ↔ t ∈ subfieldFixedGroup k Q₀ Q) ∧
  subfieldDerivedImage k hext ≤ subfieldFixedGroup k Q₀ Q ∧
  ((subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)).Normal ∧
  (∀ [((subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)).Normal],
    IsPGroup 2 (↥(subfieldFixedGroup k Q₀ Q) ⧸
      (subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q))) ∧
  solvableRadical ↥(subfieldFixedGroup k Q₀ Q) = ⊥ ∧
  fixingSubgroup (MulAut (matrixProjectiveDerived Q))
      (subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) =
    Subgroup.zpowers (fieldAutT Q σ hQσ) ∧
  fixingSubgroup (MulAut (matrixProjectiveDerived Q))
      (subfieldDerivedImage k hext : Set (matrixProjectiveDerived Q)) =
    Subgroup.zpowers (fieldAutT Q σ hQσ) ∧
  ∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ B → fieldAutT Q σ hQσ ∈ B →
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {fieldAutT Q σ hQσ}) = ⊥

@[expose] def ModelOrthogonalSubfield (c : StatedLieTag) (n ℓ e p : ℕ) : Prop :=
  StatedLieAdmissible c n ℓ e → p.Prime → 3 < p → p ≠ ℓ →
  match c with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n K)) .POmegaOdd n ℓ
          (e * p) ∧
        SubfieldConclusion k (coordinateQuadOdd n k) (coordinateQuadOdd n K) σ p
          (coordinateQuadOdd_isExtension k n) (coordinateQuadOdd_fieldAut n σ)
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n ℓ
          (e * p) ∧
        SubfieldConclusion k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p
          (coordinateQuadPlus_isExtension k n) (coordinateQuadPlus_fieldAut n σ)
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (k : Subfield K),
      Nat.card k = ℓ ^ e → Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p →
        ∀ hσk : (∀ x, x ∈ k ↔ σ x = x), ∀ b c' : k, (∀ s : k, s ^ 2 + b * s + c' ≠ 0) →
          StatedClassicalModel
            (matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c' : K))) .POmegaMinus n
            ℓ (e * p) ∧
          SubfieldConclusion k (coordinateQuadMinus n k hn b c')
            (coordinateQuadMinus n K hn (b : K) (c' : K)) σ p
            (coordinateQuadMinus_isExtension k n hn b c')
            (coordinateQuadMinus_fieldAut k n hn hσk b c')
  | _ => False

theorem subfield_conclusion {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
    {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}
    (hBY : HighWittSubfieldSemilinearPointwiseCentralizer) (S : SubfieldSetup k Q₀ Q σ p)
    (hE : ∀ β : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, β t = t) → β ∈ matrixProjectiveImage Q) :
    SubfieldConclusion k Q₀ Q σ p S.hext S.hQσ := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimple, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  refine ⟨⟨incl_injective k S.hext hd, ?_, ?_⟩,
    (orderOf_fieldAutT Q σ S.hQσ S.hnd S.hT S.hAP).trans S.hσ, fieldAutT_apply_iff S,
    subfieldDerivedImage_le k S.hext, subfieldDerivedImage_normal k S.hext, ?_,
    solvableRadical_fixedGroup hBY S, fixingSubgroup_N hBY S hE, fixingSubgroup_J hBY S hE,
    fun B hB _ => core_trivial hBY S hE hB⟩
  · have := hsimple
    exact (inclEquiv k S.hext hd).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨inclEquiv k S.hext hd a, inclEquiv k S.hext hd b, fun h => hab
      ((inclEquiv k S.hext hd).injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  · intro _
    exact fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀


open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem orthogonal_prime_subfield_fixed_group_and_full_centralizer
    (hBY : HighWittSubfieldSemilinearPointwiseCentralizer) (c : StatedLieTag)
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) (n ℓ e p : ℕ) :
    ModelOrthogonalSubfield c n ℓ e p := by
  intro hadm hp hp3 hpℓ
  have hp2 : p ≠ 2 := by omega
  rcases hc with rfl | rfl | rfl
  ·
    intro K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn3, hℓ2⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have h2K : ringChar K ≠ 2 := by
      rw [ringChar_eq_of_card_eq hℓ hf hK]
      exact hℓ2
    have S := subfieldSetup_odd k hσk hp hp2 hσ hn3 (Ring.two_ne_zero h2K)
    refine ⟨⟨⟨hℓ, hf, hn3, hℓ2⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
      (oddIndexEquiv n) (quadOdd n K) (coe_quadOdd n K)).symm⟩⟩, subfield_conclusion hBY S ?_⟩
    intro β _
    rw [matrixProjectiveImage_eq_top_odd K n hn3 h2K]
    exact Subgroup.mem_top β
  ·
    intro K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
    have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K))
        .POmegaPlus n ℓ (e * p) :=
      ⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
        (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)).symm⟩⟩
    refine ⟨hmodel, subfield_conclusion hBY S ?_⟩
    by_cases hn : n = 4
    · subst hn
      intro β hβ
      exact mem_matrixProjectiveImage_plus_four k hK hmodel (statedProjectiveReindexEquiv
        (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm S.hext S.hnd₀ S.hT₀ β hβ
    · intro β _
      rw [matrixProjectiveImage_eq_top_plus K n (by omega)]
      exact Subgroup.mem_top β
  ·
    intro hn K _ _ k hk hK σ hσ hσk b c' hirr
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    have hirrK := rootFree_of_odd_degree k hp hp2 hdeg b c' hirr
    have S := subfieldSetup_minus k hσk hp hp2 hσ hn4 hdeg b c' hirr
    refine ⟨⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, (b : K), (c' : K), hirrK,
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n K (b : K) (c' : K))
        (coe_quadMinus n K (b : K) (c' : K))).symm⟩⟩, subfield_conclusion hBY S ?_⟩
    intro β _
    rw [matrixProjectiveImage_eq_top_minus K n hn4 (b : K) (c' : K) hirrK]
    exact Subgroup.mem_top β

theorem orthogonal_prime_subfield_core_clause
    (hBY : HighWittSubfieldSemilinearPointwiseCentralizer) : OrthogonalSubfieldCoreClause := by
  intro c n ℓ f p hc hadm hp hp3 hpℓ hpf K _ _ hK σ hσ hcard
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer hBY c hc n ℓ e p hadm hp
    hp3 hpℓ
  rcases hc with rfl | rfl | rfl
  · intro g hl hr B hB haB
    obtain ⟨-, -, -, -, -, -, -, -, -, hcore⟩ := (key K (semilinearFixedSubfield σ) hcard hK' σ
      hσ hσk).2
    have hg : g = fieldPair (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) :=
      Subtype.ext (SemidirectProduct.ext hl hr)
    subst hg
    exact hcore B hB haB
  · intro g hl hr B hB haB
    obtain ⟨-, -, -, -, -, -, -, -, -, hcore⟩ := (key K (semilinearFixedSubfield σ) hcard hK' σ
      hσ hσk).2
    have hg : g = fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) :=
      Subtype.ext (SemidirectProduct.ext hl hr)
    subst hg
    exact hcore B hB haB
  · intro hn b c' hirr g hl hr B hB haB
    obtain ⟨-, -, -, -, -, -, -, -, -, hcore⟩ := (key hn K (semilinearFixedSubfield σ) hcard hK'
      σ hσ hσk b c' hirr).2
    have hg : g = fieldPair (coordinateQuadMinus n K hn (b : K) (c' : K)) σ
        (coordinateQuadMinus_fieldAut (semilinearFixedSubfield σ) n hn hσk b c') :=
      Subtype.ext (SemidirectProduct.ext hl hr)
    subst hg
    exact hcore B hB haB

end CFSG.RankThree.PartOne
