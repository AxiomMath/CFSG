module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenLang
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7D0
public import CFSG.LieType.Chevalley.SignCharacterMasks
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusDescent
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.TableBExcTwo

@[expose] def e7BitsTheta : Fin Tag.E7.rank → Bool := fun i => decide (i = 0)

@[expose] def e7BitsBeta : Fin Tag.E7.rank → Bool := fun i => decide (i = 0 ∨ i = 5)

@[expose] noncomputable def e7ChiC :
    Multiplicative (Fin Tag.E7.rank → ℤ) →* ℤˣ × ℤˣ :=
  (maskChar (τ := .E7) e7BitsTheta).prod (maskChar (τ := .E7) e7BitsBeta)

theorem ggPhiTwoGlue_kernelRoots_prod {M N : Type*} [CommGroup M] [CommGroup N]
    (f : Multiplicative (Fin Tag.E7.rank → ℤ) →* M)
    (g : Multiplicative (Fin Tag.E7.rank → ℤ) →* N) :
    kernelRoots (f.prod g) = kernelRoots f ∩ kernelRoots g := by
  ext α
  rw [kernelRoots, kernelRoots, kernelRoots, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hR, hχ⟩
    rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hχ
    exact ⟨⟨hR, hχ.1⟩, ⟨hR, hχ.2⟩⟩
  · rintro ⟨⟨hR1, hχ1⟩, ⟨hR2, hχ2⟩⟩
    exact ⟨hR1, by rw [MonoidHom.prod_apply, Prod.mk_eq_one]; exact ⟨hχ1, hχ2⟩⟩

theorem ggPhiTwoGlue_maskPairing_theta (γ : Fin Tag.E7.rank → ℤ) :
    maskPairing e7BitsTheta γ = γ 0 := by
  simp [maskPairing, e7BitsTheta]

theorem ggPhiTwoGlue_maskPairing_beta (γ : Fin Tag.E7.rank → ℤ) :
    maskPairing e7BitsBeta γ = γ 0 + γ 5 := by
  rw [maskPairing]
  have h : ∀ x : Fin Tag.E7.rank, (if e7BitsBeta x then γ x else 0)
      = (if x = 0 then γ x else 0) + (if x = 5 then γ x else 0) := by
    intro x
    by_cases h0 : x = 0 <;> by_cases h5 : x = 5 <;> simp [e7BitsBeta, h0, h5]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem ggPhiTwoGlue_maskAct : maskAct e7Word e7BitsTheta = e7BitsBeta := by
  decide +kernel

theorem ggPhiTwoGlue_kernelRoots_e7ChiC :
    kernelRoots e7ChiC = kernelRoots (maskChar (τ := .E7) e7BitsTheta) ∩
      kernelRoots (maskChar (τ := .E7) e7BitsBeta) := by
  change kernelRoots ((maskChar (τ := .E7) e7BitsTheta).prod
    (maskChar (τ := .E7) e7BitsBeta)) = _
  exact ggPhiTwoGlue_kernelRoots_prod _ _

theorem ggPhiTwoGlue_kernelRoots_theta :
    kernelRoots (maskChar (τ := .E7) e7BitsTheta) = e7A1D6Roots := by
  ext γ
  rw [mem_kernelRoots_maskChar, ggPhiTwoGlue_maskPairing_theta]
  rfl

noncomputable def ggPhiTwoGlue_frameList : List (WeylGroup .E7) :=
  [rootReflection (frameE7Root 0), rootReflection (frameE7Root 1),
    rootReflection (frameE7Root 2), rootReflection (frameE7Root 3),
    rootReflection (frameE7Root 4), rootReflection (frameE7Root 5),
    rootReflection (frameE7Root 6)]

noncomputable def ggPhiTwoGlue_frameW : WeylGroup .E7 := ggPhiTwoGlue_frameList.prod

theorem ggPhiTwoGlue_frameW_single
    (k : Fin Tag.E7.rank) :
    ggPhiTwoGlue_frameW • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = -Pi.single k 1 := by
  rw [ggPhiTwoGlue_frameW, ggPhiTwoGlue_frameList]
  simp only [List.prod_cons, List.prod_nil, mul_smul,
    rootReflection_smul (e7Frame_isRoot 0), rootReflection_smul (e7Frame_isRoot 1),
    rootReflection_smul (e7Frame_isRoot 2), rootReflection_smul (e7Frame_isRoot 3),
    rootReflection_smul (e7Frame_isRoot 4), rootReflection_smul (e7Frame_isRoot 5),
    rootReflection_smul (e7Frame_isRoot 6)]
  revert k
  decide +kernel

theorem ggPhiTwoGlue_frameE7Root_mem
    (i : Fin 7) :
    frameE7Root i ∈ kernelRoots e7ChiC := by
  rw [ggPhiTwoGlue_kernelRoots_e7ChiC, Set.mem_inter_iff]
  constructor
  · rw [kernelRoots, Set.mem_ofPred_eq]
    refine ⟨e7Frame_isRoot i, ?_⟩
    rw [maskChar_apply, neg_one_zpow_eq_one_iff, ggPhiTwoGlue_maskPairing_theta]
    fin_cases i <;> decide +kernel
  · rw [kernelRoots, Set.mem_ofPred_eq]
    refine ⟨e7Frame_isRoot i, ?_⟩
    rw [maskChar_apply, neg_one_zpow_eq_one_iff, ggPhiTwoGlue_maskPairing_beta]
    fin_cases i <;> decide +kernel

theorem ggPhiTwoGlue_frameW_mem :
    ggPhiTwoGlue_frameW ∈ Subgroup.closure ((fun α => rootReflection α) ''
      kernelRoots e7ChiC) := by
  rw [ggPhiTwoGlue_frameW, ggPhiTwoGlue_frameList]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h <;> rw [h]
  all_goals
    exact Subgroup.subset_closure ⟨_, ggPhiTwoGlue_frameE7Root_mem _, rfl⟩

theorem kernelGroup_e7ChiC_le_phiTwoA1D6Subgroup
    (L : Type) [Field L] : kernelGroup e7ChiC L ≤ phiTwoA1D6Subgroup L := by
  rw [kernelGroup, phiTwoA1D6Subgroup]
  refine sup_le le_sup_left ((rootSpan_mono ?_).trans le_sup_right)
  rw [ggPhiTwoGlue_kernelRoots_e7ChiC]
  intro γ hγ
  rw [← ggPhiTwoGlue_kernelRoots_theta]
  exact hγ.1

theorem kernelGroup_e7ChiC_le_conj
    (L : Type) [Field L] [CharP L 2] :
    kernelGroup e7ChiC L ≤ (phiTwoA1D6Subgroup L).map (MulAut.conj
      (canonicalRep (coxeterSystem .E7) L ((coxeterSystem .E7).wordProd e7Word))).toMonoidHom := by
  set v : WeylGroup .E7 := (coxeterSystem .E7).wordProd e7Word
  set n : ModGL .E7 L := canonicalRep (coxeterSystem .E7) L v
  have hn : n ∈ Subgroup.normalizer (torusGroup .E7 L : Set (ModGL .E7 L)) :=
    mem_normalizer_torusGroup_of_mem_monomialSubgroup
      (canonicalRep_mem_monomialSubgroup (τ := .E7) L v)
  have htorus : (torusGroup .E7 L).map (MulAut.conj n).toMonoidHom = torusGroup .E7 L :=
    map_conj_eq_of_mem_normalizer hn
  have hspan : (rootSpan .E7 L e7A1D6Roots).map (MulAut.conj n).toMonoidHom =
      rootSpan .E7 L ((fun γ => v • γ) '' e7A1D6Roots) :=
    CFSG.RankThree.PartOne.KE.map_conj_rootSpan (L := L) v (fun γ hγ => hγ.1)
  rw [kernelGroup, phiTwoA1D6Subgroup, Subgroup.map_sup, htorus, hspan]
  refine sup_le le_sup_left ((rootSpan_mono ?_).trans le_sup_right)
  rw [ggPhiTwoGlue_kernelRoots_e7ChiC]
  rintro γ ⟨hθ, hβ⟩
  have hχθ : maskChar (τ := .E7) e7BitsTheta
      (Multiplicative.ofAdd (v⁻¹ • γ)) = 1 := by
    rw [← maskChar_maskAct (τ := .E7) e7Word e7BitsTheta γ, ggPhiTwoGlue_maskAct]
    exact hβ.2
  refine ⟨v⁻¹ • γ, ?_, ?_⟩
  · rw [← ggPhiTwoGlue_kernelRoots_theta]
    exact ⟨IsRoot.smul hθ.1 v⁻¹, hχθ⟩
  · change v • (v⁻¹ • γ) = γ
    rw [← mul_smul, mul_inv_cancel, one_smul]

theorem canonicalRep_mem_kernelGroup_e7ChiC
    (L : Type) [Field L] {w : WeylGroup .E7}
    (hneg : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ → w • γ = -γ) :
    canonicalRep (coxeterSystem .E7) L w ∈ kernelGroup e7ChiC L := by
  have hw : w = ggPhiTwoGlue_frameW := by
    refine ext_single fun k => ?_
    rw [hneg (Pi.single k 1) (IsRoot.basis k), ggPhiTwoGlue_frameW_single]
  rw [hw, kernelGroup]
  exact canonicalRep_mem_torus_sup_rootSpan_kernelRoots ggPhiTwoGlue_frameW_mem

theorem hrat_E7
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∀ X : Subgroup (ModGL .E7 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E7 (AlgebraicClosure K) →
        (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
          X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  intro X hX hXC hXF x hx
  exact CFSG.RankThree.PartOne.KE.qplus_frobenius_fixed_mem (Or.inl rfl) Fr hFr (hXC hx)
    (hXF x hx)

end CFSG.StandardType.PhiTwoRootGen

end

