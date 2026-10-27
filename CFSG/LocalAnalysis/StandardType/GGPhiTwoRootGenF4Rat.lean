module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoLSS92Input
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralB4
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenLang
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem phiTwoB4Roots_eq_kernelRoots :
    {γ : Fin Tag.F4.rank → ℤ | IsRoot .F4 γ ∧ Even (γ ⟨3, by decide⟩)} =
      kernelRoots (maskChar (τ := .F4) CFSG.ComponentClassification.CatLeafProof.f4BitsB4) := by
  ext γ
  rw [Set.mem_ofPred_eq, mem_kernelRoots_maskChar,
    CFSG.ComponentClassification.CatLeafProof.maskPairing_f4BitsB4]
  have h : γ (⟨3, by decide⟩ : Fin Tag.F4.rank) =
      γ (CFSG.ComponentClassification.CatLeafProof.f4Node 3) := by
    congr 1
  rw [h]

private def f4B4Weyl : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd
    [CFSG.ComponentClassification.CatLeafProof.f4Node 3,
      CFSG.ComponentClassification.CatLeafProof.f4Node 2]

private theorem f4B4Weyl_smul_one :
    f4B4Weyl • (Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1 :
        Fin Tag.F4.rank → ℤ) = CFSG.ComponentClassification.CatLeafProof.b4Root := by
  rw [f4B4Weyl, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_smul, mul_smul, one_smul, simple_smul, simple_smul,
    CFSG.ComponentClassification.CatLeafProof.reflect_three_two_single_one]

private theorem f4B4Weyl_inv :
    f4B4Weyl⁻¹ = (coxeterSystem .F4).wordProd
      [CFSG.ComponentClassification.CatLeafProof.f4Node 2,
        CFSG.ComponentClassification.CatLeafProof.f4Node 3] := by
  rw [f4B4Weyl, ← CoxeterSystem.wordProd_reverse]
  rfl

private theorem torusElt_three_eq_conj_mul {K : Type} [Field K]
    (u : Kˣ) :
    torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 3) u =
      (canonicalRep (coxeterSystem .F4) K f4B4Weyl *
          torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 1) u *
        (canonicalRep (coxeterSystem .F4) K f4B4Weyl)⁻¹) *
        torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 1) u⁻¹ *
          torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 2) u⁻¹ := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit]
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply]
  rw [CFSG.LieType.Chevalley.weylTuple,
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar]
  simp only [← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum, f4B4Weyl_inv]
  rw [inv_zpow', inv_zpow', ← zpow_add, ← zpow_add]
  congr 1
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_smul, one_smul,
    simple_smul]
  revert j
  decide

private def phiTwoB4RootSet : Set (Fin Tag.F4.rank → ℤ) :=
  {γ | IsRoot .F4 γ ∧ Even (γ ⟨3, by decide⟩)}

private theorem single_mem_phiTwoB4RootSet (i : Fin Tag.F4.rank)
    (hi : i ≠ CFSG.ComponentClassification.CatLeafProof.f4Node 3) :
    (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ phiTwoB4RootSet := by
  refine ⟨isRoot_single .F4 i, ?_⟩
  have h3 : (⟨3, by decide⟩ : Fin Tag.F4.rank) =
      CFSG.ComponentClassification.CatLeafProof.f4Node 3 := by congr 1
  rw [h3]
  simp [Pi.single_apply, hi]

private theorem neg_single_mem_phiTwoB4RootSet (i : Fin Tag.F4.rank)
    (hi : i ≠ CFSG.ComponentClassification.CatLeafProof.f4Node 3) :
    (-Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ phiTwoB4RootSet := by
  refine ⟨isRoot_neg_single .F4 i, ?_⟩
  have h3 : (⟨3, by decide⟩ : Fin Tag.F4.rank) =
      CFSG.ComponentClassification.CatLeafProof.f4Node 3 := by congr 1
  rw [h3, Pi.neg_apply]
  simp [Pi.single_apply, hi]

private theorem neg_mem_phiTwoB4RootSet {γ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ phiTwoB4RootSet) : -γ ∈ phiTwoB4RootSet :=
  ⟨IsRoot.neg hγ.1, by rw [Pi.neg_apply]; exact hγ.2.neg⟩

private theorem b4Root_mem_phiTwoB4RootSet :
    CFSG.ComponentClassification.CatLeafProof.b4Root ∈ phiTwoB4RootSet := by
  refine ⟨CFSG.ComponentClassification.CatLeafProof.isRoot_b4Root, ?_⟩
  have h3 : (⟨3, by decide⟩ : Fin Tag.F4.rank) =
      CFSG.ComponentClassification.CatLeafProof.f4Node 3 := by congr 1
  rw [h3]
  decide

private def f4B4RootE3E4 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 0]

private theorem isRoot_f4B4RootE3E4 :
    IsRoot .F4 f4B4RootE3E4 :=
  (CFSG.SeitzReduction.F4Pilot.mem_C3Roots_iff.1
    (by decide : f4B4RootE3E4 ∈ CFSG.SeitzReduction.F4Pilot.C3Roots)).1

private theorem f4Neg_eq_prod_rootReflection :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg =
      rootReflection CFSG.SeitzReduction.F4Pilot.rootR *
        rootReflection CFSG.ComponentClassification.CatLeafProof.b4Root *
          rootReflection f4B4RootE3E4 *
            rootReflection (Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1) := by
  refine ext_single fun i => ?_
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul]
  simp only [mul_smul]
  rw [rootReflection_smul CFSG.SeitzReduction.F4Pilot.isRoot_rootR,
    rootReflection_smul CFSG.ComponentClassification.CatLeafProof.isRoot_b4Root,
    rootReflection_smul isRoot_f4B4RootE3E4,
    rootReflection_smul (isRoot_single .F4 (CFSG.ComponentClassification.CatLeafProof.f4Node 1))]
  ext j
  revert i j
  decide

private theorem torusElt_three_mem_rootSpan {K : Type} [Field K]
    (u : Kˣ) :
    torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 3) u ∈
      rootSpan .F4 K phiTwoB4RootSet := by
  rw [torusElt_three_eq_conj_mul]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · have hmap : (rootSubgroup .F4 K
        (Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1) ⊔
          rootSubgroup .F4 K
            (-Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K f4B4Weyl)).toMonoidHom =
        rootSubgroup .F4 K CFSG.ComponentClassification.CatLeafProof.b4Root ⊔
          rootSubgroup .F4 K (-CFSG.ComponentClassification.CatLeafProof.b4Root) := by
      rw [Subgroup.map_sup,
        (canonical_weyl_root_transport .F4 K).2.1 f4B4Weyl _
          (isRoot_single .F4 (CFSG.ComponentClassification.CatLeafProof.f4Node 1)),
        (canonical_weyl_root_transport .F4 K).2.1 f4B4Weyl _
          (IsRoot.neg (isRoot_single .F4
            (CFSG.ComponentClassification.CatLeafProof.f4Node 1))),
        smul_neg, f4B4Weyl_smul_one]
    have hmem : canonicalRep (coxeterSystem .F4) K f4B4Weyl *
        torusElt .F4 K (CFSG.ComponentClassification.CatLeafProof.f4Node 1) u *
          (canonicalRep (coxeterSystem .F4) K f4B4Weyl)⁻¹ ∈
        (rootSubgroup .F4 K
            (Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1) ⊔
          rootSubgroup .F4 K
            (-Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1)).map
          (MulAut.conj (canonicalRep (coxeterSystem .F4) K f4B4Weyl)).toMonoidHom :=
      ⟨_, CFSG.SeitzReduction.F4Pilot.torusElt_mem_rootPair
        (CFSG.ComponentClassification.CatLeafProof.f4Node 1) u, rfl⟩
    rw [hmap] at hmem
    exact sup_le
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ phiTwoB4RootSet) => rootSubgroup .F4 K γ)
        CFSG.ComponentClassification.CatLeafProof.b4Root b4Root_mem_phiTwoB4RootSet le_rfl)
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ phiTwoB4RootSet) => rootSubgroup .F4 K γ)
        (-CFSG.ComponentClassification.CatLeafProof.b4Root)
        (neg_mem_phiTwoB4RootSet b4Root_mem_phiTwoB4RootSet) le_rfl) hmem
  · exact CFSG.RankThree.PartOne.SEITZ7.torusElt_mem_rootSpan'
      (single_mem_phiTwoB4RootSet _ (by decide))
      (neg_single_mem_phiTwoB4RootSet _ (by decide)) _
  · exact CFSG.RankThree.PartOne.SEITZ7.torusElt_mem_rootSpan'
      (single_mem_phiTwoB4RootSet _ (by decide))
      (neg_single_mem_phiTwoB4RootSet _ (by decide)) _

theorem phiTwoB4Subgroup_eq_rootSpan
    {K : Type} [Field K] :
    phiTwoB4Subgroup K =
      rootSpan .F4 K {γ : Fin Tag.F4.rank → ℤ | IsRoot .F4 γ ∧ Even (γ ⟨3, by decide⟩)} := by
  change torusGroup .F4 K ⊔ rootSpan .F4 K phiTwoB4RootSet =
    rootSpan .F4 K phiTwoB4RootSet
  refine le_antisymm ?_ le_sup_right
  refine sup_le ?_ le_rfl
  intro h hh
  obtain ⟨c, rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup hh
  rw [← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j = CFSG.ComponentClassification.CatLeafProof.f4Node 3
  · subst hj
    exact torusElt_three_mem_rootSpan (c _)
  · exact CFSG.RankThree.PartOne.SEITZ7.torusElt_mem_rootSpan'
      (single_mem_phiTwoB4RootSet j hj)
      (neg_single_mem_phiTwoB4RootSet j hj) _

@[expose] def f4D4Char : Multiplicative (Fin Tag.F4.rank → ℤ) →* ℤˣ × ℤˣ :=
  (maskChar (τ := .F4) (listMask [false, false, true, false])).prod
    (maskChar (τ := .F4) CFSG.ComponentClassification.CatLeafProof.f4BitsB4)

theorem mem_kernelRoots_f4D4Char {γ : Fin Tag.F4.rank → ℤ} :
    γ ∈ kernelRoots f4D4Char ↔
      IsRoot .F4 γ ∧ Even (γ ⟨2, by decide⟩) ∧ Even (γ ⟨3, by decide⟩) := by
  have h2 : maskPairing (listMask (τ := .F4) [false, false, true, false]) γ =
      γ (CFSG.ComponentClassification.CatLeafProof.f4Node 2) := by
    rw [maskPairing]
    change (∑ j : Fin 4, if listMask (τ := .F4) [false, false, true, false] j = true then
      γ j else 0) = γ (CFSG.ComponentClassification.CatLeafProof.f4Node 2)
    rw [Fin.sum_univ_four]
    simp [listMask, CFSG.ComponentClassification.CatLeafProof.f4Node]
  have h2' : (γ (CFSG.ComponentClassification.CatLeafProof.f4Node 2) : ℤ) =
      γ ⟨2, by decide⟩ := by congr 1
  have h3 : maskPairing (τ := .F4) CFSG.ComponentClassification.CatLeafProof.f4BitsB4 γ =
      γ (CFSG.ComponentClassification.CatLeafProof.f4Node 3) :=
    CFSG.ComponentClassification.CatLeafProof.maskPairing_f4BitsB4 γ
  have h3' : (γ (CFSG.ComponentClassification.CatLeafProof.f4Node 3) : ℤ) =
      γ ⟨3, by decide⟩ := by congr 1
  have hmem : γ ∈ kernelRoots f4D4Char ↔
      γ ∈ kernelRoots (maskChar (τ := .F4) (listMask [false, false, true, false])) ∧
        γ ∈ kernelRoots (maskChar (τ := .F4)
          CFSG.ComponentClassification.CatLeafProof.f4BitsB4) := by
    rw [f4D4Char, kernelRoots, Set.mem_ofPred_eq, MonoidHom.prod_apply, Prod.mk_eq_one]
    constructor
    · rintro ⟨hI, he1, he2⟩
      rw [maskChar_apply, neg_one_zpow_eq_one_iff] at he1 he2
      exact ⟨mem_kernelRoots_maskChar.2 ⟨hI, he1⟩,
        mem_kernelRoots_maskChar.2 ⟨hI, he2⟩⟩
    · rintro ⟨h1, h2⟩
      rw [mem_kernelRoots_maskChar] at h1 h2
      refine ⟨h1.1, ?_, ?_⟩
      · rw [maskChar_apply, neg_one_zpow_eq_one_iff]
        exact h1.2
      · rw [maskChar_apply, neg_one_zpow_eq_one_iff]
        exact h2.2
  rw [hmem]
  simp only [mem_kernelRoots_maskChar, h2, h2', h3, h3']
  tauto

theorem f4Neg_mem_closure_rootReflection_kernelRoots_f4D4Char :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∈
      Subgroup.closure ((fun α => rootReflection α) '' kernelRoots f4D4Char) := by
  rw [f4Neg_eq_prod_rootReflection]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · refine Subgroup.subset_closure ⟨CFSG.SeitzReduction.F4Pilot.rootR, ?_, rfl⟩
    rw [mem_kernelRoots_f4D4Char]
    exact ⟨CFSG.SeitzReduction.F4Pilot.isRoot_rootR, by decide, by decide⟩
  · refine Subgroup.subset_closure ⟨CFSG.ComponentClassification.CatLeafProof.b4Root, ?_, rfl⟩
    rw [mem_kernelRoots_f4D4Char]
    exact ⟨CFSG.ComponentClassification.CatLeafProof.isRoot_b4Root, by decide, by decide⟩
  · refine Subgroup.subset_closure ⟨f4B4RootE3E4, ?_, rfl⟩
    rw [mem_kernelRoots_f4D4Char]
    exact ⟨isRoot_f4B4RootE3E4, by decide, by decide⟩
  · refine Subgroup.subset_closure
      ⟨Pi.single (CFSG.ComponentClassification.CatLeafProof.f4Node 1) 1, ?_, rfl⟩
    rw [mem_kernelRoots_f4D4Char]
    exact ⟨isRoot_single .F4 _,
      by rw [Pi.single_apply]; decide,
      by rw [Pi.single_apply]; decide⟩

private theorem f4Neg_mem_closure_rootReflection_kernelRoots :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∈
      Subgroup.closure ((fun α => rootReflection α) ''
        kernelRoots (maskChar (τ := .F4)
          CFSG.ComponentClassification.CatLeafProof.f4BitsB4)) := by
  have hsub : kernelRoots f4D4Char ⊆
      kernelRoots (maskChar (τ := .F4)
        CFSG.ComponentClassification.CatLeafProof.f4BitsB4) := by
    intro γ hγ
    rw [mem_kernelRoots_f4D4Char] at hγ
    rw [mem_kernelRoots_maskChar,
      CFSG.ComponentClassification.CatLeafProof.maskPairing_f4BitsB4]
    refine ⟨hγ.1, ?_⟩
    have h3 : (⟨3, by decide⟩ : Fin Tag.F4.rank) =
        CFSG.ComponentClassification.CatLeafProof.f4Node 3 := by congr 1
    rw [← h3]
    exact hγ.2.2
  exact Subgroup.closure_mono
    (Set.image_mono (f := fun α => rootReflection α) hsub)
    f4Neg_mem_closure_rootReflection_kernelRoots_f4D4Char

theorem exists_mul_eq_phiTwoB4
    {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .F4} (hneg : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → w • γ = -γ)
    {g0 : ModGL .F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w) :
    ∃ h : adjointGroup .F4 K, ∃ d ∈ phiTwoB4Subgroup (AlgebraicClosure K),
      g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .F4 K) * d := by
  have hw : w = CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg := by
    refine ext_single fun i => ?_
    rw [hneg _ (IsRoot.basis i), CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul]
  subst w
  have hD : phiTwoB4Subgroup (AlgebraicClosure K) =
      torusGroup .F4 (AlgebraicClosure K) ⊔
        rootSpan .F4 (AlgebraicClosure K)
          (kernelRoots (maskChar (τ := .F4)
            CFSG.ComponentClassification.CatLeafProof.f4BitsB4)) := by
    rw [phiTwoB4Subgroup, phiTwoB4Roots_eq_kernelRoots]
  obtain ⟨h, d, hd, hg0eq⟩ :=
    exists_mul_eq_kernelGroup
      (maskChar (τ := .F4) CFSG.ComponentClassification.CatLeafProof.f4BitsB4) hFr
      (fun X _ hXC hXF _ hy =>
        CFSG.LieType.Chevalley.mem_map_adjointGroup_F4_of_frobenius_fixed
          (k := K) (L := AlgebraicClosure K) Fr hFr (hXC hy) (hXF _ hy))
      hg0C hg0
      (CFSG.LieType.AlgebraicGroups.canonicalRep_mem_torus_sup_rootSpan_kernelRoots
        f4Neg_mem_closure_rootReflection_kernelRoots)
  refine ⟨h, d, ?_, hg0eq⟩
  rw [hD]
  exact hd

theorem mem_phiTwoB4_iff
    {K : Type} [Field K] {g0 : ModGL .F4 (AlgebraicClosure K)} {h : adjointGroup .F4 K}
    {d : ModGL .F4 (AlgebraicClosure K)} (hd : d ∈ phiTwoB4Subgroup (AlgebraicClosure K))
    (hg0 : g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL .F4 K) * d)
    (x : adjointGroup .F4 K) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .F4 K) * g0 ∈
        phiTwoB4Subgroup (AlgebraicClosure K) ↔
      ((h⁻¹ * x * h : adjointGroup .F4 K) : ModGL .F4 K) ∈ phiTwoB4Subgroup K := by
  have hDL : phiTwoB4Subgroup (AlgebraicClosure K) =
      torusGroup .F4 (AlgebraicClosure K) ⊔ rootSpan .F4 (AlgebraicClosure K)
        (kernelRoots (maskChar (τ := .F4)
          CFSG.ComponentClassification.CatLeafProof.f4BitsB4)) := by
    rw [phiTwoB4Subgroup, phiTwoB4Roots_eq_kernelRoots]
  have hDK : phiTwoB4Subgroup K =
      torusGroup .F4 K ⊔ rootSpan .F4 K
        (kernelRoots (maskChar (τ := .F4)
          CFSG.ComponentClassification.CatLeafProof.f4BitsB4)) := by
    rw [phiTwoB4Subgroup, phiTwoB4Roots_eq_kernelRoots]
  rw [hDL] at hd
  rw [hDL, hDK]
  exact mem_kernelGroup_conj_iff
    (maskChar (τ := .F4) CFSG.ComponentClassification.CatLeafProof.f4BitsB4) hd hg0 x

end CFSG.StandardType.PhiTwoRootGen

end
