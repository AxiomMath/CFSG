module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.RankThree.PartOne.KLCE.A2Sector

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggPhiTwoConj_mapRange_smul_ringHom
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (c : M) (x : RootModule τ M) :
    Finsupp.mapRange σ σ.map_zero (c • x) = σ c • Finsupp.mapRange σ σ.map_zero x := by
  ext a
  simp

private theorem ggPhiTwoConj_entrywise_sum_smul
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) {ι : Type*} (s : Finset ι) (c : ι → M)
    (A : ι → Module.End M (RootModule τ M)) :
    entrywise σ (∑ k ∈ s, c k • A k) = ∑ k ∈ s, σ (c k) • entrywise σ (A k) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, entrywise_single]
  rw [Finsupp.mapRange_finsetSum σ]
  simp only [ggPhiTwoConj_mapRange_smul_ringHom]

private theorem ggPhiTwoConj_entrywise_xCoeff
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (xCoeff τ M i k) = xCoeff τ M i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_xCoeff_single]

private theorem ggPhiTwoConj_entrywise_yCoeff
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (yCoeff τ M i k) = yCoeff τ M i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_yCoeff_single]

private theorem ggPhiTwoConj_entrywise_xOp
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (i : Fin τ.rank) (c : M) :
    entrywise σ (xOp τ M i c) = xOp τ M i (σ c) := by
  rw [xOp_eq_sum_xCoeff, ggPhiTwoConj_entrywise_sum_smul, xOp_eq_sum_xCoeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_pow, ggPhiTwoConj_entrywise_xCoeff]

private theorem ggPhiTwoConj_entrywise_yOp
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (i : Fin τ.rank) (c : M) :
    entrywise σ (yOp τ M i c) = yOp τ M i (σ c) := by
  rw [yOp_eq_sum_yCoeff, ggPhiTwoConj_entrywise_sum_smul, yOp_eq_sum_yCoeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_pow, ggPhiTwoConj_entrywise_yCoeff]

private theorem ggPhiTwoConj_entrywise_weylElt_one
    {τ : Tag} {M : Type} [Field M] (σ : M →+* M) (i : Fin τ.rank) :
    Units.map (entrywiseHom σ) (weylElt τ M i 1) = weylElt τ M i 1 := by
  apply Units.ext
  rw [Units.coe_map, coe_weylElt]
  change entrywise σ
      (xOp τ M i (↑(1 : Mˣ)) * yOp τ M i (-(↑((1 : Mˣ)⁻¹))) * xOp τ M i (↑(1 : Mˣ))) =
    xOp τ M i (↑(1 : Mˣ)) * yOp τ M i (-(↑((1 : Mˣ)⁻¹))) * xOp τ M i (↑(1 : Mˣ))
  rw [entrywise_mul, entrywise_mul, ggPhiTwoConj_entrywise_xOp,
    ggPhiTwoConj_entrywise_yOp]
  simp

private theorem ggPhiTwoConj_entrywiseHom_canonicalRep
    {τ : Tag} {M : Type} [Field M] [CharP M 2] (σ : M →+* M) (v : WeylGroup τ) :
    Units.map (entrywiseHom σ) (canonicalRep (coxeterSystem τ) M v) =
      canonicalRep (coxeterSystem τ) M v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem τ).exists_isReduced v
  rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo (M := M) (ω := ω)]
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih,
      ggPhiTwoConj_entrywise_weylElt_one σ i]

theorem isLang_mul_canonicalRep
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}
    {w v : WeylGroup τ} (hwv : v * w = w * v) {g0 : ModGL τ L}
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w) :
    Units.map (entrywiseHom Fr) (g0 * canonicalRep (coxeterSystem τ) L v) =
      (g0 * canonicalRep (coxeterSystem τ) L v) * canonicalRep (coxeterSystem τ) L w := by
  have hcomm :
      canonicalRep (coxeterSystem τ) L w * canonicalRep (coxeterSystem τ) L v =
        canonicalRep (coxeterSystem τ) L v * canonicalRep (coxeterSystem τ) L w := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo
          (M := L) (w := w) (v := v),
      ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo
          (M := L) (w := v) (v := w), hwv]
  rw [map_mul, hg0, ggPhiTwoConj_entrywiseHom_canonicalRep Fr v,
    mul_assoc, hcomm, ← mul_assoc]

theorem phiTwoComp_mul_canonicalRep
    {τ : Tag} {K : Type} [Field K] (g0 : ModGL τ (AlgebraicClosure K))
    (v : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    phiTwoComp (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) γ =
      phiTwoComp g0 (v • γ) := by
  have hS : ∀ δ ∈ ({γ, -γ} : Set (Fin τ.rank → ℤ)), IsRoot τ δ := by
    intro δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl
    · exact hγ
    · exact IsRoot.neg hγ
  have hmap :
      (rootSpan τ (AlgebraicClosure K) ({γ, -γ} : Set (Fin τ.rank → ℤ))).map
          (MulAut.conj (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)).toMonoidHom =
        rootSpan τ (AlgebraicClosure K) ({v • γ, -(v • γ)} : Set (Fin τ.rank → ℤ)) := by
    have h := CFSG.RankThree.PartOne.KE.map_conj_rootSpan (L := AlgebraicClosure K)
      (v := v) (S := ({γ, -γ} : Set (Fin τ.rank → ℤ))) hS
    rw [Set.image_pair, smul_neg] at h
    simpa using h
  ext x
  rw [mem_phiTwoComp_iff, mem_phiTwoComp_iff]
  rw [show (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) =
        (MulAut.conj (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)).symm
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0) from by
      rw [MulAut.conj_symm_apply]; group]
  rw [← hmap, Subgroup.mem_map_equiv]

theorem iSup_phiTwoComp_mul_canonicalRep
    {τ : Tag} {K : Type} [Field K] (g0 : ModGL τ (AlgebraicClosure K))
    (v : WeylGroup τ) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
        phiTwoComp (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) γ.1) =
      ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1 := by
  have hstep : ∀ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
      phiTwoComp (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) γ.1 =
        phiTwoComp g0 (v • γ.1) :=
    fun γ => phiTwoComp_mul_canonicalRep g0 v γ.2
  simp_rw [hstep]
  let e : {γ : Fin τ.rank → ℤ // IsRoot τ γ} ≃ {γ : Fin τ.rank → ℤ // IsRoot τ γ} :=
    MulAction.toPerm v
  have hfun : (fun γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ} => phiTwoComp g0 (v • γ.1)) =
      fun γ => phiTwoComp g0 (e γ).1 := by
    funext γ
    simp [e]
  rw [hfun]
  exact Equiv.iSup_comp
    (g := fun y : {γ : Fin τ.rank → ℤ // IsRoot τ γ} => phiTwoComp g0 y.1) e

theorem phiTwoComp_baseChange_mul
    {τ : Tag} {K : Type} [Field K] (h : adjointGroup τ K) (g0 : ModGL τ (AlgebraicClosure K))
    (γ : Fin τ.rank → ℤ) :
    phiTwoComp (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * g0) γ =
      (phiTwoComp g0 γ).map (MulAut.conj h).toMonoidHom := by
  ext x
  rw [mem_phiTwoComp_iff]
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_phiTwoComp_iff]
  rw [show (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * g0)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * g0) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (↑(h⁻¹ * x * h) : ModGL τ K) * g0 from by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      group]

theorem iSup_phiTwoComp_baseChange_mul
    {τ : Tag} {K : Type} [Field K] (h : adjointGroup τ K) (g0 : ModGL τ (AlgebraicClosure K)) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
        phiTwoComp (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * g0) γ.1) =
      (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1).map
        (MulAut.conj h).toMonoidHom := by
  rw [Subgroup.map_iSup]
  exact iSup_congr fun γ => phiTwoComp_baseChange_mul h g0 γ.1

end CFSG.StandardType.PhiTwoRootGen

end
