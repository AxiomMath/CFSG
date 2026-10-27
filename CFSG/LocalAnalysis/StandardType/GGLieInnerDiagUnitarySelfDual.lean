module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAUnitaryBridge
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitary
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
import CFSG.HardMathSupport.Dickson.Sec6.I1431
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem ltunisd_specialBlockEquiv_symm_sesqSUConj
    {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    (a : primaryFactors (x : Module.End K (Fin n → K))) (hq : 2 ≤ ℓ ^ f)
    (ha : IsGoodBlock h x a) {e : ℕ}
    {hE : UnitaryFieldData ℓ (f * e) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    {Y : primeFormUnitary h (idGram K n)}
    {Φ : ↥(specialBlock (idForm h n) x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)}
    (hΦ : ∀ (s : ↥(specialBlock (idForm h n) x (a : K[X]))) (v : Fin n → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])),
      blockApply (Φ s : blockGL (x : Module.End K (Fin n → K)) (a : K[X])) v hv =
        ((s : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) v)
    {g : ↥(sesqUnitaryGroup Hf)}
    (hm : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) ∈
      unitaryCentralizer (idForm h n) x)
    (hg : ∀ (v : Fin n → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])),
      blockApply g v hv =
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) : Module.End K (Fin n → K)) v)
    (u : ↥(unitaryPreimageBlock h (x := x) (a : K[X])))
    (hYmem : primeFormConjSU h (idGram K n) Y u ∈
      unitaryPreimageBlock h (x := x) (a : K[X])) :
    (specialBlockEquiv h H a hq ha).symm
      (Φ.symm (sesqSUConj g (Φ (specialBlockEquiv h H a hq ha u)))) =
      (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
  classical
  let ε := specialBlockEquiv h H a hq ha
  let w : ↥(specialBlock (idForm h n) x (a : K[X])) :=
    ⟨Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) *
      ((ε u : ↥(specialBlock (idForm h n) x (a : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) *
      (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))⁻¹,
      conj_mem_specialBlock hm (ε u).2⟩
  have hU2 := blockApply_conj_specialBlock (B := idForm h n) (x := x) (a := a)
    (G := sesqSpecialUnitaryGroup Hf) (Φ := Φ) hΦ hm hg (ε u)
  have hU2' : Φ w = sesqSUConj g (Φ (ε u)) := by
    apply Subtype.ext
    rw [sesqSUConj_apply]
    exact hU2
  have hεw : ε (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
      ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) = w := by
    apply Subtype.ext
    rw [specialBlockEquiv_apply_coe, toLinSU_primeFormConjSU,
      ← specialBlockEquiv_apply_coe h H a hq ha u]
  calc ε.symm (Φ.symm (sesqSUConj g (Φ (ε u))))
      = ε.symm (Φ.symm (Φ w)) := by rw [← hU2']
    _ = ε.symm w := by rw [Φ.symm_apply_apply]
    _ = (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
      rw [← hεw, ε.symm_apply_apply]

theorem ggUnitaryOn_unitaryBlock_selfDual {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (A B : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA3 : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hAB : (A : GL (Fin n) K) * (B : GL (Fin n) K) = (B : GL (Fin n) K) * (A : GL (Fin n) K))
    (a : primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a)
    (hself : dualPoly h.bar (a : K[X]) = a)
    (hTq : CFSG.Open.IsQuasisimple ↥(unitaryBlockComponent h
      (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X])))
    (hstab : primeFormConjHom h (idGram K n) B ∈ CFSG.GroupActions.subgroupStabAut
      (unitaryBlockComponent h (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
        (a : K[X]))) :
    GGUnitaryOn (unitaryBlockComponent h
        (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X]))
      (primeFormConjHom h (idGram K n) B) := by
  classical
  have hH : UnitaryPrimaryData h.bar (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA3
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  have hS : SelfDualPrimaryBlock h (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a :=
    selfDualPrimaryBlock hH a hself
  have hU : Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) ∈
      sesqUnitaryGroup (idForm h n) :=
    (toLin_mem_sesqUnitaryGroup_iff (h := h) (n := n) (B : GL (Fin n) K)).mpr B.2
  have hcomm : Commute (Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) :
        Module.End K (Fin n → K))
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) := by
    have h1 := congrArg (fun T : GL (Fin n) K =>
      (Matrix.GeneralLinearGroup.toLin T : Module.End K (Fin n → K))) hAB
    simp only [map_mul, Units.val_mul] at h1
    exact h1.symm
  have hm : Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) ∈
      unitaryCentralizer (idForm h n)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    mem_unitaryCentralizer.mpr ⟨hU, hcomm⟩
  obtain ⟨hE, Hf, hHf, hHfl, Φ, hΦ, hisoG⟩ :=
    exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary (hK := h) hH hself hS
  obtain ⟨g, hg⟩ := hisoG (Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K)) hm
  let F := unitaryPreimageBlock h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X])
  let SB := specialBlock (idForm h n)
    (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X])
  let Comp := unitaryBlockComponent h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X])
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n)) F
  have hπF := subgroupMap_mk'_surjective_ker_le_center (h := h)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a
  let ε : ↥F ≃* ↥SB := specialBlockEquiv (h := h) hH a hq2 ha
  let π' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥Comp :=
    πF.comp (ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom)
  have hπ' : Function.Surjective π' :=
    hπF.1.comp (ε.symm.surjective.comp Φ.symm.surjective)
  have hker' : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup Hf) := by
    rw [← MonoidHom.comap_ker]
    refine (Subgroup.comap_mono hπF.2).trans ?_
    have hinj : Function.Injective
        ⇑(ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom) := by
      intro x y hxy
      exact Φ.symm.injective (ε.symm.injective hxy)
    exact Subgroup.comap_center_le_center hinj
  let γ : MulAut ↥Comp :=
    CFSG.GroupActions.subgroupStabRestrict Comp
      ⟨primeFormConjHom h (idGram K n) B, hstab⟩
  have hγ : ∀ s : ↥(sesqSpecialUnitaryGroup Hf), γ (π' s) = π' (sesqSUConj g s) := by
    intro s
    let u : ↥F := ε.symm (Φ.symm s)
    have hεu : ε u = Φ.symm s := ε.apply_symm_apply _
    have hΦu : Φ (ε u) = s := by simpa only [hεu] using Φ.apply_symm_apply s
    have hnorm := map_conj_specialBlock_eq_self (h := h) (H := hH) (a := a) hq2 ha hstab
    have hcBmem : primeFormConjSU h (idGram K n) B u ∈ F := by
      show toLinSU h n (primeFormConjSU h (idGram K n) B u) ∈ SB
      rw [toLinSU_primeFormConjSU]
      have h2 : toLinSU h n u ∈ SB := u.2
      have h4 := Subgroup.mem_map_of_mem (MulAut.conj
        (Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K))).toMonoidHom h2
      rwa [hnorm] at h4
    have hL : γ (π' s) = πF (⟨primeFormConjSU h (idGram K n) B u, hcBmem⟩ : ↥F) := by
      have hπ's : π' s = πF u := rfl
      rw [hπ's]
      apply Subtype.ext
      rw [CFSG.GroupActions.subgroupStabRestrict_apply]
      exact primeFormConjHom_mk h (idGram K n) B (u : ↥(gramSU h (idGram K n)))
    have hεsymm : ε.symm (Φ.symm (sesqSUConj g (Φ (ε u)))) =
        (⟨primeFormConjSU h (idGram K n) B u, hcBmem⟩ : ↥F) :=
      ltunisd_specialBlockEquiv_symm_sesqSUConj (h := h) (H := hH) (a := a)
        (e := (a : K[X]).natDegree) (hE := hE) (Hf := Hf) (Y := B) (Φ := Φ) (g := g)
        hq2 ha hΦ hm hg u hcBmem
    have hR : π' (sesqSUConj g s) =
        πF (⟨primeFormConjSU h (idGram K n) B u, hcBmem⟩ : ↥F) := by
      have hπ'c : π' (sesqSUConj g s) =
          πF (ε.symm (Φ.symm (sesqSUConj g s))) := rfl
      rw [hπ'c]
      have harg : ε.symm (Φ.symm (sesqSUConj g s)) =
          ε.symm (Φ.symm (sesqSUConj g (Φ (ε u)))) :=
        congrArg (fun t => ε.symm (Φ.symm (sesqSUConj g t))) hΦu.symm
      rw [harg, hεsymm]
    exact hL.trans hR.symm
  have hconj : ∀ s : ↥(sesqSpecialUnitaryGroup Hf),
      primeFormConjHom h (idGram K n) B (π' s) = π' (sesqSUConj g s) := by
    intro s
    have h := congrArg (fun z : ↥Comp => (z : primeFormP h (idGram K n))) (hγ s)
    rw [CFSG.GroupActions.subgroupStabRestrict_apply] at h
    exact h
  exact ggUnitaryOn_of_sesqSUConj (G := primeFormP h (idGram K n))
    (J := unitaryBlockComponent h
      (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X]))
    (t := primeFormConjHom h (idGram K n) B)
    (hE := hE) (B := Hf) hTq hHf hHfl π' hπ' hker' g hconj

end CFSG.StandardType.SCFourCover

end
