module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaMixGen
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaMixCrux
import CFSG.LieType.SeitzGeneration.RootPairOrthModel
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)

section PlaneGen

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
private lemma eichler_neg_neg (u w : Fin d → K) :
    eichler Q (-u) (-w) = eichler Q u w := by
  simpa using (eichler_smul_left (Q := Q) (-1) u (-w))

omit [Finite K] in
private lemma matrixProjectiveConjugationHom_apply_eq_of_commute (g : similarityPairs Q)
    (X : matrixDerived Q)
    (h : ∀ v, coordinateSemilinearMap g.val (matrixLinearIso (X : GL (Fin d) K) v) =
      matrixLinearIso (X : GL (Fin d) K) (coordinateSemilinearMap g.val v)) :
    matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q X) =
      matrixProjectiveProjection Q X := by
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q X) = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  change matrixConjugation g.val (X : GL (Fin d) K) = X
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro v
  change matrixLinearEquiv (matrixConjugation g.val (X : GL (Fin d) K)) v = _
  rw [matrixConjugation_vector]
  have hv := h ((coordinateSemilinearMap g.val).symm v)
  rw [AddEquiv.apply_symm_apply] at hv
  exact hv

private lemma finrank_le_four_of_no_singular_zero
    (Bm : (Fin d → K) →ₗ[K] (Fin d → K)) {W : Submodule K (Fin d → K)}
    (hzero : ∀ v ∈ W, Q v = 0 → polar Q v (Bm v) = 0 → v = 0) :
    Module.finrank K W ≤ 4 := by
  by_contra hle
  rw [not_le] at hle
  let q1 : QuadraticForm K W := Q.comp W.subtype
  let q2 : QuadraticForm K W :=
    ((LinearMap.BilinForm.compRight (polarBilin Q) Bm).toQuadraticMap).comp W.subtype
  have hq1 : ∀ v : W, q1 v = Q (v : Fin d → K) := fun v => rfl
  have hq2 : ∀ v : W, q2 v = polar Q (v : Fin d → K) (Bm (v : Fin d → K)) := by
    intro v
    simp only [q2, QuadraticMap.comp_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      LinearMap.BilinForm.compRight_apply, QuadraticMap.polarBilin_apply_apply,
      Submodule.coe_subtype]
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
      (fun i : Fin 2 => ![q1, q2] i) (by omega)
  have hv1 : Q (v : Fin d → K) = 0 := by
    have h := hv 0
    simpa [hq1] using h
  have hv2 : polar Q (v : Fin d → K) (Bm (v : Fin d → K)) = 0 := by
    have h := hv 1
    simpa [hq2] using h
  exact hv0 (Subtype.ext (hzero _ v.2 hv1 hv2))

theorem planeGen_of_mixed_lifts (h2 : (2 : K) ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (hd : 7 ≤ d) (hder : elementaryGroup Q = orthDerived Q)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))} (ga gb : similarityPairs Q)
    (hga : matrixProjectiveConjugationHom Q ga ∈ E) (hgb : matrixProjectiveConjugationHom Q gb ∈ E)
    (hga1 : matrixProjectiveConjugationHom Q ga ≠ 1)
    (hgb1 : matrixProjectiveConjugationHom Q gb ≠ 1)
    (hra : ga.val.right = 1) (hrb : gb.val.right = 1) {a β : K} (ha : a ≠ 0)
    (hβ : ∀ s : K, s * s ≠ β)
    (hA2 : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) = (a * a) • v)
    (hB2 : ∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) = β • v)
    (hAsa : ∀ u w, polar Q (coordinateSemilinearMap ga.val u) w =
      polar Q u (coordinateSemilinearMap ga.val w))
    (hBsa : ∀ u w, polar Q (coordinateSemilinearMap gb.val u) w =
      polar Q u (coordinateSemilinearMap gb.val w))
    (hAB : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) =
      coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v))
    (hanis : ∀ v, (coordinateSemilinearMap ga.val v = a • v ∨
        coordinateSemilinearMap ga.val v = -(a • v)) →
      Q v = 0 → polar Q v (coordinateSemilinearMap gb.val v) = 0 → v = 0) :
    PlaneGen E := by
  classical
  have hra' : ∀ x : K, ga.val.right x = x := by
    intro x
    rw [hra]
    rfl
  have hrb' : ∀ x : K, gb.val.right x = x := by
    intro x
    rw [hrb]
    rfl
  have hσa_eq : ∀ v, coordinateSemilinearMap ga.val v = matrixLinearEquiv ga.val.left v := by
    intro v
    rw [coordinateSemilinearMap_apply, matrixLinearEquiv_apply, hra]
    congr 1
  have hσb_eq : ∀ v, coordinateSemilinearMap gb.val v = matrixLinearEquiv gb.val.left v := by
    intro v
    rw [coordinateSemilinearMap_apply, matrixLinearEquiv_apply, hrb]
    congr 1
  let σa : (Fin d → K) →ₗ[K] (Fin d → K) := (matrixLinearEquiv ga.val.left).toLinearMap
  let σb : (Fin d → K) →ₗ[K] (Fin d → K) := (matrixLinearEquiv gb.val.left).toLinearMap
  have hσa_coe : ∀ v, σa v = coordinateSemilinearMap ga.val v := by
    intro v
    show matrixLinearEquiv ga.val.left v = coordinateSemilinearMap ga.val v
    exact (hσa_eq v).symm
  have hσb_coe : ∀ v, σb v = coordinateSemilinearMap gb.val v := by
    intro v
    show matrixLinearEquiv gb.val.left v = coordinateSemilinearMap gb.val v
    exact (hσb_eq v).symm
  let A : (Fin d → K) →ₗ[K] (Fin d → K) := a⁻¹ • σa
  let Bm : (Fin d → K) →ₗ[K] (Fin d → K) := σb
  have hA_apply : ∀ v, A v = a⁻¹ • σa v := fun v => rfl
  have hBm_apply : ∀ v, Bm v = coordinateSemilinearMap gb.val v := hσb_coe
  have hσa_smul : ∀ v, coordinateSemilinearMap ga.val v = a • A v := by
    intro v
    rw [hA_apply v, smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact (hσa_coe v).symm
  have hA2σ : ∀ v, σa (σa v) = (a * a) • v := by
    intro v
    simpa only [hσa_coe] using hA2 v
  have hB2σ : ∀ v, σb (σb v) = β • v := by
    intro v
    simpa only [hσb_coe] using hB2 v
  have hAsaσ : ∀ u w, polar Q (σa u) w = polar Q u (σa w) := by
    intro u w
    simpa only [hσa_coe] using hAsa u w
  have hBsaσ : ∀ u w, polar Q (σb u) w = polar Q u (σb w) := by
    intro u w
    simpa only [hσb_coe] using hBsa u w
  have hABσ : ∀ v, σa (σb v) = σb (σa v) := by
    intro v
    simpa only [hσa_coe, hσb_coe] using hAB v
  have hA2' : ∀ v, A (A v) = v := by
    intro v
    calc A (A v) = A (a⁻¹ • σa v) := by rw [hA_apply v]
      _ = a⁻¹ • A (σa v) := by rw [map_smul]
      _ = a⁻¹ • (a⁻¹ • σa (σa v)) := by rw [hA_apply]
      _ = a⁻¹ • (a⁻¹ • ((a * a) • v)) := by rw [hA2σ]
      _ = v := by
            rw [smul_smul, smul_smul]
            have hcoef : (a⁻¹ * a⁻¹) * (a * a) = 1 := by field_simp
            rw [hcoef, one_smul]
  have hAsaA : ∀ u w, polar Q (A u) w = polar Q u (A w) := by
    intro u w
    rw [hA_apply u, hA_apply w, polar_smul_left_eq, polar_smul_right_eq, hAsaσ]
  have hAQ : ∀ v, Q (A v) = Q v := by
    intro v
    have hp : polar Q (A v) (A v) = polar Q v v := by
      rw [hAsaA v (A v), hA2' v]
    rw [polar_self_eq_two_mul, polar_self_eq_two_mul] at hp
    exact mul_left_cancel₀ h2 hp
  have hB2' : ∀ v, Bm (Bm v) = β • v := hB2σ
  have hBsa' : ∀ u w, polar Q (Bm u) w = polar Q u (Bm w) := hBsaσ
  have hAB' : ∀ v, A (Bm v) = Bm (A v) := by
    intro v
    calc A (Bm v) = a⁻¹ • σa (σb v) := by rw [hA_apply]
      _ = a⁻¹ • σb (σa v) := by rw [hABσ]
      _ = Bm (a⁻¹ • σa v) := by rw [map_smul]
      _ = Bm (A v) := by rw [hA_apply]
  let Ae : (Fin d → K) ≃ₗ[K] (Fin d → K) := LinearEquiv.ofInvolutive A hA2'
  have hAe_apply : ∀ v, Ae v = A v := fun v => rfl
  have hAe_sq : Ae * Ae = 1 := by
    apply LinearEquiv.ext
    intro v
    change Ae (Ae v) = v
    rw [hAe_apply, hAe_apply, hA2' v]
  have hAe_inv : Ae⁻¹ = Ae := inv_eq_of_mul_eq_one_right hAe_sq
  have hAe_orth : Ae ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hAQ
  let Vp : Submodule K (Fin d → K) := LinearMap.ker (A - 1)
  let Vm : Submodule K (Fin d → K) := LinearMap.ker (A + 1)
  have hVp : ∀ v, v ∈ Vp ↔ A v = v := by
    intro v
    change (A - 1) v = 0 ↔ A v = v
    exact sub_eq_zero
  have hVm : ∀ v, v ∈ Vm ↔ A v = -v := by
    intro v
    change (A + 1) v = 0 ↔ A v = -v
    exact add_eq_zero_iff_eq_neg
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot K]
    obtain ⟨hvp, hvm⟩ := Submodule.mem_inf.mp hv
    have h1 : A v = v := (hVp v).mp hvp
    have h2' : A v = -v := (hVm v).mp hvm
    have h3 : v = -v := h1.symm.trans h2'
    have h4 : v + v = 0 := by
      have := congrArg (fun w => w + v) h3
      rwa [neg_add_cancel] at this
    have h5 : (2 : K) • v = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h5).resolve_left h2
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hp : (2 : K)⁻¹ • (v + A v) ∈ Vp := by
      rw [hVp, map_smul, map_add, hA2', add_comm]
    have hm : (2 : K)⁻¹ • (v - A v) ∈ Vm := by
      rw [hVm, map_smul, map_sub, hA2']
      rw [smul_sub, smul_sub, neg_sub]
    have hsum : (2 : K)⁻¹ • (v + A v) + (2 : K)⁻¹ • (v - A v) = v := by
      rw [← smul_add]
      have h2v : (v + A v) + (v - A v) = (2 : K) • v := by
        rw [two_smul]
        abel
      rw [h2v, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hsum]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hm)
  have hc : IsCompl Vp Vm :=
    isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  have horth : ∀ x ∈ Vp, ∀ y ∈ Vm, polar Q x y = 0 := by
    intro x hx y hy
    have hx' : A x = x := (hVp x).mp hx
    have hy' : A y = -y := (hVm y).mp hy
    have h1 : polar Q x y = -polar Q x y := by
      calc polar Q x y = polar Q (A x) y := by rw [hx']
        _ = polar Q x (A y) := hAsaA x y
        _ = polar Q x (-y) := by rw [hy']
        _ = -polar Q x y := by rw [polar_neg_right]
    have h2' : polar Q x y + polar Q x y = 0 := by
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    have h3 : (2 : K) * polar Q x y = 0 := by rwa [two_mul]
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hzeroP : ∀ v ∈ Vp, Q v = 0 → polar Q v (Bm v) = 0 → v = 0 := by
    intro v hv hQv hBv
    have hAv : A v = v := (hVp v).mp hv
    have hσv : coordinateSemilinearMap ga.val v = a • v := by
      rw [hσa_smul v, hAv]
    rw [hBm_apply v] at hBv
    exact hanis v (Or.inl hσv) hQv hBv
  have hzeroM : ∀ v ∈ Vm, Q v = 0 → polar Q v (Bm v) = 0 → v = 0 := by
    intro v hv hQv hBv
    have hAv : A v = -v := (hVm v).mp hv
    have hσv : coordinateSemilinearMap ga.val v = -(a • v) := by
      rw [hσa_smul v, hAv, smul_neg]
    rw [hBm_apply v] at hBv
    exact hanis v (Or.inr hσv) hQv hBv
  have hdimV : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hrank : Module.finrank K Vp + Module.finrank K Vm = d := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rwa [hdimV] at h
  have hp4 : Module.finrank K Vp ≤ 4 :=
    finrank_le_four_of_no_singular_zero Bm hzeroP
  have hm4 : Module.finrank K Vm ≤ 4 :=
    finrank_le_four_of_no_singular_zero Bm hzeroM
  have hp3 : 3 ≤ Module.finrank K Vp := by omega
  have hm3 : 3 ≤ Module.finrank K Vm := by omega
  have hHA : ∀ x ∈ elementaryGroup Q, (∀ v, x (A v) = A (x v)) →
      x ∈ RootPairOrth.liftSubgroup Q (planeClosure E) := by
    intro x hx hcomm
    have hx' : x ∈ orthDerived Q := hder ▸ hx
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q] at hx'
    obtain ⟨X, hX, hXe⟩ := Subgroup.mem_map.mp hx'
    have hXe' : ∀ v, matrixLinearIso (X : GL (Fin d) K) v = x v := by
      intro v
      simpa using congrArg (fun f : (Fin d → K) ≃ₗ[K] (Fin d → K) => f v) hXe
    have hfix : matrixProjectiveConjugationHom Q ga (matrixProjectiveProjection Q ⟨X, hX⟩) =
        matrixProjectiveProjection Q ⟨X, hX⟩ := by
      apply matrixProjectiveConjugationHom_apply_eq_of_commute ga ⟨X, hX⟩
      intro v
      calc coordinateSemilinearMap ga.val (matrixLinearIso (X : GL (Fin d) K) v)
          = a • A (matrixLinearIso (X : GL (Fin d) K) v) := hσa_smul _
        _ = a • A (x v) := by rw [hXe' v]
        _ = a • x (A v) := by rw [hcomm v]
        _ = x (a • A v) := by rw [map_smul]
        _ = x (coordinateSemilinearMap ga.val v) := by rw [hσa_smul v]
        _ = matrixLinearIso (X : GL (Fin d) K) (coordinateSemilinearMap ga.val v) := by
              rw [← hXe' (coordinateSemilinearMap ga.val v)]
    exact RootPairOrth.mem_liftSubgroup.mpr
      ⟨⟨X, hX⟩, mem_planeClosure_of_fixed hga hga1 hfix, hXe⟩
  have hHB : ∀ x ∈ elementaryGroup Q, (∀ v, x (Bm v) = Bm (x v)) →
      x ∈ RootPairOrth.liftSubgroup Q (planeClosure E) := by
    intro x hx hcomm
    have hx' : x ∈ orthDerived Q := hder ▸ hx
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q] at hx'
    obtain ⟨X, hX, hXe⟩ := Subgroup.mem_map.mp hx'
    have hXe' : ∀ v, matrixLinearIso (X : GL (Fin d) K) v = x v := by
      intro v
      simpa using congrArg (fun f : (Fin d → K) ≃ₗ[K] (Fin d → K) => f v) hXe
    have hfix : matrixProjectiveConjugationHom Q gb (matrixProjectiveProjection Q ⟨X, hX⟩) =
        matrixProjectiveProjection Q ⟨X, hX⟩ := by
      apply matrixProjectiveConjugationHom_apply_eq_of_commute gb ⟨X, hX⟩
      intro v
      calc coordinateSemilinearMap gb.val (matrixLinearIso (X : GL (Fin d) K) v)
          = σb (matrixLinearIso (X : GL (Fin d) K) v) := (hσb_coe _).symm
        _ = σb (x v) := by rw [hXe' v]
        _ = Bm (x v) := rfl
        _ = x (Bm v) := (hcomm v).symm
        _ = x (σb v) := rfl
        _ = x (coordinateSemilinearMap gb.val v) := by rw [hσb_coe]
        _ = matrixLinearIso (X : GL (Fin d) K) (coordinateSemilinearMap gb.val v) := by
              rw [← hXe' (coordinateSemilinearMap gb.val v)]
    exact RootPairOrth.mem_liftSubgroup.mpr
      ⟨⟨X, hX⟩, mem_planeClosure_of_fixed hgb hgb1 hfix, hXe⟩
  have hHp : ∀ u ∈ Vp, ∀ w ∈ Vp, Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ RootPairOrth.liftSubgroup Q (planeClosure E) := by
    intro u hu w hw hQu hpu
    have huA : Ae u = u := ((hAe_apply u).trans ((hVp u).mp hu))
    have hwA : Ae w = w := ((hAe_apply w).trans ((hVp w).mp hw))
    have hconj := eichler_conj (Q := Q) hAe_orth u w
    rw [hAe_inv, huA, hwA] at hconj
    have hEA : eichler Q u w * Ae = Ae * eichler Q u w := by
      calc eichler Q u w * Ae = (Ae * eichler Q u w * Ae) * Ae := by rw [hconj]
        _ = Ae * eichler Q u w * (Ae * Ae) := by group
        _ = Ae * eichler Q u w := by rw [hAe_sq, mul_one]
    have hcommA : ∀ v, eichler Q u w (A v) = A (eichler Q u w v) := by
      intro v
      have h := congrArg (fun f : (Fin d → K) ≃ₗ[K] (Fin d → K) => f v) hEA
      simpa [LinearEquiv.mul_apply, hAe_apply] using h
    exact hHA _ (eichler_mem_elementaryGroup Q u w) hcommA
  have hHm : ∀ u ∈ Vm, ∀ w ∈ Vm, Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ RootPairOrth.liftSubgroup Q (planeClosure E) := by
    intro u hu w hw hQu hpu
    have huA : Ae u = -u := ((hAe_apply u).trans ((hVm u).mp hu))
    have hwA : Ae w = -w := ((hAe_apply w).trans ((hVm w).mp hw))
    have hconj := eichler_conj (Q := Q) hAe_orth u w
    rw [hAe_inv, huA, hwA, eichler_neg_neg] at hconj
    have hEA : eichler Q u w * Ae = Ae * eichler Q u w := by
      calc eichler Q u w * Ae = (Ae * eichler Q u w * Ae) * Ae := by rw [hconj]
        _ = Ae * eichler Q u w * (Ae * Ae) := by group
        _ = Ae * eichler Q u w := by rw [hAe_sq, mul_one]
    have hcommA : ∀ v, eichler Q u w (A v) = A (eichler Q u w v) := by
      intro v
      have h := congrArg (fun f : (Fin d → K) ≃ₗ[K] (Fin d → K) => f v) hEA
      simpa [LinearEquiv.mul_apply, hAe_apply] using h
    exact hHA _ (eichler_mem_elementaryGroup Q u w) hcommA
  obtain ⟨e, he, w₀, hw, he0, heQ, hw0, hew⟩ :=
    exists_mixed_root (H := RootPairOrth.liftSubgroup Q (planeClosure E)) h2 hnd (by rwa [hdimV])
      hA2' hAQ hβ hB2' hBsa' hAB' hVp hVm hp3 hm3
      (fun v hv => by
        rcases hv with hv | hv
        · exact hzeroP v hv
        · exact hzeroM v hv)
      hHA hHB
  have hHle : RootPairOrth.liftSubgroup Q (planeClosure E) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    RootPairOrth.liftSubgroup_le_orthogonalGroup (planeClosure E)
  have hgen : elementaryGroup Q ≤ RootPairOrth.liftSubgroup Q (planeClosure E) :=
    elementaryGroup_le_of_mixed_root h2 hnd hc horth hp3 hm3 hHle hHp hHm
      he he0 heQ hw hw0 hew
  exact RootPairOrth.eq_top_of_elementaryGroup_le hder hgen

end PlaneGen

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
