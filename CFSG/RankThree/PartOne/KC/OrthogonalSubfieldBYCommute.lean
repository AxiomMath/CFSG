module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open scoped commutatorElement
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Commutation

theorem comm_mul_central_left {G : Type*} [Group G] {s : G} (hs : s ∈ Subgroup.center G)
    (g h : G) : ⁅g * s, h⁆ = ⁅g, h⁆ := by
  have hs' : ∀ x, s * x = x * s := fun x => (Subgroup.mem_center_iff.mp hs x).symm
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc g * s * h * (s⁻¹ * g⁻¹) * h⁻¹ = g * (s * h) * s⁻¹ * g⁻¹ * h⁻¹ := by group
    _ = g * (h * s) * s⁻¹ * g⁻¹ * h⁻¹ := by rw [hs' h]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem comm_mul_central_right {G : Type*} [Group G] {t : G} (ht : t ∈ Subgroup.center G)
    (g h : G) : ⁅g, h * t⁆ = ⁅g, h⁆ := by
  have ht' : ∀ x, t * x = x * t := fun x => (Subgroup.mem_center_iff.mp ht x).symm
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc g * (h * t) * g⁻¹ * (t⁻¹ * h⁻¹) = g * h * (t * g⁻¹) * t⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * t) * t⁻¹ * h⁻¹ := by rw [ht' g⁻¹]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem comm_mul_central {G : Type*} [Group G] {s t : G} (hs : s ∈ Subgroup.center G)
    (ht : t ∈ Subgroup.center G) (g h : G) : ⁅g * s, h * t⁆ = ⁅g, h⁆ := by
  rw [comm_mul_central_right ht, comm_mul_central_left hs]

end Commutation


section Exact

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem matrixDerived_commutator_eq (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) :
    ⁅matrixDerived Q₀, matrixDerived Q₀⁆ = matrixDerived Q₀ := by
  obtain ⟨hperf, -⟩ := CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
    hnd₀ hT₀
  have h1 : ⁅CFSG.RankThree.Classical2.orthDerived Q₀, CFSG.RankThree.Classical2.orthDerived Q₀⁆ =
      CFSG.RankThree.Classical2.orthDerived Q₀ := Subgroup.isPerfect_iff.mp hperf
  apply Subgroup.map_injective (f := (matrixLinearIso (d := d) (K := k)).toMonoidHom)
    (matrixLinearIso (d := d) (K := k)).injective
  rw [Subgroup.map_commutator, KCOrthogonalAut.map_matrixDerived, h1]

theorem exact_commutation (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (g : similarityPairs Q)
    (hfix : ∀ t ∈ subfieldDerivedImage k hext, matrixProjectiveConjugationHom Q g t = t)
    {x : GL (Fin d) k} (hx : x ∈ matrixDerived Q₀) :
    matrixConjugation g.val (glIncl k x) = glIncl k x := by
  have hcen : ∀ y ∈ matrixDerived Q₀, ∃ c : Kˣ, matrixConjugation g.val (glIncl k y) =
      glIncl k y * GeneralLinearGroup.scalar (Fin d) c := by
    intro y hy
    have h := hfix _ ⟨matrixProjectiveProjection Q₀ ⟨y, hy⟩, rfl⟩
    rw [incl_mk] at h
    change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q (inclHom k hext ⟨y, hy⟩))
      = matrixProjectiveProjection Q (inclHom k hext ⟨y, hy⟩) at h
    rw [matrixProjectiveConjugation_mk] at h
    rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp (QuotientGroup.eq.mp h.symm)
    refine ⟨c, ?_⟩
    have e1 : (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) =
        (glIncl k y)⁻¹ * matrixConjugation g.val (glIncl k y) := hc
    rw [e1]
    group
  let C : GL (Fin d) K →* GL (Fin d) K := (matrixConjugation g.val).toMonoidHom
  let S : Subgroup (GL (Fin d) k) := MonoidHom.eqLocus (C.comp (glIncl k)) (glIncl k)
  have hS : matrixDerived Q₀ ≤ S := by
    rw [← matrixDerived_commutator_eq hnd₀ hT₀]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨ca, hca⟩ := hcen a ha
    obtain ⟨cb, hcb⟩ := hcen b hb
    show C (glIncl k ⁅a, b⁆) = glIncl k ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have hca' : C (glIncl k a) = glIncl k a * GeneralLinearGroup.scalar (Fin d) ca := hca
    have hcb' : C (glIncl k b) = glIncl k b * GeneralLinearGroup.scalar (Fin d) cb := hcb
    have hcz : ∀ c : Kˣ, (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) ∈
        Subgroup.center (GL (Fin d) K) := fun c => by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [hca', hcb', comm_mul_central (hcz ca) (hcz cb) _ _]
  exact hS hx

end Exact


section Eichler

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem vecIncl_smul (c : k) (v : Fin d → k) : vecIncl k (c • v) = (c : K) • vecIncl k v := by
  funext i
  simp [vecIncl]

theorem vecIncl_sub (v w : Fin d → k) : vecIncl k (v - w) = vecIncl k v - vecIncl k w := by
  funext i
  simp [vecIncl]

theorem eichler_vecIncl (hext : IsExtension k Q₀ Q) {u w : Fin d → k} (hu : Q₀ u = 0)
    (huw : polar Q₀ u w = 0) (v : Fin d → k) :
    eichler Q (vecIncl k u) (vecIncl k w) (vecIncl k v) = vecIncl k (eichler Q₀ u w v) := by
  have hu' : Q (vecIncl k u) = 0 := by rw [hext, hu]; rfl
  have huw' : polar Q (vecIncl k u) (vecIncl k w) = 0 := by
    rw [polar_vecIncl k hext, huw]
    rfl
  have hQw : Q (vecIncl k w) = ((Q₀ w : k) : K) := hext w
  have h1 : polar Q (vecIncl k v) (vecIncl k u) = ((polar Q₀ v u : k) : K) :=
    polar_vecIncl k hext v u
  have h2 : polar Q (vecIncl k v) (vecIncl k w) = ((polar Q₀ v w : k) : K) :=
    polar_vecIncl k hext v w
  rw [eichler_apply hu' huw', eichler_apply hu huw, hQw, h1, h2]
  funext i
  simp [vecIncl]

end Eichler


section Commute

open CFSG.RankThree.Classical (orthDerived_eq_and_le_closure)

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
theorem matrixLinearEquiv_glIncl_eichler (hext : IsExtension k Q₀ Q) {u w : Fin d → k}
    (hu : Q₀ u = 0) (huw : polar Q₀ u w = 0) {x : GL (Fin d) k}
    (hx : matrixLinearIso x = eichler Q₀ u w) :
    matrixLinearEquiv (glIncl k x) = eichler Q (vecIncl k u) (vecIncl k w) := by
  apply linearEquiv_ext_vecIncl k
  intro v
  rw [matrixLinearEquiv_apply, mulVec_vecIncl, eichler_vecIncl hext hu huw]
  congr 1
  have := congrArg (fun F => F v) hx
  simpa [KCOrthogonalAut.matrixLinearIso_apply] using this

theorem commute_eichler (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (g : similarityPairs Q)
    (hfix : ∀ t ∈ subfieldDerivedImage k hext, matrixProjectiveConjugationHom Q g t = t)
    {u w : Fin d → k} (hu : Q₀ u = 0) (huw : polar Q₀ u w = 0) (v : Fin d → K) :
    coordinateSemilinearMap g.val (eichler Q (vecIncl k u) (vecIncl k w) v) =
      eichler Q (vecIncl k u) (vecIncl k w) (coordinateSemilinearMap g.val v) := by
  have hmem : eichler Q₀ u w ∈ orthDerived Q₀ := by
    rw [(orthDerived_eq_and_le_closure hnd₀ hT₀).1]
    exact eichler_mem_elementaryGroup _ _ _
  obtain ⟨x, hxd⟩ := KCOrthogonalAut.exists_matrixDerived Q₀ ⟨_, hmem⟩
  have hcomm := exact_commutation hext hnd₀ hT₀ g hfix x.2
  have hR := matrixLinearEquiv_glIncl_eichler hext hu huw hxd.symm
  rw [← hR]
  have hcomm' : g.val.left * glFieldAut (Fin d) K g.val.right (glIncl k x.val) =
      glIncl k x.val * g.val.left := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact hcomm
  change matrixLinearEquiv g.val.left (coordinateFieldMap d g.val.right
      (matrixLinearEquiv (glIncl k x.val) v)) =
    matrixLinearEquiv (glIncl k x.val) (matrixLinearEquiv g.val.left
      (coordinateFieldMap d g.val.right v))
  rw [coordinateFieldMap_matrix, ← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hcomm',
    matrixLinearEquiv_mul, LinearEquiv.mul_apply]

end Commute

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
