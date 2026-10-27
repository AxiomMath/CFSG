module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentral

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary

section Statement

variable {ℓ f : ℕ} {K : Type*} [Field K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
  (x : LinearMap.GeneralLinearGroup K V)

@[expose] def adjointOrbits : Set (Set K[X]) :=
  (fun a : K[X] => ({a, dualPoly hK.bar a} : Set K[X])) '' (primaryFactors (x : Module.End K V))

open scoped _root_.Classical in
@[expose] def IsPairedTransversal (P : Finset K[X]) : Prop :=
  (∀ a ∈ P, a ∈ primaryFactors (x : Module.End K V) ∧ a ≠ dualPoly hK.bar a) ∧
    (∀ a ∈ primaryFactors (x : Module.End K V), a ≠ dualPoly hK.bar a →
      a ∈ P ∨ dualPoly hK.bar a ∈ P) ∧
    (∀ a ∈ P, dualPoly hK.bar a ∉ P)


structure PairedPrimaryBlock (a : primaryFactors (x : Module.End K V)) : Prop where
  natDegree_eq : (a : K[X]).natDegree = (dualPoly hK.bar (a : K[X])).natDegree
  multiplicity_eq : primaryMultiplicity (x : Module.End K V) (a : K[X]) =
    primaryMultiplicity (x : Module.End K V) (dualPoly hK.bar (a : K[X]))
  isotropic_left : ∀ v ∈ primaryComponent (x : Module.End K V) (a : K[X]),
    ∀ w ∈ primaryComponent (x : Module.End K V) (a : K[X]), B v w = 0
  isotropic_right : ∀ v ∈ primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])),
    ∀ w ∈ primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])), B v w = 0
  nondegenerate_sum :
    (B.domRestrict₁₂ (primaryComponent (x : Module.End K V) (a : K[X]) ⊔
        primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])))
      (primaryComponent (x : Module.End K V) (a : K[X]) ⊔
        primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])))).SeparatingLeft
  factor : ∃ (φ : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} ≃*
      blockGL (x : Module.End K V) (a : K[X]))
    (ψ : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} ≃*
      Matrix.GeneralLinearGroup (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (AdjoinRoot (a : K[X]))),
    (∀ (g : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (φ g) v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∧
    (∀ (g : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) (v w : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X]))
      (_ : w ∈ primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X]))),
        B (blockApply (φ g) v hv) (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) =
          B v w) ∧
    (∀ g : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])},
      Matrix.det ((ψ g : Matrix.GeneralLinearGroup (Fin (primaryMultiplicity
        (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) :
          Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
            (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) =
        LinearMap.det ((φ g : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))) ∧
    (∀ g : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])},
      LinearMap.det ((φ g : blockGL (x : Module.End K V) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 →
          LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1)


structure SelfDualPrimaryBlock (a : primaryFactors (x : Module.End K V)) : Prop where
  odd_natDegree : Odd (a : K[X]).natDegree
  unitaryForm : ∃ hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])),
    (∀ z : AdjoinRoot (a : K[X]), hE.bar z = z ^ ((ℓ ^ f) ^ (a : K[X]).natDegree)) ∧
    (∀ (e : AdjoinRoot (a : K[X])) (v w : primaryComponent (x : Module.End K V) (a : K[X])),
      B ((e • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) (w : V) =
        B (v : V) ((hE.bar e • w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
    ∃ Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X]),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
      (∀ (v w : primaryComponent (x : Module.End K V) (a : K[X])) (b : AdjoinRoot (a : K[X])),
        Algebra.trace K (AdjoinRoot (a : K[X])) (b * Hf v w) =
          B (v : V) ((b • w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
      (∃ e : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
          (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])),
        ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) ∧
      ∃ φ : supportedUnitary B x {(a : K[X])} ≃* sesqUnitaryGroup Hf,
        (∀ (g : supportedUnitary B x {(a : K[X])}) (v : V)
          (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
            blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
              ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∧
        (∀ g : supportedUnitary B x {(a : K[X])},
          (φ g : blockGL (x : Module.End K V) (a : K[X])) ∈ sesqSpecialUnitaryGroup Hf →
            LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1)


open scoped _root_.Classical in
structure UnitaryPrimaryAlgebra : Prop where
  dual_mem : ∀ a ∈ primaryFactors (x : Module.End K V),
    dualPoly hK.bar a ∈ primaryFactors (x : Module.End K V)
  dual_dual : ∀ a ∈ primaryFactors (x : Module.End K V),
    dualPoly hK.bar (dualPoly hK.bar a) = a
  algebraEquiv : Nonempty (commutant (x : Module.End K V) ≃ₐ[K]
    ((a : primaryFactors (x : Module.End K V)) →
      Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))))
  primitiveCentral : ∀ r : commutant (x : Module.End K V),
    IsPrimitiveCentralIdempotent K r ↔
      ∃ a ∈ primaryFactors (x : Module.End K V),
        (r : Module.End K V) = primaryProjection (x : Module.End K V) a
  adjoint_primitiveCentral : ∀ a ∈ primaryFactors (x : Module.End K V),
    hermAdjoint hB hBl (primaryProjection (x : Module.End K V) a) =
      primaryProjection (x : Module.End K V) (dualPoly hK.bar a)
  paired : ∀ a : primaryFactors (x : Module.End K V), (a : K[X]) ≠ dualPoly hK.bar (a : K[X]) →
    PairedPrimaryBlock hK B x a
  selfDual : ∀ a : primaryFactors (x : Module.End K V), dualPoly hK.bar (a : K[X]) = a →
    SelfDualPrimaryBlock hK B x a
  directProduct :
    (∀ O ∈ adjointOrbits hK x, ∀ O' ∈ adjointOrbits hK x, O ≠ O' →
      ∀ g ∈ supportedUnitary B x O, ∀ g' ∈ supportedUnitary B x O', Commute g g') ∧
    iSupIndep (fun O : adjointOrbits hK x => supportedUnitary B x (O : Set K[X])) ∧
    (⨆ O : adjointOrbits hK x, supportedUnitary B x (O : Set K[X])) = unitaryCentralizer B x
  dimension : (∃ P : Finset K[X], IsPairedTransversal hK x P) ∧
    ∀ P : Finset K[X], IsPairedTransversal hK x P →
      Module.finrank K V =
        ∑ a ∈ P, 2 * ((a.natDegree) * primaryMultiplicity (x : Module.End K V) a) +
          ∑ a ∈ (primaryFactors (x : Module.End K V)).filter (fun a => dualPoly hK.bar a = a),
            a.natDegree * primaryMultiplicity (x : Module.End K V) a
  center_eq : ∀ z : commutant (x : Module.End K V),
    z ∈ Subalgebra.center K (commutant (x : Module.End K V)) ↔
      ∀ a : primaryFactors (x : Module.End K V), ∃ c : AdjoinRoot (a : K[X]),
        ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
          (z : Module.End K V) (v : V) =
            ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)
  center_group : ∀ g : LinearMap.GeneralLinearGroup K V,
    (g ∈ unitaryCentralizer B x ∧
      ∀ a : primaryFactors (x : Module.End K V), ∃ c : AdjoinRoot (a : K[X]),
        ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
          (g : Module.End K V) (v : V) =
            ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ↔
    (g ∈ sesqUnitaryGroup B ∧ ∃ hz : (g : Module.End K V) ∈ commutant (x : Module.End K V),
      (⟨(g : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
        Subalgebra.center K (commutant (x : Module.End K V)))


end Statement

section Proofs

variable {ℓ f : ℕ} {K : Type*} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)
include H

theorem adjointOrbits_eq_of_mem {a c : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hc : c ∈ ({a, dualPoly hK.bar a} : Set K[X])) :
    ({c, dualPoly hK.bar c} : Set K[X]) = {a, dualPoly hK.bar a} := by
  rcases hc with rfl | hc
  · rfl
  · rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [dualPoly_dualPoly_of_mem H ha, Set.pair_comm]

theorem adjointOrbits_disjoint {O O' : Set K[X]} (hO : O ∈ adjointOrbits hK x)
    (hO' : O' ∈ adjointOrbits hK x) (hne : O ≠ O') : Disjoint O O' := by
  obtain ⟨a, ha, rfl⟩ := hO
  obtain ⟨a', ha', rfl⟩ := hO'
  rw [Set.disjoint_left]
  intro c hc hc'
  apply hne
  exact (adjointOrbits_eq_of_mem H ha hc).symm.trans (adjointOrbits_eq_of_mem H ha' hc')


theorem natDegree_dualPoly_of_mem {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    (dualPoly hK.bar a).natDegree = a.natDegree :=
  natDegree_dualPoly (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha)

theorem primaryMultiplicity_dualPoly {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    primaryMultiplicity (x : Module.End K V) (dualPoly hK.bar a) =
      primaryMultiplicity (x : Module.End K V) a := by
  have hb := dualPoly_mem_primaryFactors H ha
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have : Fact (Irreducible (dualPoly hK.bar a)) := ⟨irreducible_of_mem_primaryFactors hb⟩
  have h1 := finrank_primaryComponent (x : Module.End K V) a
  have h2 := finrank_primaryComponent (x : Module.End K V) (dualPoly hK.bar a)
  rw [finrank_primaryComponent_dualPoly H ha, h1, natDegree_dualPoly_of_mem H ha] at h2
  have hd : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
  exact (Nat.eq_of_mul_eq_mul_left hd h2).symm

open scoped _root_.Classical in
theorem exists_isPairedTransversal : ∃ P : Finset K[X], IsPairedTransversal hK x P := by
  refine ⟨(primaryFactors (x : Module.End K V)).filter
    (fun a => a ≠ dualPoly hK.bar a ∧ WellOrderingRel a (dualPoly hK.bar a)), ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1, ha.2.1⟩
  · intro a ha hne
    rcases trichotomous_of WellOrderingRel a (dualPoly hK.bar a) with h | h | h
    · left
      simp only [Finset.mem_filter]
      exact ⟨ha, hne, h⟩
    · exact absurd h hne
    · right
      simp only [Finset.mem_filter]
      refine ⟨dualPoly_mem_primaryFactors H ha, ?_, ?_⟩
      · rw [dualPoly_dualPoly_of_mem H ha]; exact hne.symm
      · rw [dualPoly_dualPoly_of_mem H ha]; exact h
  · intro a ha hda
    simp only [Finset.mem_filter] at ha hda
    rw [dualPoly_dualPoly_of_mem H ha.1] at hda
    exact asymm_of WellOrderingRel ha.2.2 hda.2.2


open scoped _root_.Classical in
theorem finrank_eq_paired_sum {P : Finset K[X]} (hP : IsPairedTransversal hK x P) :
    Module.finrank K V =
      ∑ a ∈ P, 2 * (a.natDegree * primaryMultiplicity (x : Module.End K V) a) +
        ∑ a ∈ (primaryFactors (x : Module.End K V)).filter (fun a => dualPoly hK.bar a = a),
          a.natDegree * primaryMultiplicity (x : Module.End K V) a := by
  set Φ := primaryFactors (x : Module.End K V) with hΦ
  set F : K[X] → ℕ := fun a => a.natDegree * primaryMultiplicity (x : Module.End K V) a with hF
  have h1 : Module.finrank K V = ∑ a ∈ Φ, F a := by
    rw [finrank_eq_sum_degree_mul_multiplicity H.squarefree]
    exact Finset.sum_coe_sort Φ F
  have hFd : ∀ a ∈ Φ, F (dualPoly hK.bar a) = F a := fun a ha => by
    simp only [hF, natDegree_dualPoly_of_mem H ha, primaryMultiplicity_dualPoly H ha]
  have hPr : Φ.filter (fun a => ¬ dualPoly hK.bar a = a) =
      P ∪ P.image (dualPoly hK.bar) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨ha, hne⟩
      rcases hP.2.1 a ha (fun h => hne h.symm) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨dualPoly hK.bar a, h, dualPoly_dualPoly_of_mem H ha⟩
    · rintro (h | ⟨p, hp, rfl⟩)
      · exact ⟨(hP.1 a h).1, fun h' => (hP.1 a h).2 h'.symm⟩
      · refine ⟨dualPoly_mem_primaryFactors H (hP.1 p hp).1, ?_⟩
        rw [dualPoly_dualPoly_of_mem H (hP.1 p hp).1]
        exact (hP.1 p hp).2
  have hdisj : Disjoint P (P.image (dualPoly hK.bar)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha'
    exact hP.2.2 p hp ha
  rw [h1, ← Finset.sum_filter_add_sum_filter_not Φ (fun a => dualPoly hK.bar a = a), add_comm,
    hPr, Finset.sum_union hdisj, Finset.sum_image (fun a ha b hb h =>
      dualPoly_injOn H (hP.1 a ha).1 (hP.1 b hb).1 h), ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hFd a (hP.1 a ha).1]
  simp only [hF]
  ring


theorem pairedPrimaryBlock (a : primaryFactors (x : Module.End K V))
    (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X])) : PairedPrimaryBlock hK B x a := by
  have ha := a.2
  have hb := dualPoly_mem_primaryFactors H ha
  have hne' : dualPoly hK.bar (a : K[X]) ≠ dualPoly hK.bar (dualPoly hK.bar (a : K[X])) := by
    rw [dualPoly_dualPoly_of_mem H ha]; exact hne.symm
  refine ⟨(natDegree_dualPoly_of_mem H ha).symm,
    (primaryMultiplicity_dualPoly H ha).symm,
    fun v hv w hw => isotropic_primaryComponent H ha hne hv hw,
    fun v hv w hw => isotropic_primaryComponent H hb hne' hv hw,
    separatingLeft_primaryComponent_sup H ha hne, ?_⟩
  let φ := pairedFactorEquiv H ha hne
  let bV := Module.finBasis (AdjoinRoot (a : K[X]))
    (primaryComponent (x : Module.End K V) (a : K[X]))
  let ψ := φ.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bV).toMulEquiv)
  refine ⟨φ, ψ, fun g v hv => rfl, fun g v w hv hw => ?_, fun g => ?_, fun g hg => ?_⟩
  · exact (mem_unitaryCentralizer.mp g.2.1).1 v w
  · exact LinearMap.det_toMatrix bV _
  · exact det_eq_one_of_paired hK H ha hne g hg


theorem selfDualPrimaryBlock (a : primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (a : K[X]) = a) : SelfDualPrimaryBlock hK B x a := by
  have := hK.finite
  have ha := a.2
  have h0 := coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha
  refine ⟨odd_natDegree_of_selfDual hK h0 hself, unitaryFieldData_adjoinRoot hK,
    fun z => ?_, smul_adjoint_bar hK H ha hself, selfDualForm hK H ha hself,
    selfDualForm_isSymm hK H ha hself, selfDualForm_separatingLeft hK H ha hself,
    fun v w b => trace_selfDualForm hK H ha hself v w b,
    UnitaryFieldData.exists_orthonormal_basis (unitaryFieldData_adjoinRoot hK)
      (selfDualForm_isSymm hK H ha hself) (selfDualForm_separatingLeft hK H ha hself),
    selfDualFactorEquiv hK H ha hself, fun g v hv => rfl, fun g hg => ?_⟩
  · rw [UnitaryFieldData.bar_apply, ← pow_mul]
  · exact det_eq_one_of_selfDual hK H ha hself g hg


end Proofs

section Main

variable {ℓ f : ℕ} {K : Type*} [Field K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
  (x : LinearMap.GeneralLinearGroup K V)

theorem r3e_unitary_semisimple_primary_algebra_and_full_centralizer
    (hx : x ∈ sesqUnitaryGroup B)
    (hsq : Squarefree (minpoly K (x : Module.End K V))) :
    UnitaryPrimaryAlgebra hK B hB hBl x := by
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  refine ⟨fun a ha => dualPoly_mem_primaryFactors H ha,
    fun a ha => dualPoly_dualPoly_of_mem H ha, ⟨commutantEquivMatrix hsq⟩, ?_,
    fun a ha => adj_primaryProjection H ha, fun a hne => pairedPrimaryBlock H a hne,
    fun a hself => selfDualPrimaryBlock H a hself, ?_, ⟨exists_isPairedTransversal H,
      fun P hP => finrank_eq_paired_sum H hP⟩, fun z => mem_center_commutant_iff hsq z, ?_⟩
  · intro r
    rw [isPrimitiveCentralIdempotent_iff hsq r]
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, by rw [h]; rfl⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, Subtype.ext h⟩
  · refine ⟨fun O hO O' hO' hne g hg g' hg' =>
      commute_of_disjoint H (adjointOrbits_disjoint H hO hO' hne) hg hg',
      iSupIndep_supportedUnitary H fun O hO O' hO' hne => adjointOrbits_disjoint H hO hO' hne,
      le_antisymm (iSup_le fun O => supportedUnitary_le_unitaryCentralizer _) ?_⟩
    refine unitaryCentralizer_le_iSup H ?_ ?_
    · intro b hb
      exact ⟨{b, dualPoly hK.bar b}, ⟨b, hb, rfl⟩, Or.inl rfl⟩
    · rintro O ⟨a, ha, rfl⟩ b hb hbO
      rcases hbO with rfl | hbO
      · exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at hbO
        subst hbO
        exact Or.inl (dualPoly_dualPoly_of_mem H ha)
  · intro g
    constructor
    · rintro ⟨hu, hscal⟩
      have hmem := mem_unitaryCentralizer.mp hu
      have hz : (g : Module.End K V) ∈ commutant (x : Module.End K V) :=
        (mem_commutant _).mpr hmem.2
      exact ⟨hmem.1, hz, (mem_center_commutant_iff hsq ⟨(g : Module.End K V), hz⟩).mpr hscal⟩
    · rintro ⟨hU, hz, hc⟩
      exact ⟨mem_unitaryCentralizer.mpr ⟨hU, (mem_commutant _).mp hz⟩,
        (mem_center_commutant_iff hsq ⟨(g : Module.End K V), hz⟩).mp hc⟩

end Main

end CFSG.RankThree.PartOne
