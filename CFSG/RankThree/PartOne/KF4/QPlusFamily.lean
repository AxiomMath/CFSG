module

public import CFSG.RankThree.PartOne.KF4.QPlusFactor
public import CFSG.RankThree.PartOne.KF4.B2Twist
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardQuasisimple
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenLeviCentralizer
public import CFSG.RankThree.PartOne.KF4.QPlusCobound

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley.NativeLevi
open scoped Matrix Pointwise


section Connected

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

abbrev qpK (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] (f : ℕ) : Subfield L :=
  fixSubfield (qpFrobEquiv (Ω := L) f)

@[expose] def qpFix (f : ℕ) (J : Set (Fin Tag.F4.rank)) (g : ModGL Tag.F4 L) :
    Subgroup (ModGL Tag.F4 L) :=
  ((subsystemGroup Tag.F4 (qpK L f) J).map (baseChangeGL (qpK L f).subtype)).map
    (MulAut.conj g).toMonoidHom

theorem charP_qpK (f : ℕ) : CharP (qpK L f) 2 :=
  ⟨fun x => by
    rw [← (qpK L f).subtype.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩

theorem qpFix_finite (f : ℕ) [Finite (qpK L f)] (J : Set (Fin Tag.F4.rank)) (g : ModGL Tag.F4 L) :
    Finite (qpFix f J g) := by
  have : Finite (ModGL Tag.F4 (qpK L f)) := finite_modGL
  have h1 : Finite (subsystemGroup Tag.F4 (qpK L f) J) := inferInstance
  have h2 := Finite.of_equiv _ (Subgroup.equivMapOfInjective (subsystemGroup Tag.F4 (qpK L f) J)
    (baseChangeGL (qpK L f).subtype) (baseChangeGL_injective _)).toEquiv
  exact Finite.of_equiv _ (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv

theorem qpFix_quasi (f : ℕ) [Finite (qpK L f)] (h4 : 4 ≤ Nat.card (qpK L f))
    {J : Set (Fin Tag.F4.rank)} (hJne : J.Nonempty)
    (hconn : ∀ i ∈ J, ∀ j ∈ J, ∀ k, i ≤ k → k ≤ j → k ∈ J) (g : ModGL Tag.F4 L) :
    CFSG.IsQuasisimple (qpFix f J g) := by
  have := charP_qpK (L := L) f
  have hq := (even_F4_connected_standard_root_groups_quasisimple (qpK L f) h4 J hJne hconn).2.2.2.1
  have e1 := Subgroup.equivMapOfInjective (subsystemGroup Tag.F4 (qpK L f) J)
    (baseChangeGL (qpK L f).subtype) (baseChangeGL_injective _)
  have e2 := Subgroup.equivMapOfInjective
    ((subsystemGroup Tag.F4 (qpK L f) J).map (baseChangeGL (qpK L f).subtype))
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2) hq

theorem qpFix_eq (f : ℕ) {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)}
    (hC : QPCascade J C) {ω : L} (hω : ω ^ 2 ^ f = ω + 1) :
    qpFix f (J : Set (Fin Tag.F4.rank)) (qpCas C (qpA ω)⁻¹) =
      rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) ⊓
        twistedFixedPoints (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
  rw [← subsystemGroup_eq_rootSpan]
  exact (qp_inf_fixed_eq f hC hω).symm

omit [CharP L 2] [IsAlgClosed L] in
theorem qpCas_mem_subsystemGroup {J : Finset (Fin Tag.F4.rank)}
    {C : List (Fin Tag.F4.rank → ℤ)} (hC : QPCascade J C) (M : SL2 L) :
    qpCas C M ∈ subsystemGroup Tag.F4 L (J : Set (Fin Tag.F4.rank)) := by
  rw [subsystemGroup_eq_rootSpan]
  exact qpCas_mem_rootSpan hC M

theorem qpFix_free (f : ℕ) [Finite (qpK L f)] (h4 : 4 ≤ Nat.card (qpK L f))
    {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)} (hC : QPCascade J C)
    (ω : L) :
    QPFree (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)))
      (qpFix f (J : Set (Fin Tag.F4.rank)) (qpCas C (qpA ω)⁻¹)) := by
  intro y hy hc
  have hgQ := qpCas_mem_subsystemGroup hC (qpA ω)⁻¹
  have hyL : y ∈ standardLevi Tag.F4 L (J : Set (Fin Tag.F4.rank)) := by
    unfold standardLevi
    rw [subsystemGroup_eq_rootSpan]
    exact hy
  have hyC : y ∈ Subgroup.centralizer
      ((qpFix f (J : Set (Fin Tag.F4.rank)) (qpCas C (qpA ω)⁻¹) : Subgroup (ModGL Tag.F4 L)) :
        Set (ModGL Tag.F4 L)) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => (hc u hu).symm
  have hyZ : y ∈ simpleCharKernel Tag.F4 L (J : Set (Fin Tag.F4.rank)) := by
    rw [← standardLevi_inf_centralizer_conj (J : Set (Fin Tag.F4.rank)) (qpK L f) h4 hgQ]
    exact Subgroup.mem_inf.2 ⟨hyL, hyC⟩
  refine ⟨hyZ.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : g ∈ subsystemGroup Tag.F4 L (J : Set (Fin Tag.F4.rank)) := by
    rw [subsystemGroup_eq_rootSpan]; exact hg
  exact Subgroup.mem_centralizer_singleton_iff.1 (subsystemGroup_le_centralizer_of_mem hyZ hg')

theorem qp_factor_connected (f : ℕ) [Finite (qpK L f)] (h4 : 4 ≤ Nat.card (qpK L f))
    {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)} (hC : QPCascade J C)
    (hJne : (J : Set (Fin Tag.F4.rank)).Nonempty)
    (hconn : ∀ i ∈ (J : Set (Fin Tag.F4.rank)), ∀ j ∈ (J : Set (Fin Tag.F4.rank)), ∀ k,
      i ≤ k → k ≤ j → k ∈ (J : Set (Fin Tag.F4.rank))) {ω : L} (hω : ω ^ 2 ^ f = ω + 1) :
    QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
      (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)))
      (qpFix f (J : Set (Fin Tag.F4.rank)) (qpCas C (qpA ω)⁻¹)) where
  finite := qpFix_finite f _ _
  quasi := qpFix_quasi f h4 hJne hconn _
  eq := qpFix_eq f hC hω
  cent y hy _ hc := qpFix_free f h4 hC ω y hy hc

theorem simpleRootSL2_mem_subsystemGroup {K : Type} [Field K] {J : Set (Fin Tag.F4.rank)}
    {i : Fin Tag.F4.rank} (hi : i ∈ J) (Y : SL2 K) :
    simpleRootSL2 Tag.F4 K i Y ∈ subsystemGroup Tag.F4 K J := by
  rw [subsystemGroup_eq_rootSpan, ← rootSL2_single_eq_simple]
  have h : rootSL2 Tag.F4 K (Pi.single i 1) Y ∈ (rootSL2 Tag.F4 K (Pi.single i 1)).range :=
    ⟨Y, rfl⟩
  rw [range_rootSL2_of_isRoot (isRoot_single Tag.F4 i)] at h
  exact sup_le (rootSubgroup_le_rootSpan (single_mem_parabolicRoots_F4 hi))
    (rootSubgroup_le_rootSpan (neg_mem_parabolicRoots (single_mem_parabolicRoots_F4 hi))) h

theorem qpFix_rootSL2_mem (f : ℕ) {J : Set (Fin Tag.F4.rank)} {i : Fin Tag.F4.rank} (hi : i ∈ J)
    (g : ModGL Tag.F4 L) (Y : SL2 (qpK L f)) :
    g * simpleRootSL2 Tag.F4 L i (Matrix.SpecialLinearGroup.map (qpK L f).subtype Y) * g⁻¹ ∈
      qpFix f J g := by
  refine ⟨baseChangeGL (qpK L f).subtype (simpleRootSL2 Tag.F4 (qpK L f) i Y),
    ⟨_, simpleRootSL2_mem_subsystemGroup hi Y, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [baseChangeGL_simpleRootSL2_of_field]

end Connected

end CFSG.RankThree.PartOne.KF4
