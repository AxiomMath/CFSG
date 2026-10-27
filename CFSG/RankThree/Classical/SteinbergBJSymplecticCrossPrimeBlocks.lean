module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticPrimarySelfDual
public import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentral

public section

namespace CFSG.RankThree.Classical

open Polynomial Module Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram form form_self gram_mul_gram
  mem_statedSp_iff)
open CFSG.RankThree.PartOne.KCUnitary (gl_centralizer mem_gl_centralizer blockGL blockApply
  unitaryCentralizer mem_unitaryCentralizer supportedUnitary supportedUnitary_le_unitaryCentralizer
  IsPrimitiveCentralIdempotent isPrimitiveCentralIdempotent_iff primaryProjectionR
  primaryProjection_mul_self finrank_adjoinRoot)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial natDegree_reciprocalPolynomial)

section Lift

variable {G Q : Type*} [Group G] [Group Q] {p : ℕ}

theorem commute_of_map_commute [Finite G] (π : G →* Q) (hc : π.ker ≤ Subgroup.center G)
    (hcop : Nat.Coprime (Nat.card π.ker) p) {g x : G} (hx : x ^ p = 1)
    (h : Commute (π g) (π x)) : Commute g x := by
  have hy : (g * x * g⁻¹) ^ p ^ 1 = 1 := by rw [pow_one, conj_pow, hx, mul_one, mul_inv_cancel]
  have hπ : π (g * x * g⁻¹) = π x := by
    rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right]
  have h1 := eq_of_map_eq_of_pow_eq_one_of_coprime π hc hcop hy (by rwa [pow_one]) hπ
  exact mul_inv_eq_iff_eq_mul.mp h1

end Lift

section Model

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spForm (r : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (Fin r ⊕ Fin r → K) :=
  Matrix.toBilin' (gram K r)

theorem spForm_apply (u v : Fin r ⊕ Fin r → K) : spForm r K u v = u ⬝ᵥ (gram K r *ᵥ v) :=
  Matrix.toBilin'_apply' _ _ _

theorem spForm_isAlt : (spForm r K).IsAlt := fun v => by
  rw [spForm_apply]
  exact form_self v

theorem spForm_nondegenerate : (spForm r K).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_iff_det_ne_zero.2
    (Matrix.det_ne_zero_of_right_inverse (B := -gram K r) (by
      rw [Matrix.mul_neg, gram_mul_gram, neg_neg])))

theorem spForm_mulVec (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (u v : Fin r ⊕ Fin r → K) :
    spForm r K (A *ᵥ u) (A *ᵥ v) = Matrix.toBilin' (Aᵀ * gram K r * A) u v := by
  rw [spForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply', mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, ← dotProduct_mulVec]

@[expose] noncomputable def spLin (r : ℕ) (K : Type) [Field K] :
    StatedSp r K →* LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (StatedSp r K).subtype

noncomputable abbrev spEnd (g : StatedSp r K) : Module.End K (Fin r ⊕ Fin r → K) :=
  ((spLin r K g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K))

theorem spEnd_apply (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spEnd g v = ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  rfl

theorem spLin_injective : Function.Injective (spLin r K) := fun _ _ h =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective h)

theorem spLin_mem (g : StatedSp r K) : spLin r K g ∈ sesqUnitaryGroup (spForm r K) := by
  rw [mem_sesqUnitaryGroup]
  intro u v
  change spForm r K (spEnd g u) (spEnd g v) = spForm r K u v
  rw [spEnd_apply, spEnd_apply, spForm_mulVec, mem_statedSp_iff.mp g.2]
  rfl

theorem range_spLin : (spLin r K).range = sesqUnitaryGroup (spForm r K) := by
  refine le_antisymm (by rintro _ ⟨g, rfl⟩; exact spLin_mem g) fun h hh => ?_
  set A : GL (Fin r ⊕ Fin r) K := Matrix.GeneralLinearGroup.toLin.symm h with hA
  have hAh : Matrix.GeneralLinearGroup.toLin A = h := by rw [hA, MulEquiv.apply_symm_apply]
  have hmem : A ∈ StatedSp r K := by
    rw [mem_statedSp_iff]
    apply Matrix.toBilin'.injective
    refine LinearMap.ext₂ fun u v => ?_
    rw [← spForm_mulVec]
    have := mem_sesqUnitaryGroup.mp hh u v
    rw [← hAh] at this
    exact this
  exact ⟨⟨A, hmem⟩, hAh⟩

@[expose] noncomputable def comapSpLinEquiv
    (L : Subgroup (LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)))
    (hL : L ≤ sesqUnitaryGroup (spForm r K)) : L.comap (spLin r K) ≃* L :=
  ((L.comap (spLin r K)).equivMapOfInjective (spLin r K) spLin_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hL.trans range_spLin.ge)))

theorem coe_comapSpLinEquiv (L : Subgroup (LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)))
    (hL : L ≤ sesqUnitaryGroup (spForm r K)) (g : L.comap (spLin r K)) :
    ((comapSpLinEquiv L hL g : L) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) =
      spLin r K g := rfl

@[expose] noncomputable def spSupported (x : StatedSp r K) (O : Set K[X]) :
    Subgroup (StatedSp r K) :=
  (supportedUnitary (spForm r K) (spLin r K x) O).comap (spLin r K)

theorem mem_spSupported {x g : StatedSp r K} {O : Set K[X]} :
    g ∈ spSupported x O ↔ g * x = x * g ∧ ∀ k ∈ primaryFactors (spEnd x), k ∉ O →
      ∀ v ∈ primaryComponent (spEnd x) k, spEnd g v = v := by
  change spLin r K g ∈ supportedUnitary (spForm r K) (spLin r K x) O ↔ _
  constructor
  · rintro ⟨hg, hO⟩
    refine ⟨spLin_injective ?_, hO⟩
    rw [map_mul, map_mul]
    exact Units.ext (mem_unitaryCentralizer.mp hg).2.eq
  · rintro ⟨hg, hO⟩
    refine ⟨mem_unitaryCentralizer.mpr ⟨spLin_mem g, ?_⟩, hO⟩
    change spEnd g * spEnd x = spEnd x * spEnd g
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hg]

@[expose] noncomputable def spAdj (g : Module.End K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K) :=
  (spForm r K).leftAdjointOfNondegenerate spForm_nondegenerate g

end Model

section Transport

variable {G N : Type*} [Group G] [Group N]

theorem iSupIndep_comap_of_injective {f : G →* N} (hf : Function.Injective f) {ι : Type*}
    {L : ι → Subgroup N} (hL : iSupIndep L) : iSupIndep fun i => (L i).comap f := by
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hsup
  have hle : (⨆ (j) (_ : j ≠ i), (L j).comap f) ≤ (⨆ (j) (_ : j ≠ i), L j).comap f :=
    iSup₂_le fun j hj => Subgroup.comap_mono (le_iSup₂_of_le j hj le_rfl)
  have h1 := Subgroup.disjoint_def.mp (hL i) hg (hle hsup)
  exact hf (by rw [h1, map_one])

theorem comap_iSup_of_le_range {f : G →* N} (hf : Function.Injective f) {ι : Type*}
    {L : ι → Subgroup N} (hL : ∀ i, L i ≤ f.range) :
    (⨆ i, L i).comap f = ⨆ i, (L i).comap f := by
  refine le_antisymm (fun g hg => ?_) (iSup_le fun i => Subgroup.comap_mono (le_iSup L i))
  have h1 : (⨆ i, L i) = (⨆ i, (L i).comap f).map f := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_comap_eq_self (hL i)).symm
  have hg' : f g ∈ (⨆ i, (L i).comap f).map f := h1 ▸ hg
  obtain ⟨g', hg', hfg⟩ := hg'
  rwa [← hf hfg]

end Transport

section Primary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsReciprocalTransversal (y : Module.End K V) (P : Finset K[X]) : Prop :=
  (∀ h ∈ P, h ∈ primaryFactors y ∧ h ≠ reciprocalPolynomial h) ∧
    (∀ h ∈ primaryFactors y, h ≠ reciprocalPolynomial h → h ∈ P ∨ reciprocalPolynomial h ∈ P) ∧
    (∀ h ∈ P, reciprocalPolynomial h ∉ P)

variable [FiniteDimensional K V]

open _root_.Classical in
theorem isInternal_primaryComponent_of_squarefree {y : Module.End K V}
    (hsq : Squarefree (minpoly K y)) :
    DirectSum.IsInternal (fun h : primaryFactors y => primaryComponent y (h : K[X])) := by
  classical
  have hrange : ∀ h : primaryFactors y,
      LinearMap.range (primaryProjection y (h : K[X])) = primaryComponent y (h : K[X]) :=
    fun h => le_antisymm (by rintro _ ⟨v, rfl⟩; exact primaryProjection_mem hsq h.2 v)
      (fun v hv => ⟨v, primaryProjection_of_mem hsq h.2 hv⟩)
  have := isInternal_range_of_orthogonal_idempotents
    (fun h : primaryFactors y => primaryProjection y (h : K[X]))
    (fun h => primaryProjection_mul_self hsq h.2)
    (fun h k hhk => LinearMap.ext fun v => primaryProjection_of_mem_ne hsq h.2 k.2
      (fun e => hhk (Subtype.ext e).symm) (primaryProjection_mem hsq k.2 v))
    (by rw [Finset.sum_coe_sort (primaryFactors y) (primaryProjection y)]
        exact sum_primaryProjection hsq)
  simpa only [hrange] using this

theorem primaryComponent_eq_bot_of_not_mem {y : Module.End K V} {a : K[X]} (hirr : Irreducible a)
    (hmon : a.Monic) (ha : a ∉ primaryFactors y) : primaryComponent y a = ⊥ := by
  have hcop : IsCoprime a (minpoly K y) :=
    hirr.coprime_iff_not_dvd.mpr fun hd => ha (mem_primaryFactors.mpr ⟨hirr, hmon, hd⟩)
  have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime y hcop
  rw [minpoly.aeval, LinearMap.ker_zero, disjoint_top] at hdisj
  exact hdisj

theorem irreducible_X_sub_one : Irreducible (X - 1 : K[X]) := by
  rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1]]
  exact irreducible_X_sub_C 1

theorem monic_X_sub_one : (X - 1 : K[X]).Monic := by
  rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1]]
  exact monic_X_sub_C 1

theorem orderOf_root_of_mem {p : ℕ} (hp : p.Prime) {y : Module.End K V} (hy : y ^ p = 1)
    {h : K[X]} (hh : h ∈ primaryFactors y) (h1 : h ≠ X - 1) :
    orderOf (AdjoinRoot.root h) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : h ∣ X ^ p - 1 := (mem_primaryFactors.mp hh).2.2.trans
    (minpoly.dvd K y (by rw [map_sub, map_pow, aeval_X, map_one, hy, sub_self]))
  have hpow : AdjoinRoot.root h ^ p = 1 := by
    have h2 : AdjoinRoot.mk h (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
    rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h2
  refine orderOf_eq_prime hpow fun hr => h1 ?_
  have h2 : AdjoinRoot.mk h (X - 1) = 0 := by rw [map_sub, AdjoinRoot.mk_X, map_one, hr, sub_self]
  exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) monic_X_sub_one
    ((irreducible_of_mem_primaryFactors hh).associated_of_dvd irreducible_X_sub_one
      (AdjoinRoot.mk_eq_zero.mp h2))

theorem orderOf_dvd_natCard_sub_one {E : Type*} [Field E] [Finite E] {z : E} (hz : z ≠ 0) :
    orderOf z ∣ Nat.card E - 1 := by
  have := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card]
  exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one z hz)

@[expose] noncomputable def reciprocalOrbits (y : Module.End K V) : Set (Set K[X]) :=
  (fun h : K[X] => ({h, reciprocalPolynomial h} : Set K[X])) '' (primaryFactors y : Set K[X])

namespace AltPrimaryData

variable {B : LinearMap.BilinForm K V} {x : LinearMap.GeneralLinearGroup K V}
  (H : AltPrimaryData B x)
include H

theorem reciprocalOrbits_eq_of_mem {h c : K[X]} (hh : h ∈ primaryFactors (x : Module.End K V))
    (hc : c ∈ ({h, reciprocalPolynomial h} : Set K[X])) :
    ({c, reciprocalPolynomial c} : Set K[X]) = {h, reciprocalPolynomial h} := by
  rcases hc with rfl | hc
  · rfl
  · rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [H.reciprocal_reciprocal hh, Set.pair_comm]

theorem reciprocalOrbits_disjoint {O O' : Set K[X]} (hO : O ∈ reciprocalOrbits (x : Module.End K V))
    (hO' : O' ∈ reciprocalOrbits (x : Module.End K V)) (hne : O ≠ O') : Disjoint O O' := by
  obtain ⟨h, hh, rfl⟩ := hO
  obtain ⟨h', hh', rfl⟩ := hO'
  rw [Set.disjoint_left]
  intro c hc hc'
  exact hne ((H.reciprocalOrbits_eq_of_mem hh hc).symm.trans (H.reciprocalOrbits_eq_of_mem hh' hc'))

open _root_.Classical in
theorem exists_isReciprocalTransversal :
    ∃ P : Finset K[X], IsReciprocalTransversal (x : Module.End K V) P := by
  refine ⟨(primaryFactors (x : Module.End K V)).filter
    (fun h => h ≠ reciprocalPolynomial h ∧ WellOrderingRel h (reciprocalPolynomial h)), ?_, ?_, ?_⟩
  · intro h hh
    simp only [Finset.mem_filter] at hh
    exact ⟨hh.1, hh.2.1⟩
  · intro h hh hne
    rcases trichotomous_of WellOrderingRel h (reciprocalPolynomial h) with h' | h' | h'
    · left
      simp only [Finset.mem_filter]
      exact ⟨hh, hne, h'⟩
    · exact absurd h' hne
    · right
      simp only [Finset.mem_filter]
      refine ⟨H.reciprocal_mem hh, ?_, ?_⟩
      · rw [H.reciprocal_reciprocal hh]
        exact hne.symm
      · rw [H.reciprocal_reciprocal hh]
        exact h'
  · intro h hh hrh
    simp only [Finset.mem_filter] at hh hrh
    rw [H.reciprocal_reciprocal hh.1] at hrh
    exact asymm_of WellOrderingRel hh.2.2 hrh.2.2

open _root_.Classical in
theorem finrank_eq_sum_blocks {P : Finset K[X]}
    (hP : IsReciprocalTransversal (x : Module.End K V) P) :
    finrank K V = finrank K (primaryComponent (x : Module.End K V) (X - 1)) +
      ∑ h ∈ P, 2 * (h.natDegree * primaryMultiplicity (x : Module.End K V) h) +
      ∑ h ∈ (primaryFactors (x : Module.End K V)).filter
          (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
        h.natDegree * primaryMultiplicity (x : Module.End K V) h := by
  set Φ := primaryFactors (x : Module.End K V) with hΦ
  set Fm : K[X] → ℕ := fun h => h.natDegree * primaryMultiplicity (x : Module.End K V) h with hFm
  have e1 : finrank K V = ∑ h ∈ Φ, Fm h := by
    rw [finrank_eq_sum_degree_mul_multiplicity H.squarefree]
    exact Finset.sum_coe_sort Φ Fm
  have hFd : ∀ h ∈ Φ, Fm (reciprocalPolynomial h) = Fm h := fun h hh => by
    simp only [hFm, natDegree_reciprocalPolynomial (H.coeff_zero_ne hh),
      H.primaryMultiplicity_reciprocal hh]
  have hPr : Φ.filter (fun h => ¬ reciprocalPolynomial h = h) =
      P ∪ P.image reciprocalPolynomial := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hh, hne⟩
      rcases hP.2.1 h hh (fun e => hne e.symm) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨reciprocalPolynomial h, h', H.reciprocal_reciprocal hh⟩
    · rintro (h' | ⟨k, hk, rfl⟩)
      · exact ⟨(hP.1 h h').1, fun e => (hP.1 h h').2 e.symm⟩
      · refine ⟨H.reciprocal_mem (hP.1 k hk).1, ?_⟩
        rw [H.reciprocal_reciprocal (hP.1 k hk).1]
        exact (hP.1 k hk).2
  have hdisj : Disjoint P (P.image reciprocalPolynomial) := by
    rw [Finset.disjoint_left]
    intro h hh hh'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh'
    exact hP.2.2 k hk hh
  have e2 : ∑ h ∈ Φ, Fm h = ∑ h ∈ Φ.filter (fun h => reciprocalPolynomial h = h), Fm h +
      ∑ h ∈ Φ.filter (fun h => ¬ reciprocalPolynomial h = h), Fm h :=
    (Finset.sum_filter_add_sum_filter_not Φ _ Fm).symm
  have e3 : ∑ h ∈ Φ.filter (fun h => reciprocalPolynomial h = h), Fm h =
      finrank K (primaryComponent (x : Module.End K V) (X - 1)) +
        ∑ h ∈ Φ.filter (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1), Fm h := by
    rw [← Finset.sum_filter_add_sum_filter_not (Φ.filter _) (fun h => h = X - 1),
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    by_cases h1 : (X - 1 : K[X]) ∈ Φ
    · have hs : Φ.filter (fun h => reciprocalPolynomial h = h ∧ h = X - 1) = {X - 1} := by
        ext h
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, -, rfl⟩
          rfl
        · rintro rfl
          exact ⟨h1, reciprocalPolynomial_X_sub_one, rfl⟩
      rw [hs, Finset.sum_singleton]
      have : Fact (Irreducible (X - 1 : K[X])) := ⟨irreducible_X_sub_one⟩
      exact (finrank_primaryComponent (x : Module.End K V) (X - 1)).symm
    · have hs : Φ.filter (fun h => reciprocalPolynomial h = h ∧ h = X - 1) = ∅ := by
        ext h
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hh, -, rfl⟩
        exact h1 hh
      rw [hs, Finset.sum_empty,
        primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one h1, finrank_bot]
  have e4 : ∑ h ∈ Φ.filter (fun h => ¬ reciprocalPolynomial h = h), Fm h =
      ∑ h ∈ P, Fm h + ∑ h ∈ P, Fm h := by
    rw [hPr, Finset.sum_union hdisj, Finset.sum_image fun h hh k hk e =>
      H.reciprocal_injOn (hP.1 h hh).1 (hP.1 k hk).1 e]
    congr 1
    exact Finset.sum_congr rfl fun h hh => hFd h (hP.1 h hh).1
  have e5 : ∑ h ∈ P, 2 * Fm h = 2 * ∑ h ∈ P, Fm h := (Finset.mul_sum P Fm 2).symm
  change finrank K V = finrank K (primaryComponent (x : Module.End K V) (X - 1)) +
    ∑ h ∈ P, 2 * Fm h + ∑ h ∈ Φ.filter (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1), Fm h
  omega

end AltPrimaryData

end Primary

section Statement

variable {r : ℕ} {K : Type} [Field K]

structure SpPairedBlock (ℓ f p : ℕ) (x : StatedSp r K) (h : primaryFactors (spEnd x)) :
    Prop where
  isotropic_left : ∀ v ∈ primaryComponent (spEnd x) (h : K[X]),
    ∀ w ∈ primaryComponent (spEnd x) (h : K[X]), spForm r K v w = 0
  isotropic_right : ∀ v ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
    ∀ w ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])), spForm r K v w = 0
  perfect_left : ∀ v ∈ primaryComponent (spEnd x) (h : K[X]),
    (∀ w ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])), spForm r K v w = 0) →
      v = 0
  perfect_right : ∀ w ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
    (∀ v ∈ primaryComponent (spEnd x) (h : K[X]), spForm r K v w = 0) → w = 0
  natDegree_eq : (h : K[X]).natDegree = (reciprocalPolynomial (h : K[X])).natDegree
  multiplicity_eq : primaryMultiplicity (spEnd x) (h : K[X]) =
    primaryMultiplicity (spEnd x) (reciprocalPolynomial (h : K[X]))
  card_field : Nat.card (AdjoinRoot (h : K[X])) = (ℓ ^ f) ^ (h : K[X]).natDegree
  factor : ∃ φ : spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ≃*
      blockGL (spEnd x) (h : K[X]),
    (∀ (g : spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) (v : Fin r ⊕ Fin r → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
        blockApply (φ g) v hv = spEnd (g : StatedSp r K) v) ∧
    ∀ (g : spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) (v w : Fin r ⊕ Fin r → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      w ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])) →
        spForm r K (blockApply (φ g) v hv) (spEnd (g : StatedSp r K) w) = spForm r K v w
  matrixFactor : Nonempty (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ≃*
    GL (Fin (primaryMultiplicity (spEnd x) (h : K[X]))) (AdjoinRoot (h : K[X])))
  dvd : p ∣ (ℓ ^ f) ^ (h : K[X]).natDegree - 1

structure SpSelfDualBlock (ℓ f p : ℕ) (x : StatedSp r K) (h : primaryFactors (spEnd x)) :
    Prop where
  exists_half : ∃ d : ℕ, (h : K[X]).natDegree = 2 * d ∧ p ∣ (ℓ ^ f) ^ d + 1 ∧
    ∃ σ : AdjoinRoot (h : K[X]) ≃ₐ[K] AdjoinRoot (h : K[X]),
      (∀ z, σ z = z ^ ((ℓ ^ f) ^ d)) ∧ σ ≠ 1 ∧ (∀ z, σ (σ z) = z) ∧
      σ (AdjoinRoot.root (h : K[X])) = (AdjoinRoot.root (h : K[X]))⁻¹ ∧
      (∀ (e : AdjoinRoot (h : K[X])) (v w : primaryComponent (spEnd x) (h : K[X])),
        spForm r K ((e • v : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K)
          (w : Fin r ⊕ Fin r → K) =
        spForm r K (v : Fin r ⊕ Fin r → K)
          ((σ e • w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K)) ∧
      ∃ hE : UnitaryFieldData ℓ (f * d) (AdjoinRoot (h : K[X])), (∀ z, hE.bar z = σ z) ∧
        ∃ Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[hE.bar]
            primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X]),
          Hf.IsSymm ∧ Hf.SeparatingLeft ∧
          (∃ η : AdjoinRoot (h : K[X]), η ≠ 0 ∧ hE.bar η = -η ∧
            ∀ (v w : primaryComponent (spEnd x) (h : K[X])) (c : AdjoinRoot (h : K[X])),
              Algebra.trace K (AdjoinRoot (h : K[X])) (c * Hf v w) =
                spForm r K (v : Fin r ⊕ Fin r → K)
                  (((c * η) • w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K)) ∧
          (∃ e : Module.Basis (Fin (primaryMultiplicity (spEnd x) (h : K[X])))
              (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])),
            ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) ∧
          ∃ φ : spSupported x {(h : K[X])} ≃* sesqUnitaryGroup Hf,
            ∀ (g : spSupported x {(h : K[X])}) (v : Fin r ⊕ Fin r → K)
              (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
              blockApply (φ g : blockGL (spEnd x) (h : K[X])) v hv = spEnd (g : StatedSp r K) v

open _root_.Classical in
structure SpPrimaryBlocks (ℓ f p : ℕ) (x : StatedSp r K) (a : StatedProj (StatedSp r K)) :
    Prop where
  bijOn : Set.BijOn reciprocalPolynomial (primaryFactors (spEnd x) : Set K[X])
    (primaryFactors (spEnd x) : Set K[X])
  isInternal : DirectSum.IsInternal
    (fun h : primaryFactors (spEnd x) => primaryComponent (spEnd x) (h : K[X]))
  fixed_eq : primaryComponent (spEnd x) (X - 1) = LinearMap.ker (spEnd x - 1)
  fixed_nondegenerate :
    ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).Nondegenerate
  nontrivial : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → orderOf (AdjoinRoot.root h) = p
  paired : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ reciprocalPolynomial (h : K[X]) →
    SpPairedBlock ℓ f p x h
  selfDual : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
    reciprocalPolynomial (h : K[X]) = h → SpSelfDualBlock ℓ f p x h
  fixedFactor : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) →
    ∃ φ : spSupported x {X - 1} ≃*
        sesqUnitaryGroup ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))),
      ∀ (g : spSupported x {X - 1}) (v : primaryComponent (spEnd x) (X - 1)),
        ((((φ g : sesqUnitaryGroup ((spForm r K).restrict
            (primaryComponent (spEnd x) (X - 1)))) :
          LinearMap.GeneralLinearGroup K (primaryComponent (spEnd x) (X - 1))) :
            Module.End K (primaryComponent (spEnd x) (X - 1))) v : Fin r ⊕ Fin r → K) =
          spEnd (g : StatedSp r K) v
  directProduct :
    (∀ O ∈ reciprocalOrbits (spEnd x), ∀ O' ∈ reciprocalOrbits (spEnd x), O ≠ O' →
      ∀ g ∈ spSupported x O, ∀ g' ∈ spSupported x O', Commute g g') ∧
    iSupIndep (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X])) ∧
    (⨆ O : reciprocalOrbits (spEnd x), spSupported x (O : Set K[X])) = Subgroup.centralizer {x}
  algebraEquiv : ∃ Φ : commutant (spEnd x) ≃ₐ[K] ((h : primaryFactors (spEnd x)) →
      Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))),
    ∀ (z : commutant (spEnd x)) (h : primaryFactors (spEnd x))
      (v : primaryComponent (spEnd x) (h : K[X])),
      ((Φ z h v : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) =
        (z : Module.End K (Fin r ⊕ Fin r → K)) v
  adj_spec : ∀ (g : Module.End K (Fin r ⊕ Fin r → K)) (u v : Fin r ⊕ Fin r → K),
    spForm r K (g u) v = spForm r K u (spAdj g v)
  adj_mem : ∀ g ∈ commutant (spEnd x), spAdj g ∈ commutant (spEnd x)
  primitiveCentral : ∀ z : commutant (spEnd x), IsPrimitiveCentralIdempotent K z ↔
    ∃ h ∈ primaryFactors (spEnd x),
      (z : Module.End K (Fin r ⊕ Fin r → K)) = primaryProjection (spEnd x) h
  adj_primitiveCentral : ∀ h ∈ primaryFactors (spEnd x),
    spAdj (primaryProjection (spEnd x) h) = primaryProjection (spEnd x) (reciprocalPolynomial h)
  center_eq : ∀ z : commutant (spEnd x), z ∈ Subalgebra.center K (commutant (spEnd x)) ↔
    ∀ h : primaryFactors (spEnd x), ∃ c : AdjoinRoot (h : K[X]),
      ∀ v : primaryComponent (spEnd x) (h : K[X]),
        (z : Module.End K (Fin r ⊕ Fin r → K)) (v : Fin r ⊕ Fin r → K) =
          ((c • v : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K)
  unitary_eq : ∀ g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K),
    ((g : Module.End K (Fin r ⊕ Fin r → K)) ∈ commutant (spEnd x) ∧
      spAdj (g : Module.End K (Fin r ⊕ Fin r → K)) * g = 1) ↔
      g ∈ (Subgroup.centralizer {x}).map (spLin r K)
  rank : ∃ s : ℕ, finrank K (primaryComponent (spEnd x) (X - 1)) = 2 * s ∧
    (∃ P : Finset K[X], IsReciprocalTransversal (spEnd x) P) ∧
    ∀ P : Finset K[X], IsReciprocalTransversal (spEnd x) P →
      r = s + ∑ h ∈ P, h.natDegree * primaryMultiplicity (spEnd x) h +
        ∑ h ∈ (primaryFactors (spEnd x)).filter
            (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
          h.natDegree / 2 * primaryMultiplicity (spEnd x) h
  centralizer_eq : Subgroup.centralizer {a} = (Subgroup.centralizer {x}).map (proj r K)

end Statement

section Proof

variable {r : ℕ} {K : Type} [Field K]

theorem altPrimaryData_spLin {p : ℕ} (hpK : (p : K) ≠ 0) {x : StatedSp r K} (hx : x ^ p = 1) :
    AltPrimaryData (spForm r K) (spLin r K x) := by
  refine ⟨spForm_isAlt, spForm_nondegenerate.1, spLin_mem x, ?_⟩
  have hsqp : Squarefree (X ^ p - 1 : K[X]) := by
    have := Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero
    simpa using this.squarefree
  refine squarefree_minpoly_of_aeval_eq_zero hsqp ?_
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
  change (spEnd x) ^ p = 1
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]

theorem spEnd_pow {p : ℕ} {x : StatedSp r K} (hx : x ^ p = 1) : spEnd x ^ p = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]

theorem supportedUnitary_le_sesq (x : StatedSp r K) (O : Set K[X]) :
    supportedUnitary (spForm r K) (spLin r K x) O ≤ sesqUnitaryGroup (spForm r K) :=
  fun _ hg => (mem_unitaryCentralizer.mp hg.1).1

theorem symplectic_cross_prime_primary_centralizer_blocks {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hr : 1 ≤ r) (a : StatedProj (StatedSp r K)) (ha : orderOf a = p) :
    (∃! x : StatedSp r K, proj r K x = a ∧ orderOf x = p) ∧
      ∀ x : StatedSp r K, proj r K x = a → orderOf x = p → SpPrimaryBlocks ℓ f p x a := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hcharK : CharP K ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) hcardK
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have : Fact p.Prime := ⟨hp⟩
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : Nat.Coprime (Nat.card (proj r K).ker) p := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have ha1 : a ≠ 1 := fun h => hp.one_lt.ne' (by rw [← ha, h, orderOf_one])
  have hapow : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hApow : ∀ b ∈ Subgroup.zpowers a, b ^ p = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hapow,
      _root_.one_zpow]
  have hAp : IsPGroup p (Subgroup.zpowers a) := fun b =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hApow b b.2)⟩
  obtain ⟨Ã, -, -, e, he⟩ := exists_sylow_lift_of_ker_le_center hp (proj r K)
    SymplecticHigher.proj_surjective hZc hZp (Subgroup.zpowers a) hAp
  obtain ⟨x₀, ⟨hx₀a, hx₀p⟩, hx₀u⟩ := existsUnique_lift_pow_eq_one (proj r K) hZc hZp hApow e he
    a (Subgroup.mem_zpowers a)
  have hx₀1 : x₀ ≠ 1 := fun h => ha1 (by rw [← hx₀a, h, map_one])
  refine ⟨⟨x₀, ⟨hx₀a, orderOf_eq_prime hx₀p hx₀1⟩, fun y ⟨hya, hyp⟩ =>
    hx₀u y ⟨hya, by rw [← hyp]; exact pow_orderOf_eq_one y⟩⟩, fun x hxa hxp => ?_⟩
  have hx : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have H := altPrimaryData_spLin hpK hx
  have hsq := H.squarefree
  have hX : spEnd x ^ p = 1 := spEnd_pow hx
  have hrecX : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := reciprocalPolynomial_X_sub_one
  have hcov : ∀ b ∈ primaryFactors (spEnd x), ∃ O ∈ reciprocalOrbits (spEnd x), b ∈ O :=
    fun b hb => ⟨{b, reciprocalPolynomial b}, ⟨b, hb, rfl⟩, Or.inl rfl⟩
  have hcl : ∀ O ∈ reciprocalOrbits (spEnd x), ∀ b ∈ primaryFactors (spEnd x), b ∈ O →
      reciprocalPolynomial b ∈ O := by
    rintro O ⟨c, hc, rfl⟩ b hb hbO
    rcases hbO with rfl | hbO
    · exact Or.inr rfl
    · rw [Set.mem_singleton_iff] at hbO
      subst hbO
      exact Or.inl (H.reciprocal_reciprocal hc)
  have hdisj : ∀ O ∈ reciprocalOrbits (spEnd x), ∀ O' ∈ reciprocalOrbits (spEnd x), O ≠ O' →
      Disjoint O O' := fun O hO O' hO' hne => H.reciprocalOrbits_disjoint hO hO' hne
  have hnontriv : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → orderOf (AdjoinRoot.root h) = p :=
    fun h hh h1 => orderOf_root_of_mem hp hX hh h1
  have hpaired : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ reciprocalPolynomial (h : K[X]) →
      SpPairedBlock ℓ f p x h := by
    intro h hne
    have hh := h.2
    have hb := H.reciprocal_mem hh
    have h0 := H.coeff_zero_ne hh
    have hne' : reciprocalPolynomial (h : K[X]) ≠
        reciprocalPolynomial (reciprocalPolynomial (h : K[X])) := by
      rw [H.reciprocal_reciprocal hh]
      exact hne.symm
    have hne1 : (h : K[X]) ≠ X - 1 := fun e => hne (by rw [e, hrecX])
    have hcard : Nat.card (AdjoinRoot (h : K[X])) = (ℓ ^ f) ^ (h : K[X]).natDegree := by
      rw [Module.natCard_eq_pow_finrank (K := K), finrank_adjoinRoot, hK]
    let φ := (comapSpLinEquiv _ (supportedUnitary_le_sesq x
      {(h : K[X]), reciprocalPolynomial (h : K[X])})).trans (H.pairedEquiv hh hne)
    refine ⟨fun v hv w hw => H.orthogonal_of_ne hh hh hne hv hw,
      fun v hv w hw => H.orthogonal_of_ne hb hb hne' hv hw,
      fun v hv hperp => H.eq_zero_of_perfect_left hh hv hperp,
      fun w hw hperp => H.eq_zero_of_perfect_right hh hw hperp,
      (natDegree_reciprocalPolynomial h0).symm, (H.primaryMultiplicity_reciprocal hh).symm,
      hcard, ⟨φ, fun g v hv => rfl, fun g v w hv _ =>
        mem_sesqUnitaryGroup.mp (spLin_mem (g : StatedSp r K)) v w⟩,
      ⟨φ.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis
        (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])))).toMulEquiv)⟩, ?_⟩
    have : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    rw [← hcard, ← hnontriv h hh hne1]
    exact orderOf_dvd_natCard_sub_one (CFSG.RankThree.PartOne.KCUnitary.root_ne_zero h0)
  have hselfdual : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      reciprocalPolynomial (h : K[X]) = h → SpSelfDualBlock ℓ f p x h := by
    intro h hne1 hself
    have hh := h.2
    have h0 := H.coeff_zero_ne hh
    have hord := hnontriv h hh hne1
    have hsq2 : AdjoinRoot.root (h : K[X]) ^ 2 ≠ 1 := fun h2 => hp2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hord ▸ orderOf_dvd_of_pow_eq_one h2))
    obtain ⟨d, hd, hσd⟩ := exists_rootInv_eq_pow h0 hself hsq2
    rw [finrank_adjoinRoot] at hd
    set σ := rootInv h0 hself with hσdef
    have hσq : ∀ z, σ z = z ^ ((ℓ ^ f) ^ d) := fun z => by rw [hσd, hK]
    have hd1 : 1 ≤ d := by
      have := (irreducible_of_mem_primaryFactors hh).natDegree_pos
      omega
    have hE : UnitaryFieldData ℓ (f * d) (AdjoinRoot (h : K[X])) := by
      refine ⟨hℓ, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
      rw [Module.natCard_eq_pow_finrank (K := K), finrank_adjoinRoot, hK, hd, ← pow_mul]
      ring_nf
    have hbar : ∀ z, hE.bar z = rootInv h0 hself z := fun z => by
      rw [UnitaryFieldData.bar_apply, ← hσdef, hσq, ← pow_mul]
    obtain ⟨η, hη0, hη⟩ := exists_ne_zero_neg σ (rootInv_rootInv h0 hself)
      (rootInv_ne_one h0 hself hsq2)
    have hηbar : hE.bar η = -η := by rw [hbar, ← hσdef, hη]
    have hsymm := H.altHermForm_isSymm hh hself hE.bar hbar hηbar
    have hsep := H.altHermForm_separatingLeft hh hself hE.bar hbar hη0
    refine ⟨⟨d, hd, ?_, σ, hσq, rootInv_ne_one h0 hself hsq2, rootInv_rootInv h0 hself,
      rootInv_root h0 hself, fun e v w => H.smul_adjoint hh hself e v w, hE, hbar,
      H.altHermForm hh hself hE.bar hbar η, hsymm, hsep,
      ⟨η, hη0, hηbar, fun v w c => H.trace_altHermForm hh hself hE.bar hbar η v w c⟩,
      hE.exists_orthonormal_basis hsymm hsep,
      ⟨(comapSpLinEquiv _ (supportedUnitary_le_sesq x {(h : K[X])})).trans
        (H.selfDualEquiv hh hself hE.bar hbar hη0), fun g v hv => rfl⟩⟩⟩
    have hr0 := CFSG.RankThree.PartOne.KCUnitary.root_ne_zero h0
    have h1 : AdjoinRoot.root (h : K[X]) ^ ((ℓ ^ f) ^ d + 1) = 1 := by
      rw [pow_succ, ← hσq, rootInv_root h0 hself, inv_mul_cancel₀ hr0]
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1
  have hfixed_nd : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).Nondegenerate := by
    by_cases h1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
    · exact H.nondegenerate_restrict_fixed h1
    · have hbot := primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one h1
      have h0 : ∀ v : primaryComponent (spEnd x) (X - 1), v = 0 := fun v =>
        Subtype.ext ((Submodule.mem_bot K).mp (hbot ▸ v.2))
      exact ⟨fun v _ => h0 v, fun v _ => h0 v⟩
  have hfixed_even : ∃ s, finrank K (primaryComponent (spEnd x) (X - 1)) = 2 * s := by
    by_cases h1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
    · obtain ⟨s, hs⟩ := H.even_finrank_fixed h1
      exact ⟨s, by rw [hs, two_mul]⟩
    · refine ⟨0, ?_⟩
      rw [primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one h1,
        finrank_bot]
  obtain ⟨s, hs⟩ := hfixed_even
  have hsupLe : ∀ O : reciprocalOrbits (spEnd x),
      supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X]) ≤ (spLin r K).range :=
    fun O => (supportedUnitary_le_sesq x _).trans range_spLin.ge
  have hiSup : (⨆ O : reciprocalOrbits (spEnd x),
      supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X])) =
      unitaryCentralizer (spForm r K) (spLin r K x) :=
    le_antisymm (iSup_le fun O => supportedUnitary_le_unitaryCentralizer _)
      (H.unitaryCentralizer_le_iSup hcov hcl)
  have hcomapC : (unitaryCentralizer (spForm r K) (spLin r K x)).comap (spLin r K) =
      Subgroup.centralizer {x} := by
    ext g
    rw [Subgroup.mem_comap, mem_unitaryCentralizer, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hc⟩
      apply spLin_injective
      rw [map_mul, map_mul]
      exact Units.ext hc.eq
    · intro hc
      refine ⟨spLin_mem g, ?_⟩
      change spEnd g * spEnd x = spEnd x * spEnd g
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hc]
  refine ⟨H.bijOn_reciprocal, isInternal_primaryComponent_of_squarefree hsq,
    primaryComponent_X_sub_one (spEnd x), hfixed_nd, hnontriv, hpaired, hselfdual,
    fun h1 => ⟨(comapSpLinEquiv _ (supportedUnitary_le_sesq x {X - 1})).trans (H.fixedEquiv h1),
      fun g v => rfl⟩, ⟨?_, ?_, ?_⟩, ⟨commutantEquivPi hsq, fun z h v => rfl⟩,
    fun g u v => H.adj_spec g u v, fun g hg => H.adj_mem_commutant hg, ?_,
    fun h hh => H.adj_primaryProjection hh, fun z => mem_center_commutant_iff hsq z, ?_,
    ⟨s, hs, H.exists_isReciprocalTransversal, ?_⟩, ?_⟩
  ·
    intro O hO O' hO' hne g hg g' hg'
    have hc := H.commute_of_disjoint (hdisj O hO O' hO' hne) hg hg'
    apply spLin_injective
    rw [map_mul, map_mul]
    exact hc.eq
  · exact iSupIndep_comap_of_injective spLin_injective (H.iSupIndep_supported hdisj)
  · change (⨆ O : reciprocalOrbits (spEnd x),
      (supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X])).comap (spLin r K)) = _
    rw [← comap_iSup_of_le_range spLin_injective hsupLe, hiSup, hcomapC]
  ·
    intro z
    rw [isPrimitiveCentralIdempotent_iff hsq z]
    constructor
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, by rw [e]; rfl⟩
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, Subtype.ext e⟩
  ·
    intro g
    constructor
    · rintro ⟨hgR, hadj⟩
      have hgS : g ∈ sesqUnitaryGroup (spForm r K) := (H.adj_mul_self_eq_one_iff g).mp hadj
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp (range_spLin.ge hgS)
      refine ⟨t, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply spLin_injective
      rw [map_mul, map_mul]
      exact Units.ext ((mem_commutant _).mp hgR).eq
    · rintro ⟨t, ht, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ht
      refine ⟨(mem_commutant _).mpr ?_, (H.adj_mul_self_eq_one_iff _).mpr (spLin_mem t)⟩
      change spEnd t * spEnd x = spEnd x * spEnd t
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ht]
  ·
    intro P hP
    have h1 : r + r = 2 * s + ∑ h ∈ P, 2 * (h.natDegree * primaryMultiplicity (spEnd x) h) +
        ∑ h ∈ (primaryFactors (spEnd x)).filter
          (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
          h.natDegree * primaryMultiplicity (spEnd x) h := by
      have := H.finrank_eq_sum_blocks hP
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
      rw [← hs]
      exact this
    have hsd : ∑ h ∈ (primaryFactors (spEnd x)).filter
          (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
        h.natDegree * primaryMultiplicity (spEnd x) h =
        2 * ∑ h ∈ (primaryFactors (spEnd x)).filter
          (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
        h.natDegree / 2 * primaryMultiplicity (spEnd x) h := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_filter] at hh
      obtain ⟨d, hd, -⟩ := (hselfdual ⟨h, hh.1⟩ hh.2.2 hh.2.1).exists_half
      change h.natDegree = 2 * d at hd
      rw [hd, Nat.mul_div_cancel_left d two_pos]
      ring
    have hP2 : ∑ h ∈ P, 2 * (h.natDegree * primaryMultiplicity (spEnd x) h) =
        2 * ∑ h ∈ P, h.natDegree * primaryMultiplicity (spEnd x) h := (Finset.mul_sum _ _ _).symm
    omega
  ·
    ext t
    constructor
    · intro ht
      obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective t
      refine ⟨g, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at ht
      have hc := commute_of_map_commute (proj r K) hZc hZp hx (g := g)
        (by rw [hxa]; exact ht)
      exact hc.eq
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hxa, ← map_mul, ← map_mul, hg]

end Proof

end CFSG.RankThree.Classical
