module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsCoordinates
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] {H L : Subgroup G} {z t : G} {beta : rightCosetSpace H}
  (F : UnitaryHullCoordinates H z beta t L)

@[expose] def hullTorus : Subgroup G :=
  (torusL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom)

theorem hullTorus_le : hullTorus F ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact (F.θ x).2

include F in
theorem pairHull_le : minimalLocalFailureProperPairHull H z beta t ≤ L := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (SetLike.ext_iff.mp F.subline x).mpr hx
  exact (F.θ y).2

include F in
theorem flip_mem : t ∈ L :=
  pairHull_le F (minimalLocalFailureProperPair_flip_mem H z beta t)

theorem rootHom_apply' (w : hermitianUnipotentCoord F.J) :
    F.rootHom w = (L.subtype.comp F.θ.toMonoidHom) (heisL F.J F.C F.hJ w) :=
  rfl

theorem rootHom_mem_iff (w : hermitianUnipotentCoord F.J) :
    F.rootHom w ∈ minimalLocalFailurePairActionPointHull H z ↔ w.1.1 = 0 := by
  refine (SetLike.ext_iff.mp F.upper (F.rootHom w)).symm.trans ⟨?_, ?_⟩
  · rintro ⟨x, hx, hxw⟩
    rw [rootHom_apply'] at hxw
    obtain ⟨v, hv0, rfl⟩ := (mem_upperRootL_iff F.hJ x).mp hx
    rw [← heisL_injective F.hJ F.hC (F.map_injective hxw)]
    exact hv0
  · intro h0
    exact ⟨heisL F.J F.C F.hJ w, (mem_upperRootL_iff F.hJ _).mpr ⟨w, h0, rfl⟩, rfl⟩

theorem le_root : minimalLocalFailurePairActionPointHull H z ≤ F.root := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (SetLike.ext_iff.mp F.upper y).mpr hy
  obtain ⟨v, -, rfl⟩ := (mem_upperRootL_iff F.hJ x).mp hx
  exact ⟨v, rfl⟩

theorem root_commute {x y : G} (hx : x ∈ F.root)
    (hy : y ∈ minimalLocalFailurePairActionPointHull H z) : x * y = y * x := by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := le_root F hy
  rw [← map_mul, ← map_mul, (mul_comm_of_fst_eq_zero F.J ((rootHom_mem_iff F v).mp hy) w).symm]

theorem mem_root_of_pow_eq_one [Finite G] {x : G} (hxL : x ∈ L) (hxH : x ∈ H) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ F.root := by
  set y := F.θ.symm ⟨x, hxL⟩
  have hy : coverToPGL F.J F.C F.hJ F.hC y • unitaryCoordinatePoint (K := F.k) 0 =
      unitaryCoordinatePoint 0 := (F.mem_point y).mp (by rw [MulEquiv.apply_symm_apply]; exact hxH)
  have hyk : y ^ 2 ^ k = 1 := F.θ.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact Subtype.ext hk)
  obtain ⟨w, hw⟩ := mem_range_heisL_of_pow_eq_one F.hf F.hcard F.hfixed F.hJ F.hC hy hyk
  exact ⟨w, by rw [F.rootHom_apply, hw, MulEquiv.apply_symm_apply]⟩

theorem flip_coset (hbt : beta = rightCosetMk H t) :
    rightCosetMk H (F.θ (F.flipElt (flip_mem F)) : G) = beta := by
  rw [F.θ_flipElt, hbt]

theorem rootHom_eq_one_of_fixes (hbt : beta = rightCosetMk H t)
    (hbeta : beta ≠ rightCosetMk H 1) {w : hermitianUnipotentCoord F.J}
    (hw : rightCosetTranslate H beta (F.rootHom w) = beta) : w = 1 := by
  have hb := flip_coset F hbt
  have hne : rightCosetMk H (F.θ (F.flipElt (flip_mem F)) : G) ≠ rightCosetMk H 1 :=
    fun h => hbeta (hb.symm.trans h)
  obtain ⟨w₀, -, huniq⟩ := F.root_regular _ _ hne hne
  have hw' := ((congrArg (fun ω => rightCosetTranslate H ω (F.rootHom w)) hb).trans hw).trans
    hb.symm
  rw [huniq w hw', huniq 1 (by simp only [map_one, rightCosetTranslate_one])]

theorem eq_one_of_mem_root_of_fixes (hbt : beta = rightCosetMk H t)
    (hbeta : beta ≠ rightCosetMk H 1) {x : G} (hx : x ∈ F.root)
    (hfix : rightCosetTranslate H beta x = beta) : x = 1 := by
  obtain ⟨w, rfl⟩ := hx
  rw [rootHom_eq_one_of_fixes F hbt hbeta hfix, map_one]

theorem fst_eq_zero_of_translate_mem_baseOrbit (hbt : beta = rightCosetMk H t) (ht2 : t * t = 1)
    {w : hermitianUnipotentCoord F.J}
    (hw : rightCosetTranslate H beta (F.rootHom w) ∈
      baseOrbit H (minimalLocalFailureProperPairHull H z beta t)) : w.1.1 = 0 := by
  obtain ⟨k, hk, hkω⟩ := hw
  obtain ⟨y, hy, rfl⟩ := (SetLike.ext_iff.mp F.subline k).mpr hk
  have htL := flip_mem F
  set τ := F.flipElt htL
  have h1 : rightCosetTranslate H beta (F.rootHom w) =
      rightCosetMk H (F.θ (τ * heisL F.J F.C F.hJ w) : G) := by
    refine (congrArg (fun ω => rightCosetTranslate H ω (F.rootHom w)) hbt).trans ?_
    simp only [rightCosetTranslate_mk, map_mul, Subgroup.coe_mul, τ, F.θ_flipElt htL]
    rfl
  rw [h1] at hkω
  have h2 := (F.coset_eq_iff y (τ * heisL F.J F.C F.hJ w)).mp hkω
  have h3 : coverToPGL F.J F.C F.hJ F.hC (τ * heisL F.J F.C F.hJ w)⁻¹ •
      unitaryCoordinatePoint (K := F.k) 0 =
      coverToPGL F.J F.C F.hJ F.hC (heisL F.J F.C F.hJ w⁻¹) • unitaryCoordinatePoint 2 := by
    rw [_root_.mul_inv_rev, F.flipElt_inv htL ht2, map_mul, mul_smul, F.flipElt_smul htL,
      map_inv (heisL F.J F.C F.hJ)]
  have hmem : coverToPGL F.J F.C F.hJ F.hC (heisL F.J F.C F.hJ w⁻¹) •
      unitaryCoordinatePoint (K := F.k) 2 ∈ sublineOrbit F.J F.C F.hJ F.hC :=
    ⟨y⁻¹, inv_mem hy, by rw [h2, h3]⟩
  have h4 := fst_eq_zero_of_heisL_smul_mem_sublineOrbit F.hJ F.hC _ hmem
  rwa [fst_inv, neg_eq_zero] at h4

theorem hullTorus_le_pair (hbt : beta = rightCosetMk H t) (ht2 : t * t = 1) :
    hullTorus F ≤ pairPointStabilizer H beta := by
  rintro _ ⟨x, hx, rfl⟩
  exact (F.mem_pairPointStabilizer_iff (flip_mem F) ht2 hbt x).mpr
    (torusL_le_pairStabilizerL F.hJ F.hC hx)

theorem hullTorus_commute {x y : G} (hx : x ∈ hullTorus F)
    (hy : y ∈ minimalLocalFailureProperPairHull H z beta t) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := (SetLike.ext_iff.mp F.subline y).mpr hy
  rw [← map_mul, ← map_mul, sublineL_commute_torusL F.hJ b hb a ha]

@[expose] def torusElt (c : normOne F.J) : G :=
  (L.subtype.comp F.θ.toMonoidHom) (QuotientGroup.mk' F.C (torusHom F.J F.hJ c))

theorem torusElt_mem (c : normOne F.J) : torusElt F c ∈ hullTorus F :=
  ⟨_, ⟨c, rfl⟩, rfl⟩

theorem mem_hullTorus_iff {x : G} : x ∈ hullTorus F ↔ ∃ c, torusElt F c = x := by
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact torusElt_mem F c

theorem torusElt_inv (c : normOne F.J) : (torusElt F c)⁻¹ = torusElt F c⁻¹ := by
  rw [torusElt, torusElt, ← map_inv, ← map_inv, ← map_inv]

theorem torusElt_conj (c : normOne F.J) (w : hermitianUnipotentCoord F.J) :
    torusElt F c * F.rootHom w * (torusElt F c)⁻¹ = F.rootHom (torusCoord c w) := by
  rw [torusElt, rootHom_apply', rootHom_apply', ← map_inv, ← map_mul, ← map_mul,
    torus_conj_heisL]

theorem torusElt_conj_mem (c : normOne F.J) {x : G} (hx : x ∈ F.root) :
    torusElt F c * x * (torusElt F c)⁻¹ ∈ F.root := by
  obtain ⟨w, rfl⟩ := hx
  rw [torusElt_conj]
  exact ⟨_, rfl⟩

theorem hullTorus_le_normalizer : hullTorus F ≤ Subgroup.normalizer (F.root : Set G) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_hullTorus_iff F).mp hx
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨torusElt_conj_mem F c, fun hy => ?_⟩
  have h := torusElt_conj_mem F c⁻¹ hy
  rwa [← torusElt_inv, inv_inv, show (torusElt F c)⁻¹ * (torusElt F c * y * (torusElt F c)⁻¹) *
    torusElt F c = y by group] at h

theorem hullTorus_isCyclic_odd [Finite G] :
    IsCyclic (hullTorus F) ∧ Odd (Nat.card (hullTorus F)) := by
  obtain ⟨-, -, -, -, -, -, -, hcyc, -⟩ :=
    unitary_central_cover_subline_torus_centralizer F.J F.f F.hf F.hcard F.hfixed F.hJ F.C F.hC
  have e : torusL F.J F.C F.hJ ≃* hullTorus F :=
    Subgroup.equivMapOfInjective _ _ F.map_injective
  refine ⟨isCyclic_of_surjective e.toMonoidHom e.surjective, ?_⟩
  have hq : 2 < 2 ^ F.f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos F.hf)
  have hM : Nat.card (normOne F.J) = 2 ^ F.f + 1 :=
    card_normOne Nat.prime_two hq F.hcard F.hfixed
  have hmul := card_torusL_mul_card (C := F.C) F.hJ F.hC
  rw [hM] at hmul
  have hodd : Odd (2 ^ F.f + 1) := (Nat.even_pow.mpr ⟨even_two, by have := F.hf; omega⟩).add_one
  rw [← Nat.card_congr e.toEquiv]
  rw [← hmul] at hodd
  exact Nat.Odd.of_mul_left hodd

theorem mem_hullTorus_of_mem_pair (hbt : beta = rightCosetMk H t) (ht2 : t * t = 1) {x : G}
    (hxL : x ∈ L) (hxB : x ∈ pairPointStabilizer H beta)
    (hxQ : x ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G)) :
    x ∈ hullTorus F := by
  set y := F.θ.symm ⟨x, hxL⟩
  have hyx : (F.θ y : G) = x := by rw [MulEquiv.apply_symm_apply]
  have hyB : y ∈ pairStabilizerL F.J F.C F.hJ F.hC :=
    (F.mem_pairPointStabilizer_iff (flip_mem F) ht2 hbt y).mp (hyx ▸ hxB)
  have hyQ : y ∈ Subgroup.centralizer (upperRootL F.J F.C F.hJ : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    apply F.map_injective
    have hvQ : (L.subtype.comp F.θ.toMonoidHom) v ∈ minimalLocalFailurePairActionPointHull H z :=
      (SetLike.ext_iff.mp F.upper _).mp ⟨v, hv, rfl⟩
    rw [map_mul, map_mul]
    change _ * (F.θ y : G) = (F.θ y : G) * _
    rw [hyx]
    exact Subgroup.mem_centralizer_iff.mp hxQ _ hvQ
  exact ⟨y, (pairStabilizerL_inf_centralizer F.hJ F.hC).le ⟨hyB, hyQ⟩, hyx⟩

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
