module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open SpinFrame

section Twisted

variable {m : ℕ} (hn : 4 ≤ m + 1) {L : Type} [Field L] (θ : L →+* L)

@[expose] def sigmaGL : GL (DI (m + 1)) L →* GL (DI (m + 1)) L :=
  ((tauM m).reindexGL L).toMonoidHom.comp (Matrix.GeneralLinearGroup.map θ)

theorem coe_sigmaGL (A : GL (DI (m + 1)) L) :
    ((sigmaGL θ A : GL (DI (m + 1)) L) : Matrix (DI (m + 1)) (DI (m + 1)) L) =
      ((A : Matrix (DI (m + 1)) (DI (m + 1)) L).map θ).submatrix (tauM m) (tauM m) := by
  rw [sigmaGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.coe_reindexGL,
    Equiv.symm_swap]
  rfl

@[expose] def twistedPoints : Subgroup (points (m + 1) hn L) :=
  (fixedSubgroup (sigmaGL θ)).comap (orthPoints (m + 1) hn L)

theorem mem_twistedPoints_iff (g : points (m + 1) hn L) :
    g ∈ twistedPoints hn θ ↔
      (((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L).map θ).submatrix (tauM m) (tauM m) =
        ((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
          Matrix (DI (m + 1)) (DI (m + 1)) L) := by
  rw [twistedPoints, Subgroup.mem_comap, mem_fixedSubgroup, Units.ext_iff, coe_sigmaGL]

end Twisted

section Steinberg

variable {m : ℕ} (hn : 4 ≤ m + 1) {L : Type} [Field L] (p : ℕ) [ExpChar L p] (k : ℕ)

abbrev steinbergTD : points (m + 1) hn L →* points (m + 1) hn L :=
  (graphAutPoints (m + 1) hn L).toMonoidHom.comp (frobenius (m + 1) hn p k L)

theorem orthPoints_steinbergTD (g : points (m + 1) hn L) :
    ((orthPoints (m + 1) hn L (steinbergTD hn p k g) : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L) =
      (((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L).map (iterateFrobenius L p k)).submatrix (tauM m)
          (tauM m) := by
  rw [steinbergTD, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, orthPoints_graphAutPoints,
    orthPoints_frobenius]
  rfl

theorem fixedSubgroup_le_twistedPoints :
    fixedSubgroup (steinbergTD hn p k) ≤ twistedPoints hn (iterateFrobenius L p k) := by
  intro g hg
  rw [mem_twistedPoints_iff, ← orthPoints_steinbergTD, (mem_fixedSubgroup.mp hg)]

theorem inv_mul_steinbergTD_mem_ker {g : points (m + 1) hn L}
    (hg : g ∈ twistedPoints hn (iterateFrobenius L p k)) :
    g⁻¹ * steinbergTD hn p k g ∈ (orthPoints (m + 1) hn L).ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have h := (mem_twistedPoints_iff hn _ g).mp hg
  rw [← orthPoints_steinbergTD] at h
  rw [Units.ext h, inv_mul_cancel]

theorem inv_mul_steinbergTD_mem_center (g : twistedPoints hn (iterateFrobenius L p k)) :
    (g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g ∈ Subgroup.center (points (m + 1) hn L) :=
  orthPoints_ker_le_center (m + 1) hn L (inv_mul_steinbergTD_mem_ker hn p k g.2)

@[expose] def deltaTD : twistedPoints hn (iterateFrobenius L p k) →*
    Subgroup.center (points (m + 1) hn L) where
  toFun g := ⟨(g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g,
    inv_mul_steinbergTD_mem_center hn p k g⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    have hc := Subgroup.mem_center_iff.mp (inv_mul_steinbergTD_mem_center hn p k g)
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    calc (h : points (m + 1) hn L)⁻¹ * (g : points (m + 1) hn L)⁻¹ *
          (steinbergTD hn p k g * steinbergTD hn p k h)
        = (h : points (m + 1) hn L)⁻¹ * ((g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g) *
            steinbergTD hn p k h := by group
      _ = ((g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g) * (h : points (m + 1) hn L)⁻¹ *
            steinbergTD hn p k h := by rw [hc]
      _ = _ := by group

theorem commutator_twistedPoints_le :
    _root_.commutator (twistedPoints hn (iterateFrobenius L p k)) ≤
      (fixedSubgroup (steinbergTD hn p k)).subgroupOf
        (twistedPoints hn (iterateFrobenius L p k)) := by
  intro g hg
  have h := Abelianization.commutator_subset_ker (deltaTD hn p k) hg
  rw [MonoidHom.mem_ker] at h
  rw [Subgroup.mem_subgroupOf, mem_fixedSubgroup]
  have h' : (g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g = 1 := congrArg Subtype.val h
  calc steinbergTD hn p k g = (g : points (m + 1) hn L) *
        ((g : points (m + 1) hn L)⁻¹ * steinbergTD hn p k g) := by group
    _ = g := by rw [h', mul_one]

end Steinberg

section Candidate

variable {m : ℕ} (hn : 4 ≤ m + 1) {L : Type} [Field L] (p : ℕ) [ExpChar L p] (k : ℕ)
  (S : Subfield L) (hS : ∀ x, x ∈ S ↔ iterateFrobenius L p k x = x) {ω : L}
  (hω : ω ≠ iterateFrobenius L p k ω)
  (hθω : iterateFrobenius L p k (iterateFrobenius L p k ω) = ω)

@[expose] def psiFixed : fixedSubgroup (steinbergTD hn (L := L) p k) →* GL (MI m) S :=
  (psiS hn (iterateFrobenius L p k) S hS hω hθω (twistedPoints hn (iterateFrobenius L p k))
    (mem_twistedPoints_iff hn _)).comp
      (Subgroup.inclusion (fixedSubgroup_le_twistedPoints hn p k))

theorem psiFixed_ker_le_center :
    (psiFixed hn p k S hS hω hθω).ker ≤ Subgroup.center _ := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h1 := congrArg (Matrix.GeneralLinearGroup.map S.subtype) hg
  rw [psiFixed, MonoidHom.comp_apply, map_psiS, map_one, psiL_apply] at h1
  have h2 : orthPoints (m + 1) hn L (g : points (m + 1) hn L) = 1 :=
    conjGL_injective _ (h1.trans (map_one _).symm)
  have hc := orthPoints_ker_le_center (m + 1) hn L (MonoidHom.mem_ker.mpr h2)
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)

theorem commutator_range_psiFixed [Finite S] :
    ⁅(psiFixed hn p k S hS hω hθω).range, (psiFixed hn p k S hS hω hθω).range⁆ =
      StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
        (coefC (iterateFrobenius L p k) S hS hθω)) := by
  set ψ' := psiS hn (iterateFrobenius L p k) S hS hω hθω
    (twistedPoints hn (iterateFrobenius L p k)) (mem_twistedPoints_iff hn _)
  have hle : (psiFixed hn p k S hS hω hθω).range ≤ ψ'.range := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  have hΩ := commutator_range_psiS hn (iterateFrobenius L p k) S hS hω hθω
    (twistedPoints hn (iterateFrobenius L p k)) (mem_twistedPoints_iff hn _)
  have hge : StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
      (coefC (iterateFrobenius L p k) S hS hθω)) ≤ (psiFixed hn p k S hS hω hθω).range := by
    rw [← hΩ, ← Subgroup.map_top, ← Subgroup.map_commutator, ← _root_.commutator_def]
    rintro _ ⟨g, hg, rfl⟩
    have hgF := commutator_twistedPoints_le hn p k hg
    rw [Subgroup.mem_subgroupOf] at hgF
    exact ⟨⟨g, hgF⟩, rfl⟩
  apply le_antisymm
  · rw [← hΩ]
    exact Subgroup.commutator_mono hle hle
  · have hperf := isPerfect_statedOmega_quadMinus (K := S) (n := m + 1) hn
      (coef_irreducible _ S hS hθω hω)
    have e : ⁅StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
        (coefC (iterateFrobenius L p k) S hS hθω)),
        StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
        (coefC (iterateFrobenius L p k) S hS hθω))⁆ =
        StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
          (coefC (iterateFrobenius L p k) S hS hθω)) := by
      rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← e]
    exact Subgroup.commutator_mono hge hge

def dcqEquivTwistedFixed [Finite S] :
    DerivedCentralQuotient (fixedSubgroup (steinbergTD hn (L := L) p k)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus (m + 1) S
        (coefB (iterateFrobenius L p k) S hS hθω) (coefC (iterateFrobenius L p k) S hS hθω))) := by
  have hperf := isPerfect_statedOmega_quadMinus (K := S) (n := m + 1) hn
    (coef_irreducible _ S hS hθω hω)
  have e : ⁅StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
      (coefC (iterateFrobenius L p k) S hS hθω)),
      StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
      (coefC (iterateFrobenius L p k) S hS hθω))⁆ =
      StatedOmega (StatedQuadMinus (m + 1) S (coefB (iterateFrobenius L p k) S hS hθω)
        (coefC (iterateFrobenius L p k) S hS hθω)) := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  exact (dcqEquivOfCentralKernel (psiFixed hn p k S hS hω hθω)
    (psiFixed_ker_le_center hn p k S hS hω hθω)
    (commutator_range_psiFixed hn p k S hS hω hθω) e).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadMinus hn
      (coef_irreducible _ S hS hθω hω)))

end Candidate

theorem exists_typeTwistedDGroupEquivStatedProj_of_valid (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) :
    ∃ b c : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩),
      (∀ s, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩ ≃*
          StatedProj (StatedOmega
            (StatedQuadMinus r ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hS : ∀ x, x ∈ ValidLieTypeIndex.fixedField ⟨.twistedD (m + 1) q, hv⟩ ↔
      iterateFrobenius (ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.twistedD (m + 1) q, hv⟩) x = x := by
    intro x
    rw [ValidLieTypeIndex.mem_fixedField, iterateFrobenius_def,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.twistedD (m + 1) q, hv⟩
  obtain ⟨ω, hω, hθω⟩ := exists_twist_root _ _ hS
  exact ⟨coefB _ _ hS hθω, coefC _ _ hS hθω, coef_irreducible _ _ hS hθω hω,
    ⟨dcqEquivTwistedFixed hr _ _ _ hS hω hθω⟩⟩

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_typeTwistedD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    StatedClassicalModel G .POmegaMinus r q.p q.exponent := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨b, c, hbc, ⟨φ⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  refine ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_, b, c, hbc, ⟨e.trans φ⟩⟩
  rw [ValidLieTypeIndex.card_fixedField]
  simp [ValidLieTypeIndex.fieldOrder]

theorem catalogBridgeFor_twistedD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) :
    CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.twistedD r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeTwistedD r q hv e⟩))

theorem catalogBridgeFor_twistedD_odd (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (_hp : q.p ≠ 2) :
    CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.twistedD r q, hv⟩) :=
  catalogBridgeFor_twistedD r q hv

end CFSG.RankThree.PartTwo.Census
