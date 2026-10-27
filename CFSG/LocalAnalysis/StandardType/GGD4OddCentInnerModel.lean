module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerBridge
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
public import CFSG.RankThree.PartOne.S11d.OrthLayer
import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open Polynomial Module
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne (piOrth)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev omBridge : Om8 K ≃* ProjOrthDerived (coordinateQuadPlus 4 K) :=
  projEquiv8.trans (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K)
    (by norm_num : 0 < 2 * 4))

noncomputable abbrev omLift (s : Om8 K) : orthDerived (coordinateQuadPlus 4 K) :=
  CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K) s

theorem omBridge_apply (s : Om8 K) :
    omBridge s = piOrth (coordinateQuadPlus 4 K) (omLift s) :=
  bridge_apply_eq_mk s

omit [Finite K] [CharP K 2] in
theorem omFixDim_eq_finrank_fixedSpace_omLift (s : Om8 K) :
    D4Rank.omFixDim s = finrank K (fixedSpace
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) := by
  refine congrArg (fun W : Submodule K (Fin (2 * 4) → K) => finrank K W) ?_
  ext v
  rw [D4Rank.mem_ker_omRep_sub_one, mem_fixedSpace]
  rfl

omit [Finite K] [CharP K 2] in
theorem finrank_fixedSpace_omLift {s : Om8 K} (hd : D4Rank.omFixDim s = 2) :
    finrank K (fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) = 2 := by
  rw [← omFixDim_eq_finrank_fixedSpace_omLift, hd]

omit [Finite K] [CharP K 2] in
theorem omLift_ne_one {s : Om8 K} (hd : D4Rank.omFixDim s = 2) :
    (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ≠ 1 := by
  intro h1
  have h2 := finrank_fixedSpace_omLift hd
  rw [h1] at h2
  have htop : fixedSpace (1 : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) = ⊤ :=
    eq_top_iff.2 fun v _ => mem_fixedSpace.2 rfl
  rw [htop, finrank_top, finrank_fin_fun] at h2
  omega

omit [Finite K] [CharP K 2] in
theorem orderOf_omLift {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    orderOf (omLift s) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← map_pow, hs3, map_one]) fun h1 => omLift_ne_one hd ?_
  rw [h1]
  rfl

theorem oddOrderIsometry_omLift {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    OddOrderIsometry (coordinateQuadPlus 4 K) 3
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :=
  oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [ringChar.eq K 2]; norm_num)
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus 4 K
      (by norm_num)).1 _ (orderOf_omLift hs3 hd)

omit [Field K] [Finite K] [CharP K 2] in
theorem three_dvd_card_add_one {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) :
    3 ∣ Nat.card K + 1 := by
  simpa [hK] using Odd.nat_add_dvd_pow_add_pow 2 1 hn

theorem eq_phi_of_mem_primaryFactors_omLift {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) {h : K[X]}
    (hh : h ∈ primaryFactors
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)).toLinearMap)
    (hne : h ≠ X - 1) : h = X ^ 2 + X + 1 :=
  CFSG.HardMathSupport.Dickson.Bal207.OrthFix.eq_phi (oddOrderIsometry_omLift hs3 hd)
    (three_dvd_card_add_one hK hn) hh hne

theorem phi_mem_primaryFactors_omLift {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)).toLinearMap :=
  CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem (oddOrderIsometry_omLift hs3 hd)
    (three_dvd_card_add_one hK hn) (omLift_ne_one hd)

theorem primaryMultiplicity_phi_omLift {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    primaryMultiplicity (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)).toLinearMap
      (X ^ 2 + X + 1) = 3 := by
  have hx := oddOrderIsometry_omLift hs3 hd
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have hsum := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
  rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_eq hx
      (three_dvd_card_add_one hK hn) hmem,
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.finrank_phi hmem, finrank_fixedSpace_omLift hd,
    finrank_fin_fun] at hsum
  omega

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Dickson.Bal207.OrthFix

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {x : V ≃ₗ[F] V}

theorem exists_specialBlock_phi_mulEquiv_sesqSpecialUnitaryGroup {f : ℕ}
    (hFf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f) (hx : OddOrderIsometry Q 3 x) {φ : F[X]}
    [Fact (Irreducible φ)] (hφ : φ = X ^ 2 + X + 1) (hmem : φ ∈ primaryFactors x.toLinearMap) :
    ∃ (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
      (B : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ),
      B.IsSymm ∧ B.SeparatingLeft ∧
        Nonempty (↥(specialBlock Q x φ) ≃* ↥(sesqSpecialUnitaryGroup B)) := by
  classical
  have hirr : Irreducible φ := Fact.out
  have hne1 : φ ≠ X - 1 := by rw [hφ]; exact phi_ne
  have hself : φ = reciprocalPolynomial φ := by
    have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := monic_phi.2
    have hc : (X ^ 2 + X + 1 : F[X]).coeff 0 = 1 := by simp
    have h1 : (reflect 2 X : F[X]) = X := by
      have := reflect_monomial (R := F) 2 1
      simpa [revAt_le] using this
    rw [hφ]
    unfold reciprocalPolynomial Polynomial.reverse
    rw [hdeg, hc]
    simp [reflect_add, h1]
    ring
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian ⟨1, rfl⟩ hmem hne1 hself
  have hd1 : d = 1 := by
    have h2 : φ.natDegree = 2 := by rw [hφ]; exact monic_phi.2
    omega
  subst hd1
  have : Module.Finite F (AdjoinRoot φ) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot φ) = 2 ^ (2 * f) := by
    rw [Module.natCard_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg, hFf, ← pow_mul]
    ring_nf
  have hU : UnitaryFieldData 2 f (AdjoinRoot φ) := ⟨Nat.prime_two, hf1, hcardE⟩
  have hbar' : ∀ z, frobPow F (AdjoinRoot φ) 1 z = hU.bar z := fun z => by
    rw [frobPow_apply, UnitaryFieldData.bar_apply, hFf, pow_one]
  let B : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hmem hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x φ).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hmem hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hrangeSU : (specialBlockGL Q x φ).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup, hrange]
  exact ⟨hU, B, hBsymm, hBl, ⟨(MonoidHom.ofInjective (hx.specialBlockGL_injective hmem)).trans
    (MulEquiv.subgroupCongr hrangeSU)⟩⟩

theorem isQuasisimple_specialBlock_phi {f : ℕ} (hFf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hx : OddOrderIsometry Q 3 x) {φ : F[X]} [Fact (Irreducible φ)] (hφ : φ = X ^ 2 + X + 1)
    (hmem : φ ∈ primaryFactors x.toLinearMap) (hm3 : 3 ≤ primaryMultiplicity x.toLinearMap φ)
    (hmq : ¬(primaryMultiplicity x.toLinearMap φ = 3 ∧ 2 ^ f = 2)) :
    CFSG.IsQuasisimple ↥(specialBlock Q x φ) := by
  obtain ⟨hU, B, hBsymm, hBl, ⟨e₁⟩⟩ :=
    exists_specialBlock_phi_mulEquiv_sesqSpecialUnitaryGroup hFf hf1 hx hφ hmem
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
    (isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl hm3 fun h' => ?_)
  exact hmq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

theorem nonempty_specialBlock_phi_mulEquiv_statedSU {f : ℕ} (hFf : Nat.card F = 2 ^ f)
    (hf1 : 1 ≤ f) (hx : OddOrderIsometry Q 3 x) {φ : F[X]} [Fact (Irreducible φ)]
    (hφ : φ = X ^ 2 + X + 1) (hmem : φ ∈ primaryFactors x.toLinearMap) :
    Nat.card (AdjoinRoot φ) = (2 ^ f) ^ 2 ∧
      Nonempty (↥(specialBlock Q x φ) ≃*
        ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap φ) (2 ^ f) (AdjoinRoot φ))) := by
  obtain ⟨hU, B, hBsymm, hBl, ⟨e₁⟩⟩ :=
    exists_specialBlock_phi_mulEquiv_sesqSpecialUnitaryGroup hFf hf1 hx hφ hmem
  have := hU.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.charP
  have hE : Nat.card (AdjoinRoot φ) = (2 ^ f) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
  obtain ⟨e₂⟩ :=
    CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU e₀ he₀
  have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
      (primaryMultiplicity x.toLinearMap φ) =
      CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap φ) (2 ^ f) (AdjoinRoot φ) := by
    rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
  exact ⟨hE, ⟨e₁.trans (e₂.trans (MulEquiv.subgroupCongr hS))⟩⟩

end Unitary

theorem isQuasisimple_specialBlock_phi_omLift {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    CFSG.IsQuasisimple ↥(specialBlock (coordinateQuadPlus 4 K)
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1)) := by
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have hm := primaryMultiplicity_phi_omLift hK hn hs3 hd
  refine isQuasisimple_specialBlock_phi hK (by omega) (oddOrderIsometry_omLift hs3 hd) rfl hmem
    hm.ge fun h => ?_
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  omega

theorem exists_specialBlock_phi_omLift_mulEquiv_statedSU {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Odd n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ n) ^ 2 ∧
      Nonempty (↥(specialBlock (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1)) ≃*
          ↥(CFSG.Open.StatedSU 3 (2 ^ n) E)) := by
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have hn1 : 1 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  obtain ⟨hE, he⟩ := nonempty_specialBlock_phi_mulEquiv_statedSU hK hn1
    (oddOrderIsometry_omLift hs3 hd) rfl hmem
  rw [primaryMultiplicity_phi_omLift hK hn hs3 hd] at he
  have : Finite (AdjoinRoot (X ^ 2 + X + 1 : K[X])) := Nat.finite_of_card_ne_zero (by
    rw [hE]; positivity)
  exact ⟨AdjoinRoot (X ^ 2 + X + 1 : K[X]), inferInstance, inferInstance, hE, he⟩

theorem map_centralizer_omBridge (s : Om8 K) :
    (Subgroup.centralizer ({s} : Set (Om8 K))).map (omBridge (K := K)).toMonoidHom =
      centralizerImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) := by
  rw [CFSG.RankThree.PartOne.centralizerImage_eq
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus 4 K
      (by norm_num)).1, ← omBridge_apply]
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    show omBridge z * omBridge s = omBridge s * omBridge z
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨omBridge.symm y, ?_, omBridge.apply_symm_apply y⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply omBridge.injective
    rw [map_mul, map_mul, omBridge.apply_symm_apply, hy]

theorem commutator_centralizerImage_le_componentImage_phi {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Odd n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ⁅centralizerImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)),
      centralizerImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))⁆ ≤
      componentImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  classical
  set Q := coordinateQuadPlus 4 K with hQdef
  have hQ := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    4 K (by norm_num)).1
  set xe : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    ((omLift s : orthDerived Q) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) with hxe
  have hx : OddOrderIsometry Q 3 xe := oddOrderIsometry_omLift hs3 hd
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K (Fin (2 * 4) → K)).subgroupOf
      (orthDerived Q)) with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  have hspΦ : specialProduct Q xe Rep ≤ specialBlock Q xe (X ^ 2 + X + 1) := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    rw [eq_phi_of_mem_primaryFactors_omLift hK hn hs3 hd (hRep.1 hh) hne]
  have hspM : specialProduct Q xe Rep ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hdim2 : finrank K (fixedSpace xe) ≤ 2 := (finrank_fixedSpace_omLift hd).le
  have hkey : ⁅Mo, Mo⁆ ≤ (componentImage Q xe (X ^ 2 + X + 1)).comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    rw [Subgroup.mem_comap]
    have hmM : (m : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈ isometryCentralizer Q xe :=
      Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈ isometryCentralizer Q xe :=
      Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
    have hfM : f ∈ isometryCentralizer Q xe := supportedFixedDerived_le_isometryCentralizer hf
    have hjM : j ∈ isometryCentralizer Q xe := hspM hj
    have hgM : (((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
        isometryCentralizer Q xe := by
      rw [hgjf]
      exact mul_mem hjM hfM
    have h1 : isometryRestrictFixed Q xe
        ⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)), hgM⟩ =
          1 := by
      have h2 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)),
          hgM⟩ : ↥(isometryCentralizer Q xe)) =
          ⁅(⟨(m : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)), hmM⟩ : ↥(isometryCentralizer Q xe)),
            (⟨(m' : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)), hm'M⟩ :
              ↥(isometryCentralizer Q xe))⁆ :=
        Subtype.ext rfl
      rw [h2, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hx.restrict_commute_of_mem_orthDerived ⟨1, rfl⟩ hQ hRep hdim2 hmM m.2 hm'M m'.2).eq
    have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
      have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)),
          hgM⟩ : ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
      rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM,
        one_mul] at h1
      exact h1
    have hfB := supportedFixedDerived_le_supportedBlock hf
    have h5 : restrictFixed Q xe ⟨f, hfB⟩ = 1 := by
      rw [← isometryRestrictFixed_restrictFixed]
      exact h3
    have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
    have hjΦ : (((⁅m, m'⁆ : ↥(orthDerived Q))) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
        specialBlock Q xe (X ^ 2 + X + 1) := by
      rw [hgjf, hf1, mul_one]
      exact hspΦ hj
    exact ⟨⁅m, m'⁆, Subgroup.mem_subgroupOf.mpr hjΦ, rfl⟩
  show ⁅Mo.map ρ, Mo.map ρ⁆ ≤ _
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_le_iff_le_comap.mpr hkey

theorem map_centDer_le_componentImage_phi {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    (centDer s).map (omBridge (K := K)).toMonoidHom ≤
      componentImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  rw [centDer, Subgroup.map_commutator, map_centralizer_omBridge]
  exact commutator_centralizerImage_le_componentImage_phi hK hn hs3 hd

theorem ggAutFixedSubgroup_conj_eq_centralizer {X : Type*} [Group X] (s : X) :
    ggAutFixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set X) := by
  ext g
  rw [mem_ggAutFixedSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem map_eq_componentImage_phi_of_isComponentOf {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Odd n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2)
    {J : Subgroup (Om8 K)} (hJ : IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s))) :
    J.map (omBridge (K := K)).toMonoidHom =
      componentImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  classical
  have hQ := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    4 K (by norm_num)).1
  have hx := oddOrderIsometry_omLift hs3 hd
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hJE := isComponentOf_map_mulEquiv (omBridge (K := K)) hJ
  rw [ggAutFixedSubgroup_conj_eq_centralizer, map_centralizer_omBridge] at hJE
  rcases CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.isComponentOf_centralizerImage_cases hQ
      Nat.prime_three (by norm_num) (omLift s) hx hRep (isComponentOf_iff_open.1 hJE) with
    ⟨h, hh, hne, -, hI⟩ | ⟨hlist, -⟩
  · rw [hI, eq_phi_of_mem_primaryFactors_omLift hK hn hs3 hd (hRep.1 hh) hne]
  · have h3 := hlist.1
    rw [finrank_fixedSpace_omLift hd] at h3
    omega

theorem specialBlock_phi_omLift_le_orthDerived {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    specialBlock (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) ≤
      orthDerived (coordinateQuadPlus 4 K) :=
  specialBlock_le_orthDerived_of_perfect (isQuasisimple_specialBlock_phi_omLift hK hn hn3 hs3 hd).1
    ((specialBlock_le_isometryCentralizer _).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)

theorem isQuasisimple_componentImage_phi_omLift {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    CFSG.IsQuasisimple ↥(componentImage (coordinateQuadPlus 4 K)
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1)) :=
  isQuasisimple_map_projective (specialBlock_phi_omLift_le_orthDerived hK hn hn3 hs3 hd)
    (isQuasisimple_specialBlock_phi_omLift hK hn hn3 hs3 hd)

theorem map_centDer_eq_componentImage_phi {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    (centDer s).map (omBridge (K := K)).toMonoidHom =
      componentImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  refine le_antisymm (map_centDer_le_componentImage_phi hK hn hs3 hd) ?_
  rw [centDer, Subgroup.map_commutator, map_centralizer_omBridge]
  have hperf :=
    Subgroup.isPerfect_iff.1 (isQuasisimple_componentImage_phi_omLift hK hn hn3 hs3 hd).1
  calc _ = ⁅componentImage (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1),
        componentImage (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1)⁆ := hperf.symm
    _ ≤ _ := Subgroup.commutator_mono componentImage_le_centralizerImage
        componentImage_le_centralizerImage

theorem omLift_mem_specialBlock_phi {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      specialBlock (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  set xe : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    ((omLift s : orthDerived (coordinateQuadPlus 4 K)) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) with hxe
  have hx : OddOrderIsometry (coordinateQuadPlus 4 K) 3 xe := oddOrderIsometry_omLift hs3 hd
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have hsupp : xe ∈ supportedBlock (coordinateQuadPlus 4 K) xe (X ^ 2 + X + 1) := by
    refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr
      ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem, fun v => rfl⟩, ?_⟩
    refine fixes_othersSpace_iff.mpr fun k hk hkΦ _ v hv => ?_
    have hk1 : k = X - 1 := by
      by_contra hne
      exact hkΦ (eq_phi_of_mem_primaryFactors_omLift hK hn hs3 hd hk hne)
    subst hk1
    rw [mem_primaryComponent] at hv
    simpa [sub_eq_zero] using hv
  refine mem_specialBlock.mpr ⟨hsupp, ?_⟩
  rw [blockDet_apply]
  have hroot : ((blockGL (coordinateQuadPlus 4 K) xe (X ^ 2 + X + 1) ⟨xe, hsupp⟩ :
      BlockGL xe (X ^ 2 + X + 1)) : Module.End (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
        (primaryComponent xe.toLinearMap (X ^ 2 + X + 1))) =
      AdjoinRoot.root (X ^ 2 + X + 1 : K[X]) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [coe_blockGL, LinearMap.smul_apply, LinearMap.id_apply, coe_root_smul_primaryComponent]
    rfl
  rw [hroot, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hfin : finrank (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
      (primaryComponent xe.toLinearMap (X ^ 2 + X + 1)) = 3 :=
    primaryMultiplicity_phi_omLift hK hn hs3 hd
  rw [hfin]
  exact root_pow_eq_one (hx.dvd_X_pow_sub_one hmem)

theorem mem_centDer_self {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) : s ∈ centDer s := by
  have h1 : omBridge s ∈ (centDer s).map (omBridge (K := K)).toMonoidHom := by
    rw [map_centDer_eq_componentImage_phi hK hn hn3 hs3 hd, omBridge_apply]
    exact ⟨omLift s, Subgroup.mem_subgroupOf.mpr (omLift_mem_specialBlock_phi hK hn hs3 hd), rfl⟩
  obtain ⟨y, hy, hys⟩ := h1
  rwa [omBridge.injective hys] at hy

theorem center_centDer_ne_bot {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    Subgroup.center ↥(centDer s) ≠ ⊥ := by
  intro hbot
  have hmem := mem_centDer_self hK hn hn3 hs3 hd
  have hz : (⟨s, hmem⟩ : ↥(centDer s)) ∈ Subgroup.center ↥(centDer s) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hle : centDer s ≤ Subgroup.centralizer ({s} : Set (Om8 K)) :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)
  rw [hbot, Subgroup.mem_bot] at hz
  have hs1 : s = 1 := congrArg Subtype.val hz
  subst hs1
  exact omLift_ne_one hd (congrArg Subtype.val
    (map_one (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K))))

@[expose] noncomputable def centDerEquivSpecialBlockPhi {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Odd n) (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ↥(centDer s) ≃* ↥(specialBlock (coordinateQuadPlus 4 K)
      (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1)) :=
  ((Subgroup.equivMapOfInjective (centDer s) (omBridge (K := K)).toMonoidHom
      omBridge.injective).trans
    (MulEquiv.subgroupCongr (map_centDer_eq_componentImage_phi hK hn hn3 hs3 hd))).trans
    ((Subgroup.equivMapOfInjective _ (piOrth (coordinateQuadPlus 4 K))
      (CFSG.RankThree.PartOne.piOrth_injective
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
          4 K (by norm_num)).1)).symm.trans
      (Subgroup.subgroupOfEquivOfLe (specialBlock_phi_omLift_le_orthDerived hK hn hn3 hs3 hd)))

theorem exists_centDer_mulEquiv_statedSU {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ n) ^ 2 ∧
      Nonempty (↥(centDer s) ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n) E)) := by
  obtain ⟨E, hEf, hEfin, hE, ⟨e⟩⟩ := exists_specialBlock_phi_omLift_mulEquiv_statedSU hK hn hs3 hd
  exact ⟨E, hEf, hEfin, hE, ⟨(centDerEquivSpecialBlockPhi hK hn hn3 hs3 hd).trans e⟩⟩

end D4Inner

end CFSG.StandardType

end
