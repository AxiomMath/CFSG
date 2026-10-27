module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthBlock
import CFSG.RankThree.PartOne.KC.OrthogonalMatrixModelTransport
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.K159.RowFourFixed
import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section OrthTDFourAux

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.K159 CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal

private theorem orthTDFour_center_eq_bot
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center (ProjOrthDerived Q) = ⊥ :=
  CFSG.RankThree.PartOne.KCOrthogonalModel.center_projOrthDerived_eq_bot hQ hT

private theorem orthTDFour_conj_injective
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
  CFSG.RankThree.PartOne.KCOrthogonalD4.conj_injective_of_trivial_center
    (orthTDFour_center_eq_bot hQ hT)

private theorem orthTDFour_conj_lift
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q)) :
    ∃ a : ProjOrthDerived Q, MulAut.conj a = δ' ∧ a ^ 3 = 1 ∧ a ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a : ProjOrthDerived Q, MulAut.conj a = δ' :=
    hĀI δ' hR.mem
  have hδ3 : δ' ^ 3 = 1 := hR.elem.2 δ' hR.mem
  have hinj := orthTDFour_conj_injective hQ hT
  refine ⟨a, ha, ?_, ?_⟩
  · apply hinj
    rw [map_pow, ha, hδ3, map_one]
  · intro h1
    exact hR.ne_one (by rw [← ha, h1, map_one])

private theorem orthTDFour_lift_x
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    {a : ProjOrthDerived Q} (ha : MulAut.conj a = δ') (ha3 : a ^ 3 = 1) :
    ∃ x : ↥(orthDerived Q),
      QuotientGroup.mk'
          ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)) x = a ∧
      OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) ∧
      ((∃ h : K[X], h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧ h ≠ X - 1 ∧
          CFSG.IsQuasisimple
            ↥(CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q (x : V ≃ₗ[K] V) h) ∧
          J' = CFSG.RankThree.PartOne.KCOrthogonal.componentImage Q (x : V ≃ₗ[K] V) h) ∨
        ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧
          F ≤ CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
          (F.subgroupOf
            (CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
          J' = (F.subgroupOf (orthDerived Q)).map (QuotientGroup.mk'
            ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)))) := by
  have hcomp : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) := by
    refine CFSG.Assembly.isComponentOf_iff_open.mp ?_
    have h := hR.comp
    rw [← ha, CFSG.StandardType.D4Inner.ggAutFixedSubgroup_conj_eq_centralizer] at h
    exact h
  exact CFSG.LocalAnalysis.GLTheoremA.K1419.orth_component_named Nat.prime_three (by decide)
    hQ hT (by rw [ringChar.eq K 2]; decide) a ha3 J' hcomp


private theorem orthTDFour_labelIso_D4 {n : ℕ} {lab : LargeEvenLabel}
    (hiso : GGLabelIso (⟨.D, 4, n⟩ : LargeEvenLabel) lab) : lab = ⟨.D, 4, n⟩ := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h.symm
  · obtain ⟨h1, -⟩ := h
    rcases h1 with h1 | h1 <;> exact absurd h1 (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.rank h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨h1, -⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  · obtain ⟨-, h1⟩ := h
    exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)

private theorem orthTDFour_quasi_two_le
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn1 : 1 ≤ n)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1))
    (hn2 : 2 ≤ n) :
    CFSG.IsQuasisimple ↥(specialBlock Q x (X ^ 2 + X + 1)) := by
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem⟩
  obtain ⟨hU, B, hBsymm, hBl, ⟨e₁⟩⟩ :=
    CFSG.StandardType.D4Inner.exists_specialBlock_phi_mulEquiv_sesqSpecialUnitaryGroup
      hK hn1 hx rfl hmem
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hU hBsymm hBl hm ?_)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  exact ⟨fun _ => h4, fun _ => le_trans (by norm_num) h4⟩

private theorem orthTDFour_block_eq_fixed
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    (hxδ : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) = δ')
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    componentImage Q (x : V ≃ₗ[K] V) h = J' := by
  obtain ⟨x₀, Â, hx₀δ, hx₀, -, -, -, -, -, -, huniq_h, -, -⟩ := orthT_lift hQ hT hR hĀI
  have hconj : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x₀) =
      MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) := by
    rw [hx₀δ, hxδ]
  have hmk := orthTDFour_conj_injective hQ hT hconj
  haveI : Nontrivial V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K) (by have := Submodule.finrank_le U; omega)
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  have hx0x : x₀ = x := hinj hmk
  rw [hx0x] at huniq_h
  exact huniq_h h hh hne1 hq

private theorem orthTDFour_block_contra
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    (hxδ : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) = δ')
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hJeq : J' = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))))
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1))) : False := by
  have h1 : componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1) = J' :=
    orthTDFour_block_eq_fixed hQ hT hR hĀI hx hxδ hmem
      (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne) hq
  have h2 : (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))) ≠
      componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1) :=
    orthT_fixed_ne_block hQ hx hmem
      (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne) hq hFq hFle
  rw [hJeq] at h1
  exact h2 h1.symm

private theorem orthTDFour_specialBlock_impossible
    (hRig : GGLabelRigidInput)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {J' : Subgroup (ProjOrthDerived Q)} (hlab : GGHasLabel ⟨.D, 4, n⟩ (J' ⧸ Subgroup.center J'))
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (hJeq : J' = componentImage Q (x : V ≃ₗ[K] V) h) : False := by
  obtain ⟨k, hk⟩ := hn
  have hn1 : 1 ≤ n := by omega
  have hΛD : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel) :=
    ⟨by show 1 ≤ n; omega, by show 3 ≤ 4; norm_num⟩
  obtain ⟨hm2, -, hblock⟩ :=
    orthT_blockLabel hK hx hh hne1 hq (L := componentImage Q (x : V ≃ₗ[K] V) h) rfl
  rw [hJeq] at hlab
  rcases hblock with ⟨-, h3, hlabA⟩ | ⟨-, -, ⟨-, hn2, hlabA⟩ | ⟨hm3, hne, hlabTwA⟩⟩
  ·
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn_eq : n = 1 := by omega
      rw [hn_eq] at h3
      norm_num at h3
    have hΛA : LargeEvenInLambda2
        (⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
      ⟨by show 1 ≤ n; omega, by show 1 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1; omega,
        fun _ => hn2⟩
    have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel)
      (⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
      (componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛA hlab hlabA
    exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
  ·
    have hΛA : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
      ⟨by show 1 ≤ n; omega, by show 1 ≤ 1; norm_num, fun _ => hn2⟩
    have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel)
      (componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛA hlab hlabA
    exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
  ·
    have hΛtwA : LargeEvenInLambda2
        (⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel) :=
      ⟨by show 1 ≤ n; omega,
        by show 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1; omega,
        by
          show primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1 = 2 → 2 ≤ n
          intro hb
          by_contra hn2
          exact hne ⟨by omega, by omega⟩⟩
    have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel)
      (⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩ : LargeEvenLabel)
      (componentImage Q (x : V ≃ₗ[K] V) h ⧸
        Subgroup.center (componentImage Q (x : V ≃ₗ[K] V) h)) hΛD hΛtwA hlab hlabTwA
    exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)

private theorem orthTDFour_fixed_data
    (hRig : GGLabelRigidInput)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    (hlab : GGHasLabel ⟨.D, 4, n⟩ (J' ⧸ Subgroup.center J'))
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    (hx1 : (x : V ≃ₗ[K] V) ≠ 1)
    (hxδ : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) = δ')
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (hJeq : J' = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)))) :
    finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
      IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
      primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) ≤ 3 ∧
      (3 ≤ n → primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) ≤ 1) := by
  have hn1 : 1 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hΛD : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel) :=
    ⟨by show 1 ≤ n; omega, by show 3 ≤ 4; norm_num⟩
  obtain ⟨s, hs, hcases⟩ := orthT_fixedLabel hK hQ hx hFq hFle hFn (L := J') hJeq
  have hmain : s = 4 ∧ IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) := by
    rcases hcases with ⟨h4s, hplus, hlab'⟩ | ⟨h4s, -, hlab'⟩ | ⟨hs3, -, hlab'⟩ |
      ⟨hs3, -, hlab'⟩ | ⟨hs2, -, hlab'⟩ | ⟨hs2, -, hn2, hlab'⟩
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 3 ≤ s; omega⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.D, s, n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact ⟨congrArg LargeEvenLabel.rank (orthTDFour_labelIso_D4 hiso), hplus⟩
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 2 ≤ s; omega⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.twD, s, n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 1 ≤ 3; norm_num,
          by show (3 : ℕ) = 1 → 2 ≤ n; omega⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.A, 3, n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 2 ≤ 3; norm_num,
          by show (3 : ℕ) = 2 → 2 ≤ n; omega⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.twA, 3, n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ 2 * n; omega, by show 1 ≤ 1; norm_num,
          by show (1 : ℕ) = 1 → 2 ≤ 2 * n; omega⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.A, 1, 2 * n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
    ·
      have hΛ' : LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ n; omega, by show 1 ≤ 1; norm_num, fun _ => hn2⟩
      have hiso := hRig (⟨.D, 4, n⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel)
        (J' ⧸ Subgroup.center J') hΛD hΛ' hlab hlab'
      exact absurd (congrArg LargeEvenLabel.tag (orthTDFour_labelIso_D4 hiso)) (by simp)
  obtain ⟨hs4, hplus⟩ := hmain
  have hdim8 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 := by
    rw [hs, hs4]
  have hpq : 3 ∣ Nat.card K + 1 :=
    CFSG.StandardType.D4Inner.three_dvd_card_add_one (K := K) hK hn
  have hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hx hpq hx1
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem⟩
  refine ⟨hdim8, hplus, ?_, ?_⟩
  · by_contra hle
    have ht4 : 4 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) := by omega
    have hq := CFSG.StandardType.D4Inner.isQuasisimple_specialBlock_phi
      hK hn1 hx rfl hmem (by omega) (fun hc => by omega)
    exact orthTDFour_block_contra hQ hT hR hĀI hx hxδ hFq hFle hJeq hmem hq
  · intro hn3
    by_contra hle
    have ht2 : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) := by omega
    have hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1)) := by
      by_cases ht3 : 3 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1)
      · exact CFSG.StandardType.D4Inner.isQuasisimple_specialBlock_phi
          hK hn1 hx rfl hmem ht3
          (fun hc => by
            have h8 : 8 ≤ 2 ^ n := by
              calc 8 = 2 ^ 3 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
            omega)
      · exact orthTDFour_quasi_two_le hx hK hn1 hmem ht2 (by omega)
    exact orthTDFour_block_contra hQ hT hR hĀI hx hxδ hFq hFle hJeq hmem hq

private theorem orthTDFour_t_bound
    (hRig : GGLabelRigidInput)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {r : ℕ} (hdim : Module.finrank K V = 2 * r) (hn : Odd n)
    (hlab : GGHasLabel ⟨.D, 4, n⟩ (J' ⧸ Subgroup.center J')) :
    ∃ t : ℕ, 1 ≤ t ∧ r = 4 + t ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even t) ∧ (3 ≤ n → t ≤ 1) ∧ t ≤ 3 := by
  obtain ⟨a, ha, ha3, ha1⟩ := orthTDFour_conj_lift hQ hT hR hĀI
  obtain ⟨x, hxa, hx, hcase⟩ := orthTDFour_lift_x hQ hT hR ha ha3
  have hxδ : MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) = δ' := by
    rw [hxa, ha]
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := by
    intro h
    apply ha1
    rw [← hxa, show x = 1 from Subtype.ext h, map_one]
  rcases hcase with ⟨h, hh, hne1, hq, hJeq⟩ | ⟨F, hFq, hFle, hFn, hJeq⟩
  · exact (orthTDFour_specialBlock_impossible hRig hK hn hlab hx hh hne1 hq hJeq).elim
  · obtain ⟨hdim8, hplus8, ht3, hbound⟩ :=
      orthTDFour_fixed_data hRig hK hn hQ hT hR hĀI hlab hx hx1 hxδ hFq hFle hFn hJeq
    have hpq : 3 ∣ Nat.card K + 1 :=
      CFSG.StandardType.D4Inner.three_dvd_card_add_one (K := K) hK hn
    have hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hx hpq hx1
    haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem⟩
    have hothers : othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) =
        primaryComponent (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_eq hx hpq hmem
    have hRdim : finrank K (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) =
        2 * primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) := by
      rw [hothers, CFSG.HardMathSupport.Dickson.Bal207.OrthFix.finrank_phi hmem]
    obtain ⟨hcompl, horth⟩ := hx.fixed_others
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdim8, hRdim, hdim] at hsum
    have hrt : r = 4 + primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) := by
      omega
    have hpos := hx.primaryMultiplicity_pos hmem
    have hRinv : ∀ u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1),
        (x : V ≃ₗ[K] V) u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) :=
      fun u hu => CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_invariant hu
    have hRfix : ∀ u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1),
        (x : V ≃ₗ[K] V) u = u → u = 0 := fun u hu hxu =>
      (Submodule.disjoint_def.1 hcompl.disjoint) u (mem_fixedSpace.2 hxu) hu
    have hRreg : RegOn Q (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) := by
      intro u hu hperp
      refine hx.regular u fun v => ?_
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
      rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
        horth w hw u hu, add_zero]
    have hRtype := isPlusType_iff_even_of_fixedFree hx Nat.prime_three (by norm_num) hpq
      (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1))
      (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) hRinv hRreg hRfix hRdim
    have eV : Q.IsometryEquiv
        ((Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype).prod
          (Q.comp (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)).subtype)) :=
      (isometryTop Q).trans
        ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
          (isometryEquivSup Q (fixedSpace (x : V ≃ₗ[K] V))
            (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) hcompl.disjoint horth))
    have hprod := isPlusType_prod_iff
      (Q₁ := Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)
      (Q₂ := Q.comp (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)).subtype)
      hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg)
      (d₁ := 4) (d₂ := primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1))
      (by norm_num) (by omega) (by omega) hRdim
    have htype : IsPlusType Q ↔
        Even (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1)) := by
      rw [isPlusType_congr eV, hprod, hRtype]
      simp [hplus8]
    exact ⟨primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1),
      by omega, hrt, htype, hbound, ht3⟩

end OrthTDFourAux

theorem orthT_D4
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {r : ℕ} (hdim : Module.finrank K V = 2 * r) (hn : Odd n)
    (hlab : GGHasLabel ⟨.D, 4, n⟩ (J' ⧸ Subgroup.center J')) :
    5 ≤ r ∧ (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even (r - 4)) ∧ (3 ≤ n → r ≤ 5) ∧ r ≤ 7 := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨t, ht1, hr, htype, hbound, ht3⟩ :=
    orthTDFour_t_bound hRig hK hQ hT hR hĀI hdim hn hlab
  refine ⟨by omega, ?_, ?_, by omega⟩
  · have hrt : r - 4 = t := by omega
    rw [hrt]
    exact htype
  · intro h3
    have := hbound h3
    omega

end CFSG.StandardType.TablePThreeKG

end
