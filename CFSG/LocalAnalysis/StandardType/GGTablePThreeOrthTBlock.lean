module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthBlock
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthSelfDual
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthFixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.RankThree.PartOne.KC.OrthogonalTraceModels
import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentTwo
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCBasic
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
import CFSG.RankThree.PartOne.FOC.CompCommutator

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

private theorem orthTBlock_label_sl {X : Type} [Group X] {b k : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ^ k) (hb : 2 ≤ b) (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL b E)) :
    GGHasLabel ⟨.A, b - 1, k⟩ X := by
  have eR : LargeEvenProj (LargeEvenSLGroup (Fin b) E) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL b E) :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      (largeEvenSLGroup_eq_statedSL (K := E) b)).some
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  rw [show b - 1 + 1 = b by omega]
  exact ⟨e.trans eR.symm⟩

section OrthTBlockAux

open Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem orthTBlock_dvd_phi {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {k : K[X]} (hk : k ∈ primaryFactors x.toLinearMap)
    (hk1 : k ≠ X - 1) : k ∣ (X ^ 2 + X + 1 : K[X]) := by
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  have hdvd : k ∣ (X - 1 : K[X]) * (X ^ 2 + X + 1) := by
    rw [← hfac]
    exact hx.dvd_X_pow_sub_one hk
  rcases (irreducible_of_mem_primaryFactors hk).prime.dvd_or_dvd hdvd with h | h
  · exfalso
    exact hk1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) monic_X_sub_one
      ((irreducible_of_mem_primaryFactors hk).associated_of_dvd irreducible_X_sub_one h))
  · exact h

private theorem orthTBlock_primaryFactors_three_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    ∀ k ∈ primaryFactors x.toLinearMap, k = X - 1 ∨ k = h ∨ k = reciprocalPolynomial h := by
  classical
  have hmonic : h.Monic := monic_of_mem_primaryFactors hh
  have hirr_h : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hcoeff0 : h.coeff 0 ≠ 0 := hx.coeff_zero_ne hh
  have hh_dvd : h ∣ (X ^ 2 + X + 1 : K[X]) :=
    orthTBlock_dvd_phi hx hh hne1
  have hF_natDegree : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hF_monic : (X ^ 2 + X + 1 : K[X]).Monic := by
    rw [show (X ^ 2 + X + 1 : K[X]) = X ^ 2 + (X + 1) by ring]
    refine Polynomial.monic_X_pow_add (p := (X + 1 : K[X])) ?_
    compute_degree!
  have hF_ne_zero : (X ^ 2 + X + 1 : K[X]) ≠ 0 := hF_monic.ne_zero
  have hF_coeff0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by
    rw [coeff_add, coeff_add, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  have hpos : 0 < h.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hirr_h.not_isUnit (isUnit_of_natDegree_eq_zero_of_ne_zero hirr_h.ne_zero h0)
  intro k hk
  by_cases hk1 : k = X - 1
  · exact Or.inl hk1
  · refine Or.inr ?_
    have hkmonic : k.Monic := monic_of_mem_primaryFactors hk
    have hirr_k : Irreducible k := irreducible_of_mem_primaryFactors hk
    have hkpos : 0 < k.natDegree := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hirr_k.not_isUnit (isUnit_of_natDegree_eq_zero_of_ne_zero hirr_k.ne_zero h0)
    have hk_dvd : k ∣ (X ^ 2 + X + 1 : K[X]) :=
      orthTBlock_dvd_phi hx hk hk1
    by_cases hkh : k = h
    · exact Or.inl hkh
    · refine Or.inr ?_
      have hcop : IsCoprime k h :=
        isCoprime_of_irreducible_monic_ne hirr_k hirr_h hkmonic hmonic hkh
      have hkh_dvd : k * h ∣ (X ^ 2 + X + 1 : K[X]) := hcop.mul_dvd hk_dvd hh_dvd
      have hsum : k.natDegree + h.natDegree ≤ 2 := by
        have hle := Polynomial.natDegree_le_of_dvd hkh_dvd hF_ne_zero
        rwa [hF_natDegree, natDegree_mul hirr_k.ne_zero hmonic.ne_zero] at hle
      have hdeg_h1 : h.natDegree = 1 := by omega
      have hdeg_k1 : k.natDegree = 1 := by omega
      have hF_eq : (X ^ 2 + X + 1 : K[X]) = k * h :=
        eq_of_monic_of_dvd_of_natDegree_le (hkmonic.mul hmonic) hF_monic hkh_dvd (by
          have h2 : (k * h).natDegree = k.natDegree + h.natDegree :=
            natDegree_mul hirr_k.ne_zero hmonic.ne_zero
          omega)
      have hconst : k.coeff 0 * h.coeff 0 = 1 := by
        have h := congrArg (fun p : K[X] => p.coeff 0) hF_eq
        rw [mul_coeff_zero, hF_coeff0] at h
        exact h.symm
      have hk0 : k.coeff 0 = (reciprocalPolynomial h).coeff 0 := by
        rw [coeff_zero_reciprocalPolynomial hmonic]
        exact eq_inv_of_mul_eq_one_left hconst
      have hstar_deg1 : (reciprocalPolynomial h).natDegree = 1 := by
        rw [natDegree_reciprocalPolynomial hcoeff0, hdeg_h1]
      have hk_eq : k = X + C (k.coeff 0) := hkmonic.eq_X_add_C hdeg_k1
      have hstar_eq : reciprocalPolynomial h = X + C ((reciprocalPolynomial h).coeff 0) :=
        (monic_reciprocalPolynomial hcoeff0).eq_X_add_C hstar_deg1
      calc k = X + C (k.coeff 0) := hk_eq
        _ = X + C ((reciprocalPolynomial h).coeff 0) := by rw [hk0]
        _ = reciprocalPolynomial h := hstar_eq.symm

private theorem orthTBlock_self_mem_supportedBlock {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    x ∈ supportedBlock Q x h := by
  classical
  refine hx.mem_supportedBlock_of_block hh (Subgroup.mem_centralizer_singleton_iff.mpr rfl) ?_ ?_
  · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
    rcases orthTBlock_primaryFactors_three_eq hx hh hne1 k hk with hk1 | hk2 | hk2
    · subst hk1
      have hv0 : x.toLinearMap v - v = 0 := by
        have h := mem_primaryComponent.mp hv
        simpa using h
      exact sub_eq_zero.mp hv0
    · exact absurd hk2 hkh
    · exact absurd hk2 hkh'
  · intro u _
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u

private theorem orthTBlock_self_mem_specialBlock {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 3 ∣ primaryMultiplicity x.toLinearMap h) :
    x ∈ specialBlock Q x h := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hx_supp : x ∈ supportedBlock Q x h := orthTBlock_self_mem_supportedBlock hx hh hne1
  refine mem_specialBlock.mpr ⟨hx_supp, ?_⟩
  obtain ⟨hroot, hord⟩ := hx.orderOf_root Nat.prime_three hh hne1
  let c : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hroot
  have hblock : blockGL Q x h ⟨x, hx_supp⟩ = scalarGL x h c := by
    refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
    rw [coe_blockGL, coe_scalarGL]
    exact (coe_root_smul_primaryComponent x.toLinearMap h v).symm
  rw [blockDet_apply, hblock, det_scalarGL]
  have hc3 : c ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one c
  obtain ⟨q, hq⟩ := hm
  have hcu : c ^ primaryMultiplicity x.toLinearMap h = 1 := by
    rw [hq, pow_mul, hc3, one_pow]
  rw [← Units.val_pow_eq_pow_val, hcu, Units.val_one]

private theorem orthTBlock_two_le {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    2 ≤ primaryMultiplicity x.toLinearMap h := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_contra hlt
  have hpos := hx.primaryMultiplicity_pos hh
  have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
  exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)

private theorem orthTBlock_reciprocal_X2 {K : Type} [Field K] :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hX : reflect 2 (X : K[X]) = X := by
    rw [← pow_one (X : K[X]), reflect_monomial]
    rfl
  have h0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    rw [Polynomial.reverse, hd]
    simp [reflect_add, reflect_monomial, hX] <;> ring
  rw [reciprocalPolynomial, h0, hrev, inv_one, map_one, one_mul]

private theorem orthTBlock_quot {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    Nonempty (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h) ≃*
      ↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) := by
  classical
  have hspecΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  let f_sb : ↥(specialBlock Q x h) →* ↥(componentImage Q x h) :=
    (ρ.comp (Subgroup.inclusion hspecΩ)).codRestrict (componentImage Q x h) (fun g =>
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hspecΩ g,
        Subgroup.mem_subgroupOf.mpr g.2, rfl⟩)
  have hf_sb : Function.Surjective f_sb := by
    intro y
    have hy : (y : ProjOrthDerived Q) ∈
        ((specialBlock Q x h).subgroupOf (orthDerived Q)).map ρ := by
      simpa only [componentImage] using y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩, Subtype.ext ?_⟩
    show ρ (Subgroup.inclusion hspecΩ
      ⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩) = (y : ProjOrthDerived Q)
    rw [show Subgroup.inclusion hspecΩ
      ⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩ = z from Subtype.ext rfl, hzy]
  have hker_sb : f_sb.ker ≤ Subgroup.center ↥(specialBlock Q x h) := by
    intro g hg
    have h1 : Subgroup.inclusion hspecΩ g ∈ (scalars K V).subgroupOf (orthDerived Q) :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hspecΩ g)).mp
        (congrArg Subtype.val (MonoidHom.mem_ker.mp hg))
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp h1)
    have hc' : ∀ v : V, (g : V ≃ₗ[K] V) v = c • v := hc
    rw [Subgroup.mem_center_iff]
    intro k
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (k : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = (g : V ≃ₗ[K] V) ((k : V ≃ₗ[K] V) v)
    rw [hc' v, hc', map_smul]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hq.1.commutator_eq_top f_sb hf_sb hker_sb

private theorem orthTBlock_selfDual_phi {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hchar : ringChar K = 2) (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (f : ℕ) (hcard : Nat.card K = 2 ^ f) :
    h = X ^ 2 + X + 1 ∧ 3 ∣ 2 ^ f + 1 := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨d, _, hdeg, hroot, _, _, _, _, _, _⟩ :=
    hx.exists_selfDual_hermitian (p := 3) (by decide) hh hne1 hself
  have hdvd : h ∣ (X ^ 2 + X + 1 : K[X]) := orthTBlock_dvd_phi hx hh hne1
  have hFmonic : (X ^ 2 + X + 1 : K[X]).Monic := by
    rw [show (X ^ 2 + X + 1 : K[X]) = X ^ 2 + (X + 1) by ring]
    refine Polynomial.monic_X_pow_add (p := (X + 1 : K[X])) ?_
    compute_degree!
  have hne0 : (X ^ 2 + X + 1 : K[X]) ≠ 0 := hFmonic.ne_zero
  have hF_natDegree : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hle : h.natDegree ≤ 2 := by
    have hle' := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [hF_natDegree] at hle'
  have hpos : 0 < h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hd1 : d = 1 := by omega
  have hnat : h.natDegree = 2 := by omega
  have hmonic : h.Monic := monic_of_mem_primaryFactors hh
  have heq : h = X ^ 2 + X + 1 :=
    (eq_of_monic_of_dvd_of_natDegree_le hmonic hFmonic hdvd (by omega)).symm
  haveI : CharP (AdjoinRoot h) 2 := by
    have h2 : ringChar (AdjoinRoot h) = 2 :=
      (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hchar
    exact h2 ▸ ringChar.charP (AdjoinRoot h)
  refine ⟨heq, ?_⟩
  have hroot3 : (AdjoinRoot.root h) ^ 3 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hroot0 : AdjoinRoot.root h ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hroot3
    exact zero_ne_one hroot3
  have hroot_ne_one : AdjoinRoot.root h ≠ 1 := by
    intro h1
    have h0 : Polynomial.aeval (AdjoinRoot.root h) h = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    obtain ⟨q, hq⟩ := hdvd
    have h2 : Polynomial.aeval (AdjoinRoot.root h) (X ^ 2 + X + 1 : K[X]) = 0 := by
      rw [hq, map_mul, h0, zero_mul]
    have h0' : (AdjoinRoot.root h) ^ 2 + AdjoinRoot.root h + 1 = 0 := by
      simpa using h2
    rw [h1] at h0'
    simp only [one_pow] at h0'
    have h2 : (2 : AdjoinRoot h) = 0 := CharP.cast_eq_zero (AdjoinRoot h) 2
    have h1' : (1 : AdjoinRoot h) + 1 + 1 = 1 := by
      rw [show (1 : AdjoinRoot h) + 1 = 2 by norm_num, h2, zero_add]
    rw [h1'] at h0'
    exact one_ne_zero h0'
  have hord : orderOf (AdjoinRoot.root h) = 3 := by
    have hdvd3 : orderOf (AdjoinRoot.root h) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr hroot3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hroot_ne_one
    · exact h
  have hmul : (AdjoinRoot.root h) ^ (Nat.card K ^ d + 1) = 1 := by
    rw [pow_succ, hroot, inv_mul_cancel₀ hroot0]
  have h3dvd : 3 ∣ Nat.card K ^ d + 1 := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hmul
  rwa [hcard, hd1, pow_one] at h3dvd

private theorem orthTBlock_paired {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (hchar : ringChar K = 2)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (hne : h ≠ reciprocalPolynomial h) :
    3 ∣ 2 ^ f - 1 ∧
      GGHasLabel ⟨.A, primaryMultiplicity x.toLinearMap h - 1, f⟩
        (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hdvd : h ∣ (X ^ 2 + X + 1 : K[X]) := orthTBlock_dvd_phi hx hh hne1
  have hFmonic : (X ^ 2 + X + 1 : K[X]).Monic := by
    rw [show (X ^ 2 + X + 1 : K[X]) = X ^ 2 + (X + 1) by ring]
    refine Polynomial.monic_X_pow_add (p := (X + 1 : K[X])) ?_
    compute_degree!
  have hne0 : (X ^ 2 + X + 1 : K[X]) ≠ 0 := hFmonic.ne_zero
  have hF_natDegree : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hle : h.natDegree ≤ 2 := by
    have hle' := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [hF_natDegree] at hle'
  have hpos : 0 < h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hmonic : h.Monic := monic_of_mem_primaryFactors hh
  have hnat1 : h.natDegree = 1 := by
    by_contra h1
    have h2 : h.natDegree = 2 := by omega
    have heq : h = X ^ 2 + X + 1 :=
      (eq_of_monic_of_dvd_of_natDegree_le hmonic hFmonic hdvd (by omega)).symm
    exact hne (by rw [heq, orthTBlock_reciprocal_X2])
  have hroot3 : (AdjoinRoot.root h) ^ 3 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hroot0 : AdjoinRoot.root h ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hroot3
    exact zero_ne_one hroot3
  haveI : CharP (AdjoinRoot h) 2 := by
    have h2 : ringChar (AdjoinRoot h) = 2 :=
      (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hchar
    exact h2 ▸ ringChar.charP (AdjoinRoot h)
  have hroot_ne_one : AdjoinRoot.root h ≠ 1 := by
    intro h1
    have h0 : Polynomial.aeval (AdjoinRoot.root h) h = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    obtain ⟨q, hq⟩ := hdvd
    have h2 : Polynomial.aeval (AdjoinRoot.root h) (X ^ 2 + X + 1 : K[X]) = 0 := by
      rw [hq, map_mul, h0, zero_mul]
    have h0' : (AdjoinRoot.root h) ^ 2 + AdjoinRoot.root h + 1 = 0 := by
      simpa using h2
    rw [h1] at h0'
    simp only [one_pow] at h0'
    have h3 : (2 : AdjoinRoot h) = 0 := CharP.cast_eq_zero (AdjoinRoot h) 2
    have h1' : (1 : AdjoinRoot h) + 1 + 1 = 1 := by
      rw [show (1 : AdjoinRoot h) + 1 = 2 by norm_num, h3, zero_add]
    rw [h1'] at h0'
    exact one_ne_zero h0'
  let u : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hroot0
  have hord : orderOf u = 3 := by
    have hu3 : u ^ 3 = 1 := Units.ext (by
      change (AdjoinRoot.root h) ^ 3 = 1
      exact hroot3)
    have hdvd3 : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hu3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with hord1 | hord1
    · refine absurd (orderOf_eq_one_iff.mp hord1) ?_
      intro h1
      have h1' : (AdjoinRoot.root h) = 1 := by
        have h2 : (u : AdjoinRoot h) = 1 := by
          rw [h1]
          rfl
        rwa [show (u : AdjoinRoot h) = AdjoinRoot.root h from rfl] at h2
      exact hroot_ne_one h1'
    · exact hord1
  have h3 : 3 ∣ 2 ^ f - 1 := by
    have hdvd3 : 3 ∣ Nat.card (AdjoinRoot h)ˣ := by
      rw [← hord]
      exact orderOf_dvd_natCard u
    rw [Nat.card_units, CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hcard, hnat1,
      pow_one] at hdvd3
    exact hdvd3
  obtain ⟨eJS⟩ := orthTBlock_quot hq
  let bb : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let eSL : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    ((MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv bb).symm)
  obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl
    (primaryMultiplicity x.toLinearMap h) eSL
  refine ⟨h3, ?_⟩
  have hcardE : Nat.card (AdjoinRoot h) = 2 ^ f := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hcard, hnat1, pow_one]
  exact orthTBlock_label_sl hcardE (orthTBlock_two_le hx hh hne1 hq) (eJS.trans eSZ)

private theorem orthTBlock_selfDual {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hchar : ringChar K = 2) (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (hself : h = reciprocalPolynomial h) :
    h = X ^ 2 + X + 1 ∧ 3 ∣ 2 ^ f + 1 ∧
      ((primaryMultiplicity x.toLinearMap h = 2 ∧ 2 ≤ f ∧
          GGHasLabel ⟨.A, 1, f⟩
            (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h))) ∨
        (3 ≤ primaryMultiplicity x.toLinearMap h ∧
          ¬ (f = 1 ∧ primaryMultiplicity x.toLinearMap h = 3) ∧
          GGHasLabel ⟨.twA, primaryMultiplicity x.toLinearMap h - 1, f⟩
            (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)))) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hself_eq, h3dvd⟩ := orthTBlock_selfDual_phi hchar hx hh hne1 hself f hcard
  have hnat : h.natDegree = 2 := by rw [hself_eq]; compute_degree!
  obtain ⟨eJS⟩ := orthTBlock_quot hq
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian (p := 3) (by decide) hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (irreducible_of_mem_primaryFactors hh).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hdpos : 1 ≤ d := by
    have := (Fact.out : Irreducible h).natDegree_pos
    omega
  obtain ⟨ℓ, ff, hU, hq0, hbar⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_unitaryFieldData (K := K) (E := AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (ff * d)) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hcharE : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
  have hℓ : ringChar (AdjoinRoot h) = ℓ := ringChar.eq _ ℓ
  have hℓ2 : ℓ = 2 := hℓ.symm.trans (hcharE.trans hchar)
  have hff : ff = f := by
    have h1 : ℓ ^ ff = 2 ^ f := by rw [← hq0, hcard]
    have h2 : 2 ^ ff = 2 ^ f := by rwa [hℓ2] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  have hd1 : d = 1 := by omega
  have hfd : ff * d = f := by rw [hff, hd1, mul_one]
  have hcardE : Nat.card (AdjoinRoot h) = (2 ^ f) ^ 2 := by
    rw [hE, hℓ2, hfd]
  refine ⟨hself_eq, h3dvd, ?_⟩
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with hm3 | hm3
  ·
    have hm2_eq : primaryMultiplicity x.toLinearMap h = 2 := by
      have := orthTBlock_two_le hx hh hne1 hq
      omega
    have hm2 : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := hm2_eq
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU
      hBsymm hBl hm2
    letI : Fintype ↥hU.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card ↥hU.fixedField = ℓ ^ (ff * d) := by
      rw [Fintype.card_eq_nat_card, hU.card_fixedField]
    have h4 : 4 ≤ Fintype.card ↥hU.fixedField := by
      by_contra hlt
      refine (CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.not_isSolvable_of_isQuasisimple_aux hq) ?_
      haveI := isSolvable_specialLinear_two_of_card_le_three (K := ↥hU.fixedField)
        (by rw [Nat.card_eq_fintype_card]; omega)
      exact Group.isSolvable_of_isSolvable_injective (f := (e₁.trans φ).toMonoidHom)
        (e₁.trans φ).injective
    have hcardNat : Nat.card ↥hU.fixedField = 2 ^ f := by
      rw [Nat.card_eq_fintype_card, hcardF, hℓ2, hfd]
    have h2f : 2 ≤ f := by
      have h4' : 2 ^ 2 ≤ 2 ^ f := by
        rw [← Nat.card_eq_fintype_card, hcardNat] at h4
        simpa using h4
      exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp h4'
    refine Or.inl ⟨hm2_eq, h2f, ?_⟩
    refine orthTBlock_label_sl (b := 2) hcardNat (by norm_num) ?_
    exact eJS.trans ((CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2
      (e₁.trans φ)).some)
  ·
    have hmq : (primaryMultiplicity x.toLinearMap h, ℓ ^ (ff * d)) ≠ (3, 2) := by
      intro he
      have h3 : primaryMultiplicity x.toLinearMap h = 3 := (Prod.mk.inj he).1
      have h2 : ℓ ^ (ff * d) = 2 := (Prod.mk.inj he).2
      refine (CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.not_isSolvable_of_isQuasisimple_aux hq) ?_
      haveI : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := by
        refine isSolvable_of_card_primeFactors_le_two ?_
        have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
          (n := primaryMultiplicity x.toLinearMap h) rfl (by omega)).2.1
        rw [h3, h2] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
        have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          exact_mod_cast hcard.trans e
        rw [h216]
        decide +kernel
      exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
    obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
    obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
      e₀ he₀
    have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
        (primaryMultiplicity x.toLinearMap h) =
        CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (ff * d))
          (AdjoinRoot h) := by
      rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
      exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
    let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h)
        (ℓ ^ (ff * d)) (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (e₂.trans (MulEquiv.subgroupCongr hS)).symm
    have hbarQ : ∀ y, hU.barEquiv y = y ^ ℓ ^ (ff * d) := fun y => by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    have hbarQ2 : ∀ y, hU.barEquiv y = y ^ (2 ^ (ff * d)) := fun y => by
      rw [hbarQ y, hℓ2]
    have hcardE' : Nat.card (AdjoinRoot h) = (2 ^ (ff * d)) ^ 2 := by
      rw [hE, hℓ2]
    have hmq2 : (primaryMultiplicity x.toLinearMap h, 2 ^ (ff * d)) ≠ (3, 2) := by
      rwa [hℓ2] at hmq
    have hne31 : ¬ (f = 1 ∧ primaryMultiplicity x.toLinearMap h = 3) := by
      rintro ⟨hf1, hf3⟩
      apply hmq2
      rw [hf3, hfd, hf1, pow_one]
    obtain ⟨eSZ₁⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_su
      (Q := ℓ ^ (ff * d)) rfl (e₁.trans e₃.symm) hU.barEquiv hU.bar_bar hbarQ
    obtain ⟨eSZ₂⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds hU.barEquiv hU.bar_bar hbarQ2
      hcardE' hm3 hmq2
    have he : ↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU
          (primaryMultiplicity x.toLinearMap h - 1 + 1) (2 ^ (ff * d)) (AdjoinRoot h)) := by
      rw [show primaryMultiplicity x.toLinearMap h - 1 + 1 = primaryMultiplicity x.toLinearMap h
        by omega]
      exact eJS.trans (eSZ₁.trans eSZ₂)
    have hlab := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA
      (b := primaryMultiplicity x.toLinearMap h - 1) hcardE' he
    refine Or.inr ⟨hm3, hne31, ?_⟩
    simpa [hfd] using hlab

private theorem orthTBlock_concl {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (hchar : ringChar K = 2)
    (f : ℕ) (hcard : Nat.card K = 2 ^ f) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    2 ≤ primaryMultiplicity x.toLinearMap h ∧
    ((h ≠ reciprocalPolynomial h ∧ 3 ∣ 2 ^ f - 1 ∧
        GGHasLabel ⟨.A, primaryMultiplicity x.toLinearMap h - 1, f⟩
          (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h))) ∨
      (h = X ^ 2 + X + 1 ∧ 3 ∣ 2 ^ f + 1 ∧
        ((primaryMultiplicity x.toLinearMap h = 2 ∧ 2 ≤ f ∧
            GGHasLabel ⟨.A, 1, f⟩
              (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h))) ∨
          (3 ≤ primaryMultiplicity x.toLinearMap h ∧
            ¬ (f = 1 ∧ primaryMultiplicity x.toLinearMap h = 3) ∧
            GGHasLabel ⟨.twA, primaryMultiplicity x.toLinearMap h - 1, f⟩
              (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)))))) := by
  classical
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := orthTBlock_two_le hx hh hne1 hq
  refine ⟨hm, ?_⟩
  rcases eq_or_ne h (reciprocalPolynomial h) with hself | hne
  · obtain ⟨hself_eq, h3, hrest⟩ :=
      orthTBlock_selfDual hchar hx hh hne1 hq f hcard hself
    exact Or.inr ⟨hself_eq, h3, hrest⟩
  · obtain ⟨h3, hlab⟩ := orthTBlock_paired hchar hx hh hne1 hq f hcard hne
    exact Or.inl ⟨hne, h3, hlab⟩

end OrthTBlockAux

theorem orthT_blockLabel {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    {L : Subgroup (ProjOrthDerived Q)} (hL : L = componentImage Q (x : V ≃ₗ[K] V) h) :
    2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ∧
      (3 ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x ∈ L) ∧
      ((h ≠ reciprocalPolynomial h ∧ 3 ∣ 2 ^ n - 1 ∧
          GGHasLabel ⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩
            (L ⧸ Subgroup.center L)) ∨
        (h = X ^ 2 + X + 1 ∧ 3 ∣ 2 ^ n + 1 ∧
          ((primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2 ∧ 2 ≤ n ∧
              GGHasLabel ⟨.A, 1, n⟩ (L ⧸ Subgroup.center L)) ∨
            (3 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ∧
              ¬ (n = 1 ∧ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3) ∧
              GGHasLabel ⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩
                (L ⧸ Subgroup.center L))))) := by
  classical
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hm, hmain⟩ := orthTBlock_concl hchar n hK hx hh hne1 hq
  subst hL
  refine ⟨hm, ?_, hmain⟩
  intro hm3
  refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (orthTBlock_self_mem_specialBlock hx hh hne1 hm3)

end CFSG.StandardType.TablePThreeKG

end
