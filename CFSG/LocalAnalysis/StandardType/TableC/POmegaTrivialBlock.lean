module

public import CFSG.LocalAnalysis.StandardType.TableC.PSpTrivialBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition

@[expose] noncomputable def trivBlockOrth {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (p : ℕ) (s : spinGroup Q) : Subgroup (spinGroup Q) :=
  glBlockCentralizer (Spin.spinMatrix Q)
    ({(Spin.spinMatrix Q s : GL ι F)} : Set (GL ι F))
    (fixIdem p (Spin.spinMatrix Q s : GL ι F))

theorem oddOrderIsometry_spinAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1) :
    OddOrderIsometry Q p (Spin.spinAction Q s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (Spin.map_spinAction Q s)
  · rw [← map_pow, hs, map_one]
  · intro hzero
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
    exact hp2 ((hp.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd)
  · intro v hv
    refine hQ.1 v fun w => ?_
    simpa only [QuadraticMap.polarBilin_apply_apply] using hv w

private lemma o2c_geom_sum_mul_sub_one {R : Type} [Ring R] {p : ℕ} (x : R) (hx : x ^ p = 1) :
    (∑ i ∈ Finset.range p, x ^ i) * (x - 1) = 0 := by
  have h := geom_sum_mul_neg x p
  rw [hx, sub_self] at h
  calc (∑ i ∈ Finset.range p, x ^ i) * (x - 1)
      = (∑ i ∈ Finset.range p, x ^ i) * (-(1 - x)) := by
        congr 1
        rw [neg_sub]
    _ = -((∑ i ∈ Finset.range p, x ^ i) * (1 - x)) := by rw [mul_neg]
    _ = 0 := by rw [h, neg_zero]

private lemma o2c_toLin'_pow {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (M : Matrix ι ι F) (n : ℕ) :
    Matrix.toLin' (M ^ n) = (Matrix.toLin' M) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Matrix.toLin'_mul, ih]; rfl

private lemma o2c_rank_eq_finrank_range_toLin' {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (M : Matrix ι ι F) :
    M.rank = finrank F ↥(LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F ι) (Pi.basisFun F ι),
    Matrix.toLin_eq_toLin']

private lemma o2c_toLin_fixIdem_sum {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (p : ℕ) (b : GL ι F) :
    Matrix.toLin' (fixIdem p b) =
      ((p : F)⁻¹) • ∑ i ∈ Finset.range p,
        (Matrix.toLin' (b : Matrix ι ι F)) ^ i := by
  unfold fixIdem
  rw [map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => o2c_toLin'_pow (b : Matrix ι ι F) i

private lemma o2c_geom_sum_mul_left {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) :
    (b : Matrix ι ι F) * (∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i) =
      ∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i := by
  have h := mul_geom_sum (b : Matrix ι ι F) p
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one] at h
  rw [sub_mul, one_mul, sub_self] at h
  exact sub_eq_zero.mp h

private lemma o2c_fixIdem_mul_left {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) :
    (b : Matrix ι ι F) * fixIdem p b = fixIdem p b := by
  unfold fixIdem
  rw [Matrix.mul_smul, o2c_geom_sum_mul_left b hpow]

private lemma o2c_toLin_fixIdem_mul_left {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) :
    Matrix.toLin' (b : Matrix ι ι F) * Matrix.toLin' (fixIdem p b) =
      Matrix.toLin' (fixIdem p b) := by
  calc Matrix.toLin' (b : Matrix ι ι F) * Matrix.toLin' (fixIdem p b)
      = Matrix.toLin' ((b : Matrix ι ι F) * fixIdem p b) :=
        (Matrix.toLin'_mul (b : Matrix ι ι F) (fixIdem p b)).symm
    _ = Matrix.toLin' (fixIdem p b) := by rw [o2c_fixIdem_mul_left b hpow]

private lemma o2c_fixIdem_apply_eq_self_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) (hc : (p : F) ≠ 0) (v : ι → F) :
    Matrix.toLin' (fixIdem p b) v = v ↔ Matrix.toLin' (b : Matrix ι ι F) v = v := by
  constructor
  · intro hv
    calc Matrix.toLin' (b : Matrix ι ι F) v
        = Matrix.toLin' (b : Matrix ι ι F) (Matrix.toLin' (fixIdem p b) v) := by rw [hv]
      _ = (Matrix.toLin' (b : Matrix ι ι F) * Matrix.toLin' (fixIdem p b)) v := rfl
      _ = Matrix.toLin' (fixIdem p b) v := by rw [o2c_toLin_fixIdem_mul_left b hpow]
      _ = v := hv
  · intro hv
    rw [o2c_toLin_fixIdem_sum]
    have hpowv : ∀ i : ℕ, ((Matrix.toLin' (b : Matrix ι ι F)) ^ i) v = v := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
    have hsum : (∑ i ∈ Finset.range p, (Matrix.toLin' (b : Matrix ι ι F)) ^ i) v =
        (p : F) • v := by
      rw [LinearMap.sum_apply]
      rw [Finset.sum_congr rfl fun i _ => hpowv i]
      rw [Finset.sum_const, Finset.card_range]
      exact (Nat.cast_smul_eq_nsmul F p v).symm
    rw [LinearMap.smul_apply, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]

private lemma o2c_toLin_spinMatrix {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (u : spinGroup Q) :
    Matrix.toLin' (Spin.spinMatrix Q u : Matrix ι ι F) =
      (Spin.spinAction Q u : (ι → F) →ₗ[F] (ι → F)) := by
  rw [Spin.coe_spinMatrix, Matrix.toLin'_toMatrix']

private lemma o2c_p_ne_zero {F : Type} [Field F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro hzero
  have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
  exact hp2 ((hp.dvd_iff_eq (by norm_num)).mp h2dvd)

private lemma o2c_spinMatrix_pow {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) {p : ℕ} (s : spinGroup Q) (hs : s ^ p = 1) :
    (Spin.spinMatrix Q s : GL ι F) ^ p = 1 := by
  rw [← map_pow, hs, map_one]

private lemma o2c_eps_mul_sub_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) {p : ℕ} (s : spinGroup Q) (hs : s ^ p = 1) :
    Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) *
        ((Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) - 1) = 0 := by
  rw [← o2c_toLin_spinMatrix Q s]
  rw [o2c_toLin_fixIdem_sum]
  have hb : (Spin.spinMatrix Q s : GL ι F) ^ p = 1 := o2c_spinMatrix_pow Q s hs
  have hxL : (Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F)) ^ p = 1 := by
    rw [← o2c_toLin'_pow, ← Units.val_pow_eq_pow_val, hb, Units.val_one,
      Matrix.toLin'_one]
    rfl
  rw [smul_mul_assoc, o2c_geom_sum_mul_sub_one _ hxL, smul_zero]

private lemma o2c_range_fixIdem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1) :
    LinearMap.range (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) =
      fixedSpace (Spin.spinAction Q s) := by
  have hb := o2c_spinMatrix_pow Q s hs
  have hc := o2c_p_ne_zero (F := F) hp hp2
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [mem_fixedSpace]
    show ((Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)))
        (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) w) =
      Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) w
    rw [← o2c_toLin_spinMatrix Q s]
    calc Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F)
          (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) w)
        = (Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F) *
            Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) w := rfl
      _ = Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) w := by
            rw [o2c_toLin_fixIdem_mul_left (Spin.spinMatrix Q s) hb]
  · intro w hw
    rw [mem_fixedSpace] at hw
    refine ⟨w, (o2c_fixIdem_apply_eq_self_iff (Spin.spinMatrix Q s) hb hc w).mpr ?_⟩
    simpa only [o2c_toLin_spinMatrix Q s, LinearEquiv.coe_coe] using hw

private lemma o2c_othersSpace_eq_range {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1) :
    othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) =
      LinearMap.range ((Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) - 1) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rintro v ⟨w, rfl⟩
    refine hx.perp_fixed_le_others fun u hu => ?_
    have hu' : (Spin.spinAction Q s) u = u := mem_fixedSpace.mp hu
    have hxu : (Spin.spinAction Q s).symm u = u := by
      have h := congrArg (Spin.spinAction Q s).symm hu'
      simpa using h.symm
    have hpolar := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem w
      ((Spin.spinAction Q s).symm u)
    simp only [LinearEquiv.apply_symm_apply] at hpolar
    change QuadraticMap.polar (⇑Q) ((Spin.spinAction Q s) w - w) u = 0
    rw [QuadraticMap.polar_sub_left, hpolar, hxu, sub_self]
  · have hrn := LinearMap.finrank_range_add_finrank_ker
      ((Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) - 1)
    have hcd := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
    have hker : LinearMap.ker ((Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) - 1) =
        fixedSpace (Spin.spinAction Q s) := rfl
    rw [hker] at hrn
    omega

private lemma o2c_ker_fixIdem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1) :
    LinearMap.ker (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) =
      othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hle : othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) ≤
      LinearMap.ker (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) := by
    rw [o2c_othersSpace_eq_range Q hQ hp hp2 s hs]
    rintro v ⟨w, rfl⟩
    have h := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f w)
      (o2c_eps_mul_sub_one Q s hs)
    simpa only [Module.End.mul_apply, LinearMap.mem_ker, LinearMap.zero_apply] using h
  have hfin : finrank F ↥(othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1)) =
      finrank F ↥(LinearMap.ker (Matrix.toLin'
        (fixIdem p (Spin.spinMatrix Q s : GL ι F)))) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)))
    rw [o2c_range_fixIdem Q hp hp2 s hs] at hrn
    have hcd := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

private lemma o2c_range_one_sub_fixIdem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1) :
    LinearMap.range (1 - Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) =
      othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hker : LinearMap.ker ((1 : (ι → F) →ₗ[F] (ι → F)) -
      Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))) =
      fixedSpace (Spin.spinAction Q s) := by
    have hb := o2c_spinMatrix_pow Q s hs
    have hc := o2c_p_ne_zero (F := F) hp hp2
    ext v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, eq_comm]
    rw [o2c_fixIdem_apply_eq_self_iff (Spin.spinMatrix Q s) hb hc v,
      o2c_toLin_spinMatrix Q s, mem_fixedSpace]
    simp only [LinearEquiv.coe_coe]
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [← o2c_ker_fixIdem Q hQ hp hp2 s hs]
    intro r hr
    refine ⟨r, ?_⟩
    have he : Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)) r = 0 :=
      (LinearMap.mem_ker).mp hr
    rw [LinearMap.sub_apply, Module.End.one_apply, he, sub_zero]
  · have hrn := LinearMap.finrank_range_add_finrank_ker
      ((1 : (ι → F) →ₗ[F] (ι → F)) -
        Matrix.toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F)))
    have hcd := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
    rw [hker] at hrn
    omega

private lemma o2c_mul_one_sub_eq_one_sub_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (M : GL ι F) (e : Matrix ι ι F) :
    (M : Matrix ι ι F) * (1 - e) = 1 - e ↔
      ∀ r ∈ LinearMap.range (1 - Matrix.toLin' e),
        Matrix.toLin' (M : Matrix ι ι F) r = r := by
  constructor
  · intro hM r hr
    obtain ⟨w, rfl⟩ := hr
    have h1e : (1 - Matrix.toLin' e) = Matrix.toLin' (1 - e) := by
      rw [map_sub, Matrix.toLin'_one]
      rfl
    rw [h1e]
    have h2 := congrArg (fun A : Matrix ι ι F => Matrix.toLin' A w) hM
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply] using h2
  · intro hfix
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, map_sub, Matrix.toLin'_one]
    apply LinearMap.ext
    intro w
    rw [LinearMap.comp_apply]
    exact hfix _ (LinearMap.mem_range.mpr ⟨w, rfl⟩)

private lemma o2c_glFixing_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1)
    (M : GL ι F) :
    M ∈ glFixing (1 - fixIdem p (Spin.spinMatrix Q s : GL ι F)) ↔
      ∀ r ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1),
        Matrix.toLin' (M : Matrix ι ι F) r = r := by
  have hgl : (M ∈ glFixing (1 - fixIdem p (Spin.spinMatrix Q s : GL ι F))) ↔
      ((M : Matrix ι ι F) * (1 - fixIdem p (Spin.spinMatrix Q s : GL ι F)) =
        1 - fixIdem p (Spin.spinMatrix Q s : GL ι F)) := Iff.rfl
  rw [hgl, o2c_mul_one_sub_eq_one_sub_iff,
    o2c_range_one_sub_fixIdem Q hQ hp hp2 s hs]

private lemma o2c_mem_centralizer_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (s : spinGroup Q) (M : GL ι F) :
    M ∈ Subgroup.centralizer
        ({(Spin.spinMatrix Q s : GL ι F)} : Set (GL ι F)) ↔
      Matrix.toLin' (M : Matrix ι ι F) *
          (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) =
        (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) *
          Matrix.toLin' (M : Matrix ι ι F) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : ((M * (Spin.spinMatrix Q s) : GL ι F) : Matrix ι ι F) =
        (((Spin.spinMatrix Q s) * M : GL ι F) : Matrix ι ι F) :=
      congrArg (fun x : GL ι F => (x : Matrix ι ι F)) h
    rw [Units.val_mul, Units.val_mul] at h'
    calc Matrix.toLin' (M : Matrix ι ι F) *
            (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F))
        = Matrix.toLin' (M : Matrix ι ι F) *
            Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F) := by
          rw [o2c_toLin_spinMatrix Q s]
      _ = Matrix.toLin' ((M : Matrix ι ι F) *
            (Spin.spinMatrix Q s : Matrix ι ι F)) := (Matrix.toLin'_mul _ _).symm
      _ = Matrix.toLin' ((Spin.spinMatrix Q s : Matrix ι ι F) *
            (M : Matrix ι ι F)) := by rw [h']
      _ = Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F) *
            Matrix.toLin' (M : Matrix ι ι F) := Matrix.toLin'_mul _ _
      _ = (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) *
            Matrix.toLin' (M : Matrix ι ι F) := by rw [o2c_toLin_spinMatrix Q s]
  · intro h
    rw [← o2c_toLin_spinMatrix Q s] at h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    apply Matrix.toLin'.injective
    calc Matrix.toLin' ((M : Matrix ι ι F) * (Spin.spinMatrix Q s : Matrix ι ι F))
        = Matrix.toLin' (M : Matrix ι ι F) *
            Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F) := Matrix.toLin'_mul _ _
      _ = Matrix.toLin' (Spin.spinMatrix Q s : Matrix ι ι F) *
            Matrix.toLin' (M : Matrix ι ι F) := h
      _ = Matrix.toLin' ((Spin.spinMatrix Q s : Matrix ι ι F) *
            (M : Matrix ι ι F)) := (Matrix.toLin'_mul _ _).symm

theorem map_trivBlockOrth_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F))) :
    (trivBlockOrth Q p s).map (Spin.spinAction Q) =
      supportedFixedDerived Q (Spin.spinAction Q s) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hR : (polarBilin (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    change Spin.spinMatrix Q u ∈
      (Subgroup.centralizer ({(Spin.spinMatrix Q s : GL ι F)} : Set (GL ι F)) ⊓
        glFixing (1 - fixIdem p (Spin.spinMatrix Q s : GL ι F))) at hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have hcomm := (o2c_mem_centralizer_iff Q s (Spin.spinMatrix Q u)).mp hu1
    have hfix := (o2c_glFixing_iff Q hQ hp hp2 s hs (Spin.spinMatrix Q u)).mp hu2
    have hcommψ : (Spin.spinAction Q u : (ι → F) →ₗ[F] (ι → F)) *
        (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) =
        (Spin.spinAction Q s : (ι → F) →ₗ[F] (ι → F)) *
        (Spin.spinAction Q u : (ι → F) →ₗ[F] (ι → F)) := by
      rwa [o2c_toLin_spinMatrix Q u] at hcomm
    have hfixψ : ∀ r ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1),
        (Spin.spinAction Q u) r = r := by
      intro r hr
      have h := hfix r hr
      rwa [o2c_toLin_spinMatrix Q u] at h
    have hiso : Spin.spinAction Q u ∈ isometryCentralizer Q (Spin.spinAction Q s) := by
      rw [mem_isometryCentralizer]
      refine ⟨fun v => Spin.map_spinAction Q u v, fun v => ?_⟩
      have h := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f v) hcommψ
      simpa only [Module.End.mul_apply, LinearEquiv.coe_coe] using h
    have hblock : Spin.spinAction Q u ∈ supportedBlock Q (Spin.spinAction Q s)
        (Polynomial.X - 1) :=
      mem_supportedBlock.mpr ⟨hiso, hfixψ⟩
    have hψ_der : Spin.spinAction Q u ∈ orthDerived Q := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
    obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
    have hmem_iso_block : Spin.spinAction Q u ∈
        isometryCentralizer Q (Spin.spinAction Q s) :=
      supportedBlock_le_isometryCentralizer (Polynomial.X - 1) hblock
    have hdick_der : (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ)
        ⟨Spin.spinAction Q u, orthDerived_le_orthogonalGroup hψ_der⟩ = 1 :=
      dicksonHom_eq_one_of_mem_orthDerived hQ hψ_der
    have hdick_lhs : (dicksonCentralizer Q (Spin.spinAction Q s) hQ)
        ⟨Spin.spinAction Q u, hmem_iso_block⟩ = 1 := by
      show (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ)
        ⟨Spin.spinAction Q u, (Subgroup.mem_inf.mp hmem_iso_block).1⟩ = 1
      rw [show (⟨Spin.spinAction Q u, (Subgroup.mem_inf.mp hmem_iso_block).1⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
          ⟨Spin.spinAction Q u, orthDerived_le_orthogonalGroup hψ_der⟩ from
        Subtype.ext rfl]
      exact hdick_der
    have hdick_fixed : (dicksonFixed hx) ⟨Spin.spinAction Q u, hmem_iso_block⟩ = 1 := by
      rw [← DFunLike.congr_fun (OddOrderIsometry.dicksonCentralizer_eq_dicksonFixed hx
        (hp.odd_of_ne_two hp2) hQ hRep) ⟨Spin.spinAction Q u, hmem_iso_block⟩]
      exact hdick_lhs
    have hT : ∃ U : Submodule F ↥(fixedSpace (Spin.spinAction Q s)), finrank F U = 3 ∧
        ∀ u ∈ U, (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) u = 0 := by
      have h8' : 8 ≤ finrank F ↥(fixedSpace (Spin.spinAction Q s)) := by
        rw [← o2c_range_fixIdem Q hp hp2 s hs,
          ← o2c_rank_eq_finrank_range_toLin'
            (fixIdem p (Spin.spinMatrix Q s : GL ι F))]
        exact h8
      obtain ⟨m, hm⟩ := hx.even_finrank_fixed
      have hm2 : finrank F ↥(fixedSpace (Spin.spinAction Q s)) = 2 * m := by omega
      exact CFSG.RankThree.PartOne.exists_threeSingular_of_dim
        (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) hR (m := m) (by omega) hm2
    have hD := CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular
      (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) hR hT
    have hres : restrictFixed Q (Spin.spinAction Q s) ⟨Spin.spinAction Q u, hblock⟩ ∈
        orthDerived (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) := by
      refine hD ⟨restrictFixed Q (Spin.spinAction Q s) ⟨Spin.spinAction Q u, hblock⟩,
        restrictFixed_mem_orthogonalGroup _⟩ ?_
      exact hdick_fixed
    exact mem_supportedFixedDerived.mpr ⟨hblock, hres⟩
  · rintro g hg
    have hg_block : g ∈ supportedBlock Q (Spin.spinAction Q s) (Polynomial.X - 1) :=
      supportedFixedDerived_le_supportedBlock hg
    have hg_der : g ∈ orthDerived Q := OddOrderIsometry.supportedFixedDerived_le_orthDerived hx hg
    have hg_range : g ∈ (Spin.spinAction Q).range := by rwa [hrange]
    obtain ⟨u, hu_eq⟩ := MonoidHom.mem_range.mp hg_range
    refine Subgroup.mem_map.mpr ⟨u, ?_, hu_eq⟩
    show Spin.spinMatrix Q u ∈
      (Subgroup.centralizer ({(Spin.spinMatrix Q s : GL ι F)} : Set (GL ι F)) ⊓
        glFixing (1 - fixIdem p (Spin.spinMatrix Q s : GL ι F)))
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine (o2c_mem_centralizer_iff Q s (Spin.spinMatrix Q u)).mpr ?_
      rw [o2c_toLin_spinMatrix Q u, hu_eq]
      apply LinearMap.ext
      intro v
      have hv := (mem_isometryCentralizer.mp
        (supportedBlock_le_isometryCentralizer _ hg_block)).2 v
      simpa only [Module.End.mul_apply, LinearEquiv.coe_coe] using hv
    · refine (o2c_glFixing_iff Q hQ hp hp2 s hs (Spin.spinMatrix Q u)).mpr ?_
      intro r hr
      rw [o2c_toLin_spinMatrix Q u, hu_eq]
      exact (mem_supportedBlock.mp hg_block).2 r hr

private lemma o2b_geom_sum_fixes_right {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) :
    (∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i) * (b : Matrix ι ι F) =
      ∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i :=
  CFSG.TwoRankLowerBound.Helpers.finiteOrder_geometric_sum_fixes_right p
    (b : Matrix ι ι F) (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])

private lemma o2b_geom_sum_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F] {p : ℕ}
    (b : GL ι F) :
    Commute (b : Matrix ι ι F) (∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i) :=
  Commute.sum_right (Finset.range p) (fun i => (b : Matrix ι ι F) ^ i) (b : Matrix ι ι F)
    (fun i _ => (Commute.refl (b : Matrix ι ι F)).pow_right i)

private lemma o2b_geom_sum_mul_left {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F] {p : ℕ}
    (b : GL ι F) (hpow : b ^ p = 1) :
    (b : Matrix ι ι F) * (∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i) =
      ∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i := by
  rw [(o2b_geom_sum_comm (p := p) b).eq]
  exact o2b_geom_sum_fixes_right b hpow

private lemma o2b_fixIdem_mul_left {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {p : ℕ}
    (b : GL ι F) (hpow : b ^ p = 1) :
    (b : Matrix ι ι F) * fixIdem p b = fixIdem p b := by
  unfold fixIdem
  rw [Matrix.mul_smul, o2b_geom_sum_mul_left b hpow]

private lemma o2b_fixIdem_mulVec_of_fixed {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (b : GL ι F) (hpow : b ^ p = 1) (hc : (p : F) ≠ 0) {v : ι → F}
    (hv : (b : Matrix ι ι F).mulVec v = v) :
    (fixIdem p b).mulVec v = v := by
  have hbpow : ∀ i : ℕ, ((b : Matrix ι ι F) ^ i).mulVec v = v := by
    intro i
    induction i with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ i ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hsum : ((∑ i ∈ Finset.range p, (b : Matrix ι ι F) ^ i)).mulVec v =
      ∑ _ ∈ Finset.range p, v := by
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => hbpow i
  unfold fixIdem
  rw [Matrix.smul_mulVec, hsum, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul F p v, inv_smul_smul₀ hc]

theorem finrank_fixedSpace_spinAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1) :
    Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F)) =
      finrank F (fixedSpace (Spin.spinAction Q s)) := by
  have hpow : (Spin.spinMatrix Q s) ^ p = 1 := by
    have h := congrArg (Spin.spinMatrix Q) hs
    simpa only [map_pow, map_one] using h
  have hc : (p : F) ≠ 0 := by
    intro hzero
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
    exact hp2 ((hp.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd)
  have hrange : LinearMap.range
        (Matrix.mulVecLin (fixIdem p (Spin.spinMatrix Q s : GL ι F))) =
      fixedSpace (Spin.spinAction Q s) := by
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      rw [mem_fixedSpace, ← Spin.spinMatrix_mulVec Q s, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, o2b_fixIdem_mul_left (Spin.spinMatrix Q s) hpow]
    · intro v hv
      rw [mem_fixedSpace] at hv
      exact ⟨v, o2b_fixIdem_mulVec_of_fixed (Spin.spinMatrix Q s) hpow hc (by
        rw [Spin.spinMatrix_mulVec]; exact hv)⟩
  rw [show Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F)) =
      Module.finrank F (LinearMap.range
        (Matrix.mulVecLin (fixIdem p (Spin.spinMatrix Q s : GL ι F)))) from rfl,
    hrange]

private lemma o2d_spinAction_injective {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hj : Function.Injective (Spin.spinMatrix Q)) :
    Function.Injective (Spin.spinAction Q) := by
  intro a b hab
  apply hj
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [o2c_toLin_spinMatrix Q a, o2c_toLin_spinMatrix Q b, hab]

private lemma o2d_threeSingular {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F))) :
    ∃ U : Submodule F ↥(fixedSpace (Spin.spinAction Q s)), finrank F U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) u = 0 := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hR : (polarBilin (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have h8' : 8 ≤ finrank F ↥(fixedSpace (Spin.spinAction Q s)) := by
    rw [← o2c_range_fixIdem Q hp hp2 s hs,
      ← o2c_rank_eq_finrank_range_toLin' (fixIdem p (Spin.spinMatrix Q s : GL ι F))]
    exact h8
  obtain ⟨m, hm⟩ := hx.even_finrank_fixed
  have hm2 : finrank F ↥(fixedSpace (Spin.spinAction Q s)) = 2 * m := by omega
  exact CFSG.RankThree.PartOne.exists_threeSingular_of_dim
    (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype) hR (m := m) (by omega) hm2

private lemma o2d_normal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F))) :
    Subgroup.Normal ((trivBlockOrth Q p s).subgroupOf
      (Subgroup.centralizer ({s} : Set (spinGroup Q)))) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hinjA := o2d_spinAction_injective Q hj
  have hmap := map_trivBlockOrth_eq Q hQ hj hrange hp hp2 s hs h8
  have hle : trivBlockOrth Q p s ≤ Subgroup.centralizer ({s} : Set (spinGroup Q)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hj
    have hu' : Spin.spinMatrix Q u ∈ Subgroup.centralizer
        ({(Spin.spinMatrix Q s : GL ι F)} : Set (GL ι F)) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hu)).1
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hu'
  refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
  intro h k hh hk
  have hψh : Spin.spinAction Q h ∈ supportedFixedDerived Q (Spin.spinAction Q s) := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  have hkcomm : Commute k s := Subgroup.mem_centralizer_singleton_iff.mp hk
  have hm_mem : Spin.spinAction Q k ∈ isometryCentralizer Q (Spin.spinAction Q s) := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => Spin.map_spinAction Q k v, fun v => ?_⟩
    have hcomm : Spin.spinAction Q k * Spin.spinAction Q s =
        Spin.spinAction Q s * Spin.spinAction Q k := by
      rw [← map_mul, ← map_mul, hkcomm.eq]
    show Spin.spinAction Q k (Spin.spinAction Q s v) =
      Spin.spinAction Q s (Spin.spinAction Q k v)
    calc Spin.spinAction Q k (Spin.spinAction Q s v)
        = (Spin.spinAction Q k * Spin.spinAction Q s) v := rfl
      _ = (Spin.spinAction Q s * Spin.spinAction Q k) v := by rw [hcomm]
      _ = Spin.spinAction Q s (Spin.spinAction Q k v) := rfl
  have hconj : Spin.spinAction Q k * Spin.spinAction Q h * (Spin.spinAction Q k)⁻¹ ∈
      supportedFixedDerived Q (Spin.spinAction Q s) :=
    hx.conj_mem_supportedFixedDerived hm_mem hψh
  have hconj' : Spin.spinAction Q (k * h * k⁻¹) ∈
      supportedFixedDerived Q (Spin.spinAction Q s) := by
    rw [map_mul, map_mul, map_inv]
    exact hconj
  rw [← hmap] at hconj'
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hconj'
  rw [← hinjA hbeq]
  exact hb

private lemma o2d_inner {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F)))
    (g : spinGroup Q) (hg : Commute g s) (hgp : g ^ p = 1) :
    ∃ r ∈ trivBlockOrth Q p s, ∀ l ∈ trivBlockOrth Q p s,
      g⁻¹ * l * g = r⁻¹ * l * r := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hinjA := o2d_spinAction_injective Q hj
  have hmap := map_trivBlockOrth_eq Q hQ hj hrange hp hp2 s hs h8
  have hT := o2d_threeSingular Q hQ hp hp2 s hs h8
  let m : (ι → F) ≃ₗ[F] (ι → F) := Spin.spinAction Q g
  have hmp : m ^ p = 1 := by
    show Spin.spinAction Q g ^ p = 1
    rw [← map_pow, hgp, map_one]
  have hm_mem : m ∈ isometryCentralizer Q (Spin.spinAction Q s) := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => Spin.map_spinAction Q g v, fun v => ?_⟩
    have hcomm : Spin.spinAction Q g * Spin.spinAction Q s =
        Spin.spinAction Q s * Spin.spinAction Q g := by
      rw [← map_mul, ← map_mul, hg.eq]
    show Spin.spinAction Q g (Spin.spinAction Q s v) =
      Spin.spinAction Q s (Spin.spinAction Q g v)
    calc Spin.spinAction Q g (Spin.spinAction Q s v)
        = (Spin.spinAction Q g * Spin.spinAction Q s) v := rfl
      _ = (Spin.spinAction Q s * Spin.spinAction Q g) v := by rw [hcomm]
      _ = Spin.spinAction Q s (Spin.spinAction Q g v) := rfl
  obtain ⟨f, hf_eq⟩ := restrictFixed_surjective hx
    (isometryRestrictFixed Q (Spin.spinAction Q s) ⟨m, hm_mem⟩)
    (isometryRestrictFixed_mem_orthogonalGroup (Q := Q) (x := Spin.spinAction Q s)
      ⟨m, hm_mem⟩)
  have hsub : (⟨m, hm_mem⟩ : ↥(isometryCentralizer Q (Spin.spinAction Q s))) ^ p = 1 :=
    Subtype.ext (by simpa using hmp)
  have hfp : f ^ p = 1 := by
    apply restrictFixed_injective hx
    rw [map_pow, hf_eq, map_one, ← map_pow, hsub, map_one]
  have hfp' : (f : (ι → F) ≃ₗ[F] (ι → F)) ^ p = 1 := by
    have h := congrArg (fun y : ↥(supportedBlock Q (Spin.spinAction Q s) (Polynomial.X - 1)) =>
      (y : (ι → F) ≃ₗ[F] (ι → F))) hfp
    simpa using h
  have hf_der : (f : (ι → F) ≃ₗ[F] (ι → F)) ∈
      supportedFixedDerived Q (Spin.spinAction Q s) :=
    hx.mem_supportedFixedDerived_of_odd_pow hT f.2 (hp.odd_of_ne_two hp2) hfp'
  have hf_map : (f : (ι → F) ≃ₗ[F] (ι → F)) ∈
      (trivBlockOrth Q p s).map (Spin.spinAction Q) := by
    rw [hmap]
    exact hf_der
  obtain ⟨r, hr, hr_eq⟩ := Subgroup.mem_map.mp hf_map
  refine ⟨r, hr, fun l hl => ?_⟩
  apply hinjA
  simp only [map_mul, map_inv, hr_eq]
  have hf_block : (f : (ι → F) ≃ₗ[F] (ι → F)) ∈
      supportedBlock Q (Spin.spinAction Q s) (Polynomial.X - 1) := f.2
  have hf_c : (f : (ι → F) ≃ₗ[F] (ι → F)) ∈ Subgroup.centralizer
      ({Spin.spinAction Q s} : Set ((ι → F) ≃ₗ[F] (ι → F))) :=
    (Subgroup.mem_inf.mp (mem_supportedBlock.mp hf_block).1).2
  have hf_fix : ∀ z ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1),
      (f : (ι → F) ≃ₗ[F] (ι → F)) z = z := (mem_supportedBlock.mp hf_block).2
  have hl_der : Spin.spinAction Q l ∈ supportedFixedDerived Q (Spin.spinAction Q s) := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
  have hl_block : Spin.spinAction Q l ∈
      supportedBlock Q (Spin.spinAction Q s) (Polynomial.X - 1) :=
    supportedFixedDerived_le_supportedBlock hl_der
  have hl_c : Spin.spinAction Q l ∈ Subgroup.centralizer
      ({Spin.spinAction Q s} : Set ((ι → F) ≃ₗ[F] (ι → F))) :=
    (Subgroup.mem_inf.mp (mem_supportedBlock.mp hl_block).1).2
  have hl_fix : ∀ z ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1),
      Spin.spinAction Q l z = z := (mem_supportedBlock.mp hl_block).2
  have hm_c : m ∈ Subgroup.centralizer
      ({Spin.spinAction Q s} : Set ((ι → F) ≃ₗ[F] (ι → F))) := (Subgroup.mem_inf.mp hm_mem).2
  have hWagree : ∀ w ∈ fixedSpace (Spin.spinAction Q s),
      (f : (ι → F) ≃ₗ[F] (ι → F)) w = m w := by
    intro w hw
    have h1 := congrArg (fun φ : fixedSpace (Spin.spinAction Q s) ≃ₗ[F]
        fixedSpace (Spin.spinAction Q s) => (φ ⟨w, hw⟩ : (ι → F))) hf_eq
    rw [coe_restrictFixed, coe_isometryRestrictFixed] at h1
    exact h1
  have hinv : ∀ z ∈ fixedSpace (Spin.spinAction Q s),
      m⁻¹ z = (f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z := by
    intro z hz
    have hfw : (f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z ∈ fixedSpace (Spin.spinAction Q s) :=
      mem_fixedSpace_of_apply (inv_mem hf_c) hz
    have h1 : m ((f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z) = z := by
      rw [← hWagree ((f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z) hfw]
      simpa only [LinearEquiv.coe_inv] using
        LinearEquiv.apply_symm_apply (f : (ι → F) ≃ₗ[F] (ι → F)) z
    calc m⁻¹ z = m⁻¹ (m ((f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z)) := by rw [h1]
      _ = (f : (ι → F) ≃ₗ[F] (ι → F)) ⁻¹ z := LinearEquiv.symm_apply_apply m _
  have hpres_m : ∀ z ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1),
      m z ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) :=
    fun z hz => mem_othersSpace_of_apply hm_c hz
  have hmain : (m⁻¹ * Spin.spinAction Q l * m : (ι → F) ≃ₗ[F] (ι → F)) =
      (f : (ι → F) ≃ₗ[F] (ι → F))⁻¹ * Spin.spinAction Q l *
        (f : (ι → F) ≃ₗ[F] (ι → F)) := by
    ext v
    obtain ⟨u, hu, rr, hrr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
    have hmu : m u ∈ fixedSpace (Spin.spinAction Q s) := mem_fixedSpace_of_apply hm_c hu
    have hfu : (f : (ι → F) ≃ₗ[F] (ι → F)) u ∈ fixedSpace (Spin.spinAction Q s) :=
      mem_fixedSpace_of_apply hf_c hu
    have hfu_eq : (f : (ι → F) ≃ₗ[F] (ι → F)) u = m u := hWagree u hu
    have hAu : (m⁻¹ * Spin.spinAction Q l * m : (ι → F) ≃ₗ[F] (ι → F)) u =
        ((f : (ι → F) ≃ₗ[F] (ι → F))⁻¹ * Spin.spinAction Q l *
          (f : (ι → F) ≃ₗ[F] (ι → F))) u := by
      show m⁻¹ (Spin.spinAction Q l (m u)) =
        (f : (ι → F) ≃ₗ[F] (ι → F))⁻¹
          (Spin.spinAction Q l ((f : (ι → F) ≃ₗ[F] (ι → F)) u))
      rw [← hfu_eq]
      exact hinv _ (mem_fixedSpace_of_apply hl_c hfu)
    have hmr : m rr ∈ othersSpace (Spin.spinAction Q s).toLinearMap (Polynomial.X - 1) :=
      hpres_m rr hrr
    have hAr : (m⁻¹ * Spin.spinAction Q l * m : (ι → F) ≃ₗ[F] (ι → F)) rr =
        ((f : (ι → F) ≃ₗ[F] (ι → F))⁻¹ * Spin.spinAction Q l *
          (f : (ι → F) ≃ₗ[F] (ι → F))) rr := by
      show m⁻¹ (Spin.spinAction Q l (m rr)) =
        (f : (ι → F) ≃ₗ[F] (ι → F))⁻¹
          (Spin.spinAction Q l ((f : (ι → F) ≃ₗ[F] (ι → F)) rr))
      rw [hl_fix (m rr) hmr, hf_fix rr hrr, hl_fix rr hrr]
      simp only [LinearEquiv.coe_inv]
      rw [LinearEquiv.symm_apply_apply]
      have hfr : (f : (ι → F) ≃ₗ[F] (ι → F)).symm rr = rr := by
        rw [LinearEquiv.symm_apply_eq]
        exact (hf_fix rr hrr).symm
      rw [hfr]
    rw [map_add, map_add, hAu, hAr]
  exact hmain

private noncomputable def o2d_isoEquiv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F))) :
    ↥(trivBlockOrth Q p s) ≃*
      ↥(orthDerived (Q.comp (fixedSpace (Spin.spinAction Q s)).subtype)) := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  have hmap := map_trivBlockOrth_eq Q hQ hj hrange hp hp2 s hs h8
  exact (Subgroup.equivMapOfInjective (trivBlockOrth Q p s) (Spin.spinAction Q)
    (o2d_spinAction_injective Q hj)).trans
    ((MulEquiv.subgroupCongr hmap).trans (supportedFixedDerivedEquiv hx))

theorem trivialBlock_orth {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : spinGroup Q) (hs : s ^ p = 1)
    (h8 : 8 ≤ Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F))) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : FiniteDimensional F W)
      (R : QuadraticForm F W), (polarBilin R).Nondegenerate ∧
      finrank F W = Matrix.rank (fixIdem p (Spin.spinMatrix Q s : GL ι F)) ∧
      Nonempty (↥(trivBlockOrth Q p s) ≃* ↥(orthDerived R)) ∧
      Subgroup.Normal ((trivBlockOrth Q p s).subgroupOf
        (Subgroup.centralizer ({s} : Set (spinGroup Q)))) ∧
      ∀ g : spinGroup Q, Commute g s → g ^ p = 1 →
        ∃ r ∈ trivBlockOrth Q p s, ∀ l ∈ trivBlockOrth Q p s, g⁻¹ * l * g = r⁻¹ * l * r := by
  have hx := oddOrderIsometry_spinAction Q hQ hp hp2 s hs
  refine ⟨↥(fixedSpace (Spin.spinAction Q s)), inferInstance, inferInstance, inferInstance,
    Q.comp (fixedSpace (Spin.spinAction Q s)).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · exact hx.polarBilin_fixed_nondegenerate
  · exact (finrank_fixedSpace_spinAction Q hQ hp hp2 s hs).symm
  · exact ⟨o2d_isoEquiv Q hQ hj hrange hp hp2 s hs h8⟩
  · exact o2d_normal Q hQ hj hrange hp hp2 s hs h8
  · exact o2d_inner Q hQ hj hrange hp hp2 s hs h8

end CFSG.StandardType.TableC

end
