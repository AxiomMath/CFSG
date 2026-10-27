module

public import CFSG.Assembly.GL83LieDefs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitA
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma kgLangCAux_polar_comp {ι 𝕂 : Type} [Fintype ι] [Field 𝕂]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂) (u v : ι → 𝕂) :
    QuadraticMap.polar (Q.comp (Matrix.mulVecLin x)) u v
      = QuadraticMap.polar Q (x.mulVec u) (x.mulVec v) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_add]

private lemma kgLangCAux_defect_add {ι 𝕂 : Type} [Fintype ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂)
    (hxB : ∀ u v, QuadraticMap.polar Q (x.mulVec u) (x.mulVec v) = QuadraticMap.polar Q u v) :
    ∀ u v, Q (x.mulVec (u + v)) + Q (u + v)
      = (Q (x.mulVec u) + Q u) + (Q (x.mulVec v) + Q v) := by
  intro u v
  let D : QuadraticMap 𝕂 (ι → 𝕂) 𝕂 := Q.comp (Matrix.mulVecLin x) + Q
  have hpolar : QuadraticMap.polar D u v = 0 := by
    change QuadraticMap.polar (⇑(Q.comp (Matrix.mulVecLin x)) + ⇑Q) u v = 0
    rw [QuadraticMap.polar_add, kgLangCAux_polar_comp, hxB u v, CharTwo.add_self_eq_zero]
  have h := QuadraticMap.map_add (D : (ι → 𝕂) → 𝕂) u v
  rw [hpolar, add_zero] at h
  simpa only [D, QuadraticMap.add_apply, QuadraticMap.comp_apply, Matrix.mulVecLin_apply] using h

private lemma kgLangCAux_defect_smul {ι 𝕂 : Type} [Fintype ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂) :
    ∀ (a : 𝕂) (v : ι → 𝕂), Q (x.mulVec (a • v)) + Q (a • v)
      = a * a * (Q (x.mulVec v) + Q v) := by
  intro a v
  let D : QuadraticMap 𝕂 (ι → 𝕂) 𝕂 := Q.comp (Matrix.mulVecLin x) + Q
  have h := D.map_smul a v
  simpa only [D, QuadraticMap.add_apply, QuadraticMap.comp_apply, Matrix.mulVecLin_apply,
    smul_eq_mul] using h

private lemma kgLangCAux_defect_span {ι 𝕂 : Type} [Fintype ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂)
    (hadd : ∀ u v, Q (x.mulVec (u + v)) + Q (u + v)
      = (Q (x.mulVec u) + Q u) + (Q (x.mulVec v) + Q v))
    (hsmul : ∀ (a : 𝕂) (v : ι → 𝕂), Q (x.mulVec (a • v)) + Q (a • v)
      = a * a * (Q (x.mulVec v) + Q v))
    {S : Set (ι → 𝕂)} (hS : ∀ v ∈ S, Q (x.mulVec v) + Q v = 0) :
    ∀ v ∈ Submodule.span 𝕂 S, Q (x.mulVec v) + Q v = 0 := by
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · exact hS
  · simp [Matrix.mulVec_zero]
  · intro u v _ _ pu pv
    rw [hadd u v, pu, pv, add_zero]
  · intro a v _ pv
    rw [hsmul a v, pv, mul_zero]

private lemma kgLangCAux_commute {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {x : Matrix ι ι 𝕂}
    (hx : x ∈ Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)))
    {g : GL ι 𝕂} (hg : g ∈ P) : x * (g : Matrix ι ι 𝕂) = (g : Matrix ι ι 𝕂) * x := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨g', hg', rfl⟩
    have h := congrArg (fun u : GL ι 𝕂 => (u : Matrix ι ι 𝕂)) (hab g' hg' g hg)
    simpa only [Units.val_mul] using h
  · simp
  · intro y z _ _ py pz
    rw [add_mul, mul_add, py, pz]
  · intro a y _ py
    rw [Matrix.smul_mul, Matrix.mul_smul, py]

private lemma kgLangCAux_defect_inv {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (P : Subgroup (GL ι 𝕂))
    (hPQ : ∀ g ∈ P, ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v) {x : Matrix ι ι 𝕂}
    (hxcomm : ∀ g ∈ P, x * (g : Matrix ι ι 𝕂) = (g : Matrix ι ι 𝕂) * x) :
    ∀ g ∈ P, ∀ v, Q (x.mulVec ((g : Matrix ι ι 𝕂).mulVec v)) + Q ((g : Matrix ι ι 𝕂).mulVec v)
      = Q (x.mulVec v) + Q v := by
  intro g hg v
  have h1 : x.mulVec ((g : Matrix ι ι 𝕂).mulVec v) = (g : Matrix ι ι 𝕂).mulVec (x.mulVec v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxcomm g hg]
  rw [h1, hPQ g hg (x.mulVec v), hPQ g hg v]

private lemma kgLangCAux_defect_comm {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂) (P : Subgroup (GL ι 𝕂))
    (hadd : ∀ u v, Q (x.mulVec (u + v)) + Q (u + v)
      = (Q (x.mulVec u) + Q u) + (Q (x.mulVec v) + Q v))
    (hsmul : ∀ (a : 𝕂) (v : ι → 𝕂), Q (x.mulVec (a • v)) + Q (a • v)
      = a * a * (Q (x.mulVec v) + Q v))
    (hinv : ∀ g ∈ P, ∀ v, Q (x.mulVec ((g : Matrix ι ι 𝕂).mulVec v))
      + Q ((g : Matrix ι ι 𝕂).mulVec v) = Q (x.mulVec v) + Q v) :
    ∀ g ∈ P, ∀ w, Q (x.mulVec ((g : Matrix ι ι 𝕂).mulVec w - w))
      + Q ((g : Matrix ι ι 𝕂).mulVec w - w) = 0 := by
  intro g hg w
  have hw : Q (x.mulVec (-w)) + Q (-w) = Q (x.mulVec w) + Q w := by
    simpa using hsmul (-1) w
  have h1 := hadd ((g : Matrix ι ι 𝕂).mulVec w) (-w)
  rw [hinv g hg w, hw, CharTwo.add_self_eq_zero] at h1
  rw [sub_eq_add_neg]
  exact h1



private noncomputable def kgLangCAux_avg {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) [Fintype P] : (ι → 𝕂) →ₗ[𝕂] (ι → 𝕂) :=
  (Nat.card P : 𝕂)⁻¹ • ∑ g : P, Matrix.mulVecLin ((g : GL ι 𝕂) : Matrix ι ι 𝕂)

private lemma kgLangCAux_avg_apply {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) [Fintype P] (v : ι → 𝕂) :
    kgLangCAux_avg P v
      = (Nat.card P : 𝕂)⁻¹ • ∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v := by
  simp only [kgLangCAux_avg, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    Matrix.mulVecLin_apply]

private lemma kgLangCAux_avg_fixed {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) [Fintype P]
    {h : GL ι 𝕂} (hh : h ∈ P) (v : ι → 𝕂) :
    (h : Matrix ι ι 𝕂).mulVec (kgLangCAux_avg P v) = kgLangCAux_avg P v := by
  have hW : (h : Matrix ι ι 𝕂).mulVec (∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v)
      = ∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v := by
    change ((h : Matrix ι ι 𝕂).mulVecLin) (∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v)
      = ∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v
    rw [map_sum]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.val_mul]
    rw [← Function.Bijective.sum_comp (Group.mulLeft_bijective (⟨h, hh⟩ : P))
      (fun x : P => (((x : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v)]
    simp only [Subgroup.coe_mul, Units.val_mul]
  rw [kgLangCAux_avg_apply, Matrix.mulVec_smul, hW]



private lemma kgLangCAux_polar_preserved {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    [CharP 𝕂 2] (Q : QuadraticForm 𝕂 (ι → 𝕂)) {g : GL ι 𝕂}
    (hg : ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v) (a b : ι → 𝕂) :
    QuadraticMap.polar Q ((g : Matrix ι ι 𝕂).mulVec a) ((g : Matrix ι ι 𝕂).mulVec b)
      = QuadraticMap.polar Q a b := by
  have hcomp : Q.comp (Matrix.mulVecLin g) = Q := by
    ext v
    simpa only [QuadraticMap.comp_apply, Matrix.mulVecLin_apply] using hg v
  rw [← kgLangCAux_polar_comp Q (g : Matrix ι ι 𝕂) a b, hcomp]

private lemma kgLangCAux_polar_sum {ι 𝕂 α : Type} [Fintype ι] [Field 𝕂] [Fintype α]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (w : α → ι → 𝕂) (v : ι → 𝕂) :
    QuadraticMap.polar Q (∑ g, w g) v = ∑ g, QuadraticMap.polar Q (w g) v := by
  have h : (QuadraticMap.polarBilin Q) (∑ g, w g)
      = ∑ g, QuadraticMap.polarBilin Q (w g) :=
    map_sum (QuadraticMap.polarBilin Q) w Finset.univ
  calc QuadraticMap.polar Q (∑ g, w g) v
      = (QuadraticMap.polarBilin Q) (∑ g, w g) v := by
          rw [QuadraticMap.polarBilin_apply_apply]
    _ = (∑ g, QuadraticMap.polarBilin Q (w g)) v := by rw [h]
    _ = ∑ g, (QuadraticMap.polarBilin Q (w g)) v := by
          rw [LinearMap.coe_sum, Finset.sum_apply]
    _ = ∑ g, QuadraticMap.polar Q (w g) v := by
          simp only [QuadraticMap.polarBilin_apply_apply]

private lemma kgLangCAux_polar_sum_right {ι 𝕂 α : Type} [Fintype ι] [Field 𝕂] [Fintype α]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (w : α → ι → 𝕂) (v : ι → 𝕂) :
    QuadraticMap.polar Q v (∑ g, w g) = ∑ g, QuadraticMap.polar Q v (w g) := by
  rw [QuadraticMap.polar_comm, kgLangCAux_polar_sum]
  exact Finset.sum_congr rfl fun g _ => (QuadraticMap.polar_comm Q v (w g)).symm

private lemma kgLangCAux_polar_avg {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (P : Subgroup (GL ι 𝕂)) [Fintype P]
    (hPQ : ∀ g ∈ P, ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v)
    (u v : ι → 𝕂) :
    QuadraticMap.polar Q (kgLangCAux_avg P u) v
      = QuadraticMap.polar Q u (kgLangCAux_avg P v) := by
  rw [kgLangCAux_avg_apply, kgLangCAux_avg_apply, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right]
  congr 1
  rw [kgLangCAux_polar_sum Q (fun g : P => (((g : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec u) v,
    kgLangCAux_polar_sum_right Q (fun g : P => (((g : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v) u]
  rw [← Function.Bijective.sum_comp (inv_bijective (G := P))
    (fun g : P => QuadraticMap.polar Q ((((g : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec u) v)]
  refine Finset.sum_congr rfl ?_
  intro g _
  have hfix : ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec
      ((((g⁻¹ : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec u) = u := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  have hgp := kgLangCAux_polar_preserved Q (hPQ (g : GL ι 𝕂) g.2)
    ((((g⁻¹ : P) : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec u) v
  rw [hfix] at hgp
  exact hgp.symm



private lemma kgLangCAux_card_ne_zero {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2]
    {P : Type} [Finite P] (hodd : Odd (Nat.card P)) : (Nat.card P : 𝕂) ≠ 0 := by
  intro h
  exact (Nat.not_odd_iff_even.mpr
    (even_iff_two_dvd.mpr ((CharP.cast_eq_zero_iff 𝕂 2 (Nat.card P)).mp h))) hodd

private lemma kgLangCAux_avg_of_fixed {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) [Fintype P] (hcard : (Nat.card P : 𝕂) ≠ 0)
    {a : ι → 𝕂} (ha : ∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec a = a) :
    kgLangCAux_avg P a = a := by
  rw [kgLangCAux_avg_apply]
  have hsum : (∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec a) = (Nat.card P : 𝕂) • a := by
    rw [show (∑ g : P, ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec a) = ∑ _ : P, a from
      Finset.sum_congr rfl (fun g _ => ha g g.2)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul (R := 𝕂)]
  rw [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]

private lemma kgLangCAux_avg_sub {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) [Fintype P] (hcard : (Nat.card P : 𝕂) ≠ 0) (v : ι → 𝕂) :
    v - kgLangCAux_avg P v
      = (Nat.card P : 𝕂)⁻¹ • ∑ g : P, (v - ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v) := by
  rw [kgLangCAux_avg_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (R := 𝕂), smul_sub, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

private lemma kgLangCAux_defect_avg {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂) (P : Subgroup (GL ι 𝕂)) [Fintype P]
    (hadd : ∀ u v, Q (x.mulVec (u + v)) + Q (u + v)
      = (Q (x.mulVec u) + Q u) + (Q (x.mulVec v) + Q v))
    (hsmul : ∀ (a : 𝕂) (v : ι → 𝕂), Q (x.mulVec (a • v)) + Q (a • v)
      = a * a * (Q (x.mulVec v) + Q v))
    (hinv : ∀ g ∈ P, ∀ v, Q (x.mulVec ((g : Matrix ι ι 𝕂).mulVec v))
      + Q ((g : Matrix ι ι 𝕂).mulVec v) = Q (x.mulVec v) + Q v)
    (hcard : (Nat.card P : 𝕂) ≠ 0) (v : ι → 𝕂) :
    Q (x.mulVec (v - kgLangCAux_avg P v)) + Q (v - kgLangCAux_avg P v) = 0 := by
  let S : Set (ι → 𝕂) := Set.range (fun p : P × (ι → 𝕂) =>
    ((p.1 : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec p.2 - p.2)
  have hS : ∀ y ∈ S, Q (x.mulVec y) + Q y = 0 := by
    rintro y ⟨⟨g, w⟩, rfl⟩
    exact kgLangCAux_defect_comm Q x P hadd hsmul hinv g g.2 w
  have hmem : v - kgLangCAux_avg P v ∈ Submodule.span 𝕂 S := by
    rw [kgLangCAux_avg_sub P hcard v]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.sum_mem _ ?_
    intro g _
    have hgS : ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v - v ∈ S := ⟨(g, v), rfl⟩
    have hneg : v - ((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v
        = -(((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v - v) := by abel
    rw [hneg]
    exact Submodule.neg_mem _ (Submodule.subset_span hgS)
  exact kgLangCAux_defect_span Q x hadd hsmul hS _ hmem

private lemma kgLangCAux_augmentation {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) {x : Matrix ι ι 𝕂}
    (hx : x ∈ Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _))) :
    ∃ ε : 𝕂, ∀ v, (∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec v = v) → x.mulVec v = ε • v := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨g, hg, rfl⟩
    exact ⟨1, fun v hv => by rw [hv g hg, one_smul]⟩
  · exact ⟨0, fun v _ => by rw [Matrix.zero_mulVec, zero_smul]⟩
  · intro y z _ _ ⟨ε₁, h₁⟩ ⟨ε₂, h₂⟩
    exact ⟨ε₁ + ε₂, fun v hv => by rw [Matrix.add_mulVec, h₁ v hv, h₂ v hv, add_smul]⟩
  · intro a y _ ⟨ε, hε⟩
    exact ⟨a * ε, fun v hv => by rw [Matrix.smul_mulVec, hε v hv, smul_smul]⟩

private lemma kgLangCAux_defect_avg_fixed {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    [CharP 𝕂 2] (Q : QuadraticForm 𝕂 (ι → 𝕂))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (P : Subgroup (GL ι 𝕂)) [Fintype P]
    (hPQ : ∀ g ∈ P, ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v)
    {x : Matrix ι ι 𝕂}
    (hxB : ∀ u v, QuadraticMap.polar Q (x.mulVec u) (x.mulVec v) = QuadraticMap.polar Q u v)
    (hε : ∃ ε : 𝕂, ∀ v, (∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec v = v) → x.mulVec v = ε • v)
    (hcard : (Nat.card P : 𝕂) ≠ 0) (v : ι → 𝕂) :
    Q (x.mulVec (kgLangCAux_avg P v)) + Q (kgLangCAux_avg P v) = 0 := by
  set c : ι → 𝕂 := kgLangCAux_avg P v with hc
  have hc_fixed : ∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec c = c :=
    fun g hg => kgLangCAux_avg_fixed P hg v
  have hc_e : kgLangCAux_avg P c = c := kgLangCAux_avg_of_fixed P hcard hc_fixed
  by_cases hp : ∀ a b, (∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec a = a) →
      (∀ g ∈ P, (g : Matrix ι ι 𝕂).mulVec b = b) → QuadraticMap.polar Q a b = 0
  · have hc0 : c = 0 := by
      refine hQ.1 c ?_
      intro w
      rw [QuadraticMap.polarBilin_apply_apply]
      have h1 := kgLangCAux_polar_avg Q P hPQ c w
      rw [hc_e] at h1
      rw [h1]
      exact hp c (kgLangCAux_avg P w) hc_fixed (fun g hg => kgLangCAux_avg_fixed P hg w)
    rw [hc0, Matrix.mulVec_zero, QuadraticMap.map_zero, add_zero]
  · push Not at hp
    obtain ⟨a, b, ha, hb, hpab⟩ := hp
    obtain ⟨ε, hε'⟩ := hε
    have hxa : x.mulVec a = ε • a := hε' a ha
    have hxb : x.mulVec b = ε • b := hε' b hb
    have hε2 : ε * ε = 1 := by
      have h := hxB a b
      rw [hxa, hxb, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_smul,
        smul_eq_mul] at h
      exact mul_right_cancel₀ hpab (by simpa using h)
    have hε1 : ε = 1 := by
      rcases mul_self_eq_one_iff.mp hε2 with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    have hxc : x.mulVec c = c := by
      rw [hε' c hc_fixed, hε1, one_smul]
    rw [hxc, CharTwo.add_self_eq_zero]

theorem kgLangC_quadratic_preserved {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [CharP 𝕂 2]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (P : Subgroup (GL ι 𝕂)) [Finite P] (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hodd : Odd (Nat.card P)) (hPQ : ∀ g ∈ P, ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v)
    {x : Matrix ι ι 𝕂}
    (hx : x ∈ Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)))
    (hxB : ∀ u v, QuadraticMap.polar Q (x.mulVec u) (x.mulVec v) = QuadraticMap.polar Q u v) :
    ∀ v, Q (x.mulVec v) = Q v := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  have hcard : (Nat.card P : 𝕂) ≠ 0 := kgLangCAux_card_ne_zero hodd
  have hadd := kgLangCAux_defect_add Q x hxB
  have hsmul := kgLangCAux_defect_smul Q x
  have hcomm : ∀ g ∈ P, x * (g : Matrix ι ι 𝕂) = (g : Matrix ι ι 𝕂) * x :=
    fun g hg => kgLangCAux_commute P hab hx hg
  have hinv : ∀ g ∈ P, ∀ v, Q (x.mulVec ((g : Matrix ι ι 𝕂).mulVec v))
      + Q ((g : Matrix ι ι 𝕂).mulVec v) = Q (x.mulVec v) + Q v :=
    kgLangCAux_defect_inv Q P hPQ hcomm
  have hε := kgLangCAux_augmentation P hx
  intro v
  have hsplit : Q (x.mulVec v) + Q v
      = (Q (x.mulVec (kgLangCAux_avg P v)) + Q (kgLangCAux_avg P v))
        + (Q (x.mulVec (v - kgLangCAux_avg P v)) + Q (v - kgLangCAux_avg P v)) := by
    have h := hadd (kgLangCAux_avg P v) (v - kgLangCAux_avg P v)
    have hsum : kgLangCAux_avg P v + (v - kgLangCAux_avg P v) = v := by abel
    rwa [hsum] at h
  have hzero : Q (x.mulVec v) + Q v = 0 := by
    rw [hsplit, kgLangCAux_defect_avg_fixed Q hQ P hPQ hxB hε hcard v,
      kgLangCAux_defect_avg Q x P hadd hsmul hinv hcard v, add_zero]
  exact CharTwo.add_eq_zero.mp hzero

private theorem kgLangCAux_pow_isometry {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    {Q : QuadraticForm 𝕂 (ι → 𝕂)} {g : GL ι 𝕂}
    (hg : ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v) (n : ℕ) :
    ∀ v, Q (((g ^ n : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v) = Q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (ih ((g : Matrix ι ι 𝕂).mulVec v)).trans (hg v)

theorem kgLangC_mem_omega_of_odd {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂] [Finite 𝕂]
    [CharP 𝕂 2] (Q : QuadraticForm 𝕂 (ι → 𝕂)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule 𝕂 (ι → 𝕂), Module.finrank 𝕂 T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : GL ι 𝕂} (hg : ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v)
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    g ∈ LargeEvenOmega (ι := ι) (K := 𝕂) ⇑Q := by
  set h : GL ι 𝕂 := g ^ ((m + 1) / 2) with hh
  have hh_iso : ∀ v, Q ((h : Matrix ι ι 𝕂).mulVec v) = Q v := by
    rw [hh]; exact kgLangCAux_pow_isometry hg ((m + 1) / 2)
  have hm1 : 2 * ((m + 1) / 2) = m + 1 :=
    Nat.two_mul_div_two_of_even (by simpa [Nat.add_comm] using hm.one_add)
  have hh_sq : h ^ 2 = g := by
    have h2 : ((m + 1) / 2) * 2 = m + 1 := by rw [Nat.mul_comm, hm1]
    rw [hh, ← pow_mul, h2, pow_succ, hgm, one_mul]
  have hev : Even (CFSG.ComponentClassification.RankTwoClassical.commRank g) := by
    have h2 := CFSG.ComponentClassification.RankTwoClassical.even_commRank_sq Q hQ (M := h) hh_iso
    rwa [hh_sq] at h2
  exact CFSG.ComponentClassification.RankTwoClassical.mem_statedOmega_of Q hQ hT hg hev

end CFSG.StandardType
