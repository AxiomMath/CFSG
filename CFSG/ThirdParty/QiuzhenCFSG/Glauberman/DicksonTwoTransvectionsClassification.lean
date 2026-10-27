module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTraceField
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvections
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Glauberman

namespace Dickson

variable {p : ℕ} [Fact p.Prime] {hpodd : p ≠ 2}
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
variable {H : Type*} [Group H]

/-! A two-generator specialization of Dickson's subgroup classification. -/

include hpodd

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
public theorem two_transvections_classification_aligned
    (rhoF : H →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hrhoF : Function.Injective rhoF)
    (K : Type) [Field K] [Algebra (ZMod p) K] [Module K V] [Finite K]
    (hlinear : ∀ h : H, ∀ k : K, ∀ v : V,
      (rhoF h : V →ₗ[ZMod p] V) (k • v) =
        k • (rhoF h : V →ₗ[ZMod p] V) v) :
      ∀ coord : LinearEquiv (RingHom.id K) V (K × K),
      ∀ r : K, ∀ x y : H,
      Module.finrank (ZMod p) K = (minpoly (ZMod p) r).natDegree →
      r ≠ 0 →
      Subgroup.closure ({x, y} : Set H) = ⊤ →
      (∀ a c : K,
        coord.toFun ((rhoF x : V →ₗ[ZMod p] V)
          (coord.symm.toFun (a, c))) = (a + r * c, c)) →
      (∀ a c : K,
        coord.toFun ((rhoF y : V →ₗ[ZMod p] V)
          (coord.symm.toFun (a, c))) = (a, c + a)) →
      ∃ (coordFin : V ≃ₗ[K] (Fin 2 → K))
          (rhoSL : H →* Matrix.SpecialLinearGroup (Fin 2) K),
        Function.Injective rhoSL ∧
        ((rhoSL x : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) = !![1, r; 0, 1] ∧
        ((rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] ∧
        (∀ h : H, ∀ v : V,
          coordFin ((rhoF h : V →ₗ[ZMod p] V) v) =
            Matrix.SpecialLinearGroup.toLin' (rhoSL h) (coordFin v)) ∧
        (Function.Surjective rhoSL ∨
          (Nat.card K = 9 ∧ r ^ 2 + 1 = 0 ∧
            Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))) := by
  intro coord r x y hdegree hrne hcl hxmodel hymodel
  let linEquivK (h : H) : V ≃ₗ[K] V :=
    { (rhoF h).toLinearEquiv with
      map_smul' := by
        intro k v
        simpa using hlinear h k v }
  let rhoKV : H →* LinearMap.GeneralLinearGroup K V :=
    { toFun := fun h => LinearMap.GeneralLinearGroup.ofLinearEquiv (linEquivK h)
      map_one' := by
        apply Units.ext
        apply LinearMap.ext
        intro v
        simp [linEquivK]
      map_mul' := by
        intro a b
        apply Units.ext
        apply LinearMap.ext
        intro v
        simp [linEquivK, map_mul] }
  let e : V ≃ₗ[K] (Fin 2 → K) :=
    coord.trans (LinearEquiv.finTwoArrow K K).symm
  let rho : H →* GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp rhoKV)
  have hrhoKV : Function.Injective rhoKV := by
    intro a b hab
    apply hrhoF
    apply Units.ext
    apply LinearMap.ext
    intro v
    simpa [rhoKV, linEquivK] using
      congrArg (fun g : LinearMap.GeneralLinearGroup K V => g.toLinearEquiv v) hab
  have hrho_apply (h : H) (z : Fin 2 → K) :
      (Matrix.GeneralLinearGroup.toLin (rho h)).toLinearEquiv z =
        e ((rhoF h : V →ₗ[ZMod p] V) (e.symm z)) := by
    simp [rho, rhoKV, e, linEquivK]
  have hx_apply (z : Fin 2 → K) :
      (Matrix.GeneralLinearGroup.toLin (rho x)).toLinearEquiv z =
        ![z 0 + r * z 1, z 1] := by
    rw [hrho_apply]
    have hcoord : coord (e.symm z) = (z 0, z 1) := by
      simp [e, LinearEquiv.finTwoArrow]
    rw [show e.symm z = coord.symm (z 0, z 1) by
      apply coord.injective
      simp [hcoord]]
    change (LinearEquiv.finTwoArrow K K).symm
      (coord ((rhoF x : V →ₗ[ZMod p] V) (coord.symm (z 0, z 1)))) = _
    simpa [LinearEquiv.finTwoArrow] using congrArg
      (LinearEquiv.finTwoArrow K K).symm (hxmodel (z 0) (z 1))
  have hy_apply (z : Fin 2 → K) :
      (Matrix.GeneralLinearGroup.toLin (rho y)).toLinearEquiv z =
        ![z 0, z 1 + z 0] := by
    rw [hrho_apply]
    have hcoord : coord (e.symm z) = (z 0, z 1) := by
      simp [e, LinearEquiv.finTwoArrow]
    rw [show e.symm z = coord.symm (z 0, z 1) by
      apply coord.injective
      simp [hcoord]]
    change (LinearEquiv.finTwoArrow K K).symm
      (coord ((rhoF y : V →ₗ[ZMod p] V) (coord.symm (z 0, z 1)))) = _
    simpa [LinearEquiv.finTwoArrow] using congrArg
      (LinearEquiv.finTwoArrow K K).symm (hymodel (z 0) (z 1))
  have hxmatrix : (rho x : Matrix (Fin 2) (Fin 2) K) = !![1, r; 0, 1] := by
    have hx0 := hx_apply ![1, 0]
    have hx1 := hx_apply ![0, 1]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 0) hx0
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 0) hx1
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 1) hx0
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 1) hx1
  have hymatrix : (rho y : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := by
    have hy0 := hy_apply ![1, 0]
    have hy1 := hy_apply ![0, 1]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 0) hy0
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 0) hy1
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 1) hy0
    · simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
        congrArg (fun v => v 1) hy1
  let detKer : Subgroup H := (Matrix.GeneralLinearGroup.det.comp rho).ker
  have hxdet : x ∈ detKer := by
    change Matrix.GeneralLinearGroup.det (rho x) = 1
    apply Units.ext
    change Matrix.det (rho x : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hxmatrix]
    simp [Matrix.det_fin_two]
  have hydet : y ∈ detKer := by
    change Matrix.GeneralLinearGroup.det (rho y) = 1
    apply Units.ext
    change Matrix.det (rho y : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hymatrix]
    simp [Matrix.det_fin_two]
  have hdet_le : Subgroup.closure ({x, y} : Set H) ≤ detKer := by
    rw [Subgroup.closure_le]
    intro z hz
    have hz' : z = x ∨ z = y := by simpa using hz
    rcases hz' with rfl | rfl
    · exact hxdet
    · exact hydet
  have hdet (h : H) : Matrix.GeneralLinearGroup.det (rho h) = 1 := by
    exact hdet_le (hcl ▸ (trivial : h ∈ (⊤ : Subgroup H)))
  let rhoSL : H →* Matrix.SpecialLinearGroup (Fin 2) K :=
    { toFun := fun h => ⟨(rho h : Matrix (Fin 2) (Fin 2) K), by
          simpa using congrArg Units.val (hdet h)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hrhoSL : Function.Injective rhoSL := by
    intro a b hab
    apply hrhoKV
    apply (LinearMap.GeneralLinearGroup.congrLinearEquiv e).injective
    apply Matrix.GeneralLinearGroup.toLin.symm.injective
    apply Units.ext
    exact congrArg Subtype.val hab
  let f : ℕ := Module.finrank (ZMod p) K
  have hKcard : Nat.card K = p ^ f := by
    exact (FiniteField.pow_finrank_eq_natCard p K).symm
  let qSL : Matrix.SpecialLinearGroup (Fin 2) K →*
      BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  let rhoPSL : H →* BenderSuzuki.MatrixGroups.PSL2MatrixGroup K := qSL.comp rhoSL
  let P : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) := rhoPSL.range
  let rhoP : H →* P := rhoPSL.rangeRestrict
  let px : P := rhoP x
  let py : P := rhoP y
  have hqnoncomm :
      qSL (rhoSL x) * qSL (rhoSL y) ≠ qSL (rhoSL y) * qSL (rhoSL x) := by
    intro hcomm
    have hqeq : qSL (rhoSL x * rhoSL y) = qSL (rhoSL y * rhoSL x) := by
      simpa using hcomm
    have hcenter :
        (rhoSL x * rhoSL y) / (rhoSL y * rhoSL x) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      QuotientGroup.eq_iff_div_mem.mp hqeq
    have hglcenter :
        Matrix.SpecialLinearGroup.toGL
            ((rhoSL x * rhoSL y) / (rhoSL y * rhoSL x)) ∈
          Subgroup.center (GL (Fin 2) K) :=
      (Matrix.SpecialLinearGroup.toGL_mem_center_iff _).2 hcenter
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hglcenter
    rcases hglcenter with ⟨a, ha⟩
    let g : Matrix.SpecialLinearGroup (Fin 2) K :=
      (rhoSL x * rhoSL y) / (rhoSL y * rhoSL x)
    have hgmat : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (a : K) := by
      change Matrix.scalar (Fin 2) (a : K) = (g : Matrix (Fin 2) (Fin 2) K) at ha
      exact ha.symm
    have hab : rhoSL x * rhoSL y = g * (rhoSL y * rhoSL x) := by
      dsimp [g]
      exact (div_mul_cancel _ _).symm
    have habmat := congrArg Subtype.val hab
    change
      ((rho x : Matrix (Fin 2) (Fin 2) K) * (rho y : Matrix (Fin 2) (Fin 2) K)) =
        (g : Matrix (Fin 2) (Fin 2) K) *
          ((rho y : Matrix (Fin 2) (Fin 2) K) *
            (rho x : Matrix (Fin 2) (Fin 2) K)) at habmat
    rw [hxmatrix, hymatrix, hgmat] at habmat
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) habmat
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) habmat
    have haone : (a : K) = 1 := by
      have haone' : (1 : K) = a := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] using h10
      exact haone'.symm
    apply hrne
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, haone] using h00
  have hpnoncomm : px * py ≠ py * px := by
    intro hcomm
    apply hqnoncomm
    exact congrArg Subtype.val hcomm
  have hxmatrixSL : (rhoSL x : Matrix (Fin 2) (Fin 2) K) = !![1, r; 0, 1] := by
    simpa [rhoSL] using hxmatrix
  have hymatrixSL : (rhoSL y : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := by
    simpa [rhoSL] using hymatrix
  refine ⟨e, rhoSL, hrhoSL, hxmatrixSL, hymatrixSL, (by
    intro h v
    change e ((rhoF h : V →ₗ[ZMod p] V) v) =
      (Matrix.GeneralLinearGroup.toLin (rho h)).toLinearEquiv (e v)
    simpa using (hrho_apply h (e v)).symm), ?_⟩
  have hxpow (n : ℕ) :
      ((rhoSL x) ^ n : Matrix (Fin 2) (Fin 2) K) = !![1, (n : K) * r; 0, 1] := by
    induction n with
    | zero =>
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
        rw [pow_succ]
        change
          (((rhoSL x) ^ n : Matrix (Fin 2) (Fin 2) K) *
            (rhoSL x : Matrix (Fin 2) (Fin 2) K)) = _
        rw [ih, hxmatrixSL]
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ]; ring
  have hypow (n : ℕ) :
      ((rhoSL y) ^ n : Matrix (Fin 2) (Fin 2) K) = !![1, 0; (n : K), 1] := by
    induction n with
    | zero =>
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
        rw [pow_succ]
        change
          (((rhoSL y) ^ n : Matrix (Fin 2) (Fin 2) K) *
            (rhoSL y : Matrix (Fin 2) (Fin 2) K)) = _
        rw [ih, hymatrixSL]
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ]
  have hpcast : (p : K) = 0 := by
    have hz := congrArg (algebraMap (ZMod p) K) (ZMod.natCast_self p)
    simpa only [map_zero, map_natCast] using hz
  have hxpowp : px ^ p = 1 := by
    apply Subtype.ext
    change (qSL (rhoSL x)) ^ p = 1
    rw [← map_pow]
    have hsl : (rhoSL x) ^ p = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      apply Units.ext
      change ((rhoSL x : Matrix (Fin 2) (Fin 2) K) ^ p) = 1
      rw [hxpow]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hpcast]
    rw [hsl, map_one]
  have hypowp : py ^ p = 1 := by
    apply Subtype.ext
    change (qSL (rhoSL y)) ^ p = 1
    rw [← map_pow]
    have hsl : (rhoSL y) ^ p = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      apply Units.ext
      change ((rhoSL y : Matrix (Fin 2) (Fin 2) K) ^ p) = 1
      rw [hypow]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hpcast]
    rw [hsl, map_one]
  have hxne : px ≠ 1 := by
    intro hxone
    apply hpnoncomm
    simp [hxone]
  have hyne : py ≠ 1 := by
    intro hyone
    apply hpnoncomm
    simp [hyone]
  have hxorder : orderOf px = p := orderOf_eq_prime hxpowp hxne
  have hyorder : orderOf py = p := orderOf_eq_prime hypowp hyne
  have hpgen : Subgroup.closure ({px, py} : Set P) = ⊤ := by
    let Q : Subgroup P := Subgroup.closure ({px, py} : Set P)
    have hxQ : x ∈ Q.comap rhoP := by
      change px ∈ Q
      exact Subgroup.subset_closure (by simp)
    have hyQ : y ∈ Q.comap rhoP := by
      change py ∈ Q
      exact Subgroup.subset_closure (by simp)
    have hle : Subgroup.closure ({x, y} : Set H) ≤ Q.comap rhoP := by
      rw [Subgroup.closure_le]
      intro z hz
      have hz' : z = x ∨ z = y := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hxQ
      · exact hyQ
    apply top_unique
    intro z _hz
    rcases z.2 with ⟨h, hh⟩
    have hz : z = rhoP h := Subtype.ext hh.symm
    rw [hz]
    exact hle (hcl ▸ (trivial : h ∈ (⊤ : Subgroup H)))
  have hclassification :=
    Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hKcard P
  have hr_mem_of_witness (m : ℕ)
      (W : Dickson.SubfieldConjugacyWitness p m P) : r ∈ W.K := by
    let : Fintype K := Fintype.ofFinite K
    let : CharP K p := charP_of_card_eq_prime_pow (by
      simpa [Nat.card_eq_fintype_card] using hKcard)
    have htwo : (2 : K) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hpodd
    have htraceX : Matrix.trace
        (rhoSL x : Matrix (Fin 2) (Fin 2) K) = 2 := by
      rw [hxmatrixSL]
      simp [Matrix.trace, Fin.sum_univ_two]
      ring
    have htraceY : Matrix.trace
        (rhoSL y : Matrix (Fin 2) (Fin 2) K) = 2 := by
      rw [hymatrixSL]
      simp [Matrix.trace, Fin.sum_univ_two]
      ring
    have htraceXY : Matrix.trace
        ((rhoSL x * rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = 2 + r := by
      change Matrix.trace
        ((rhoSL x : Matrix (Fin 2) (Fin 2) K) *
          (rhoSL y : Matrix (Fin 2) (Fin 2) K)) = 2 + r
      rw [hxmatrixSL, hymatrixSL]
      simp [Matrix.trace, Fin.sum_univ_two]
      ring
    have hratio := Dickson.normalizedTrace_mem_subfield P W px py
      (rhoSL x) (rhoSL y) (by rfl) (by rfl)
      (by rw [htraceX]; exact htwo) (by rw [htraceY]; exact htwo)
    have hratio' : (2 + r) / 4 ∈ W.K := by
      rw [htraceXY, htraceX, htraceY] at hratio
      convert hratio using 1 <;> ring
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero htwo htwo
    have hr_formula : r = 4 * ((2 + r) / 4) - 2 := by
      field_simp [hfour]
      ring
    rw [hr_formula]
    exact W.K.sub_mem (W.K.mul_mem (natCast_mem W.K 4) hratio')
      (natCast_mem W.K 2)
  have hdegree_le_of_witness (m : ℕ)
      (W : Dickson.SubfieldConjugacyWitness p m P) : f ≤ m := by
    let : Fintype K := Fintype.ofFinite K
    let : CharP K p := charP_of_card_eq_prime_pow (by
      simpa [Nat.card_eq_fintype_card] using hKcard)
    have halgmem (a : ZMod p) : algebraMap (ZMod p) K a ∈ W.K := by
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
      simpa using natCast_mem W.K n
    let E : IntermediateField (ZMod p) K := W.K.toIntermediateField halgmem
    let r0 : E := ⟨r, hr_mem_of_witness m W⟩
    have hminpoly : minpoly (ZMod p) r = minpoly (ZMod p) r0 := by
      exact minpoly.algHom_eq E.val E.val.injective r0
    have hdegree_bound :
        (minpoly (ZMod p) r0).natDegree ≤ Module.finrank (ZMod p) E :=
      minpoly.natDegree_le r0
    have hEcard : Nat.card E = p ^ m := by
      exact W.card_eq
    have hErank : Module.finrank (ZMod p) E = m := by
      apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
      calc
        p ^ Module.finrank (ZMod p) E = Nat.card E :=
          FiniteField.pow_finrank_eq_natCard p E
        _ = p ^ m := hEcard
    change Module.finrank (ZMod p) K ≤ m
    rw [hdegree, hminpoly]
    simpa [hErank] using hdegree_bound
  have hfne : f ≠ 0 :=
    Dickson.huppert_II_8_27_field_exponent_ne_zero hKcard
  have hpsl_card_formula (L : Type) [Field L] [Finite L]
      (htwo : (2 : L) ≠ 0) :
      Nat.card (BenderSuzuki.MatrixGroups.PSL2MatrixGroup L) =
        Nat.card L * (Nat.card L ^ 2 - 1) / 2 := by
    have hneg : (-1 : L) ≠ 1 := by
      intro h
      apply htwo
      calc
        (2 : L) = 1 + 1 := by norm_num
        _ = 1 + -1 := by rw [h]
        _ = 0 := add_neg_cancel 1
    have hc :=
      BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg
    have hmul :=
      BenderSuzuki.External.huppert614_card_psl_mul_center (K := L)
    rw [hc] at hmul
    exact Nat.eq_div_of_mul_eq_right (by norm_num : 2 ≠ 0)
      (by simpa [mul_comm] using hmul)
  have hxyne : px * py ≠ 1 := by
    intro hxy
    apply hpnoncomm
    calc
      px * py = 1 := hxy
      _ = py * px := by
        rw [(mul_eq_one_iff_eq_inv.mp hxy)]
        simp
  have hxyorder_ne_one : orderOf (px * py) ≠ 1 := by
    intro horder
    exact hxyne (orderOf_eq_one_iff.mp horder)
  have hxyMatrix :
      ((rhoSL x * rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = !![1 + r, r; 1, 1] := by
    change
      (rhoSL x : Matrix (Fin 2) (Fin 2) K) *
        (rhoSL y : Matrix (Fin 2) (Fin 2) K) = _
    rw [hxmatrixSL, hymatrixSL]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hpow_mem_center (n : ℕ) (horder : orderOf (px * py) = n) :
      (rhoSL x * rhoSL y) ^ n ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    apply (QuotientGroup.eq_one_iff ((rhoSL x * rhoSL y) ^ n)).mp
    change qSL ((rhoSL x * rhoSL y) ^ n) = 1
    rw [map_pow, map_mul]
    have hpown : (px * py) ^ n = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one _
    exact congrArg Subtype.val hpown
  have hpoly_two (horder : orderOf (px * py) = 2) : r + 2 = 0 := by
    have hc := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
      (hpow_mem_center 2 horder) 0
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hc
    rw [Matrix.scalar_apply] at h10
    simp only [OfNat.ofNat] at h10
    change 0 =
      ((((rhoSL x * rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) ^ 2) 1 0) at h10
    rw [hxyMatrix] at h10
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h10
    ring_nf at h10 ⊢
    exact h10.symm
  have hpoly_three (horder : orderOf (px * py) = 3) :
      (r + 1) * (r + 3) = 0 := by
    have hc := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
      (hpow_mem_center 3 horder) 0
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hc
    rw [Matrix.scalar_apply] at h10
    simp only [OfNat.ofNat] at h10
    change 0 =
      ((((rhoSL x * rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) ^ 3) 1 0) at h10
    rw [hxyMatrix] at h10
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h10
    ring_nf at h10 ⊢
    exact h10.symm
  have hpoly_five (horder : orderOf (px * py) = 5) :
      (r ^ 2 + 3 * r + 1) * (r ^ 2 + 5 * r + 5) = 0 := by
    have hc := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
      (hpow_mem_center 5 horder) 0
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hc
    rw [Matrix.scalar_apply] at h10
    simp only [OfNat.ofNat] at h10
    change 0 =
      ((((rhoSL x * rhoSL y : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) ^ 5) 1 0) at h10
    rw [hxyMatrix] at h10
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h10
    ring_nf at h10 ⊢
    exact h10.symm
  have hf_eq_one_of_add_nat (n : ℕ) (hr : r + n = 0) : f = 1 := by
    have hre : r = -(n : K) := eq_neg_of_add_eq_zero_left hr
    have hrange : r ∈ (algebraMap (ZMod p) K).range := by
      refine ⟨-(n : ZMod p), ?_⟩
      simpa using hre.symm
    have hmin := minpoly.natDegree_eq_one_iff.mpr hrange
    change Module.finrank (ZMod p) K = 1
    rw [hdegree, hmin]
  have hf_eq_one_of_mem_base
      (hrange : r ∈ (algebraMap (ZMod p) K).range) : f = 1 := by
    have hmin := minpoly.natDegree_eq_one_iff.mpr hrange
    change Module.finrank (ZMod p) K = 1
    rw [hdegree, hmin]
  have hf_le_two_of_quadratic (a b : ZMod p)
      (hr : r ^ 2 + algebraMap (ZMod p) K a * r +
        algebraMap (ZMod p) K b = 0) : f ≤ 2 := by
    let q : Polynomial (ZMod p) :=
      Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b
    have hroot : Polynomial.aeval r q = 0 := by
      simpa [q] using hr
    have hdvd : minpoly (ZMod p) r ∣ q := minpoly.dvd (ZMod p) r hroot
    have hqmonic : q.Monic := by
      exact (Polynomial.isMonicOfDegree_add_add_two a b).monic
    have hle : (minpoly (ZMod p) r).natDegree ≤ q.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hqmonic.ne_zero
    have hqdegree : q.natDegree = 2 :=
      (Polynomial.isMonicOfDegree_add_add_two a b).natDegree_eq
    change Module.finrank (ZMod p) K ≤ 2
    rw [← hdegree, hqdegree] at hle
    exact hle
  have hrange_eq_closure : rhoSL.range =
      Subgroup.closure ({rhoSL x, rhoSL y} :
        Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    rw [rhoSL.range_eq_map, ← hcl, MonoidHom.map_closure]
    congr 1
    ext z
    simp [eq_comm]
  have hSL_of_f_eq_one (hf_one : f = 1) :
      Function.Surjective rhoSL := by
    let X : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have hxEq : rhoSL x = X := by
      apply Subtype.ext
      exact hxmatrixSL
    have hyEq : rhoSL y = Y := by
      apply Subtype.ext
      exact hymatrixSL
    have hgen : Subgroup.closure ({X, Y} : Set _) = ⊤ := by
      exact Dickson.standard_two_transvections_generate_of_finrank_one r hrne hf_one
    have hrange_top : rhoSL.range = ⊤ := by
      rw [hrange_eq_closure, hxEq, hyEq]
      exact hgen
    rw [← MonoidHom.range_eq_top]
    exact hrange_top
  have hnotElementary : ¬ IsElementaryAbelian p P := by
    intro h
    let : IsElementaryAbelian p P := h
    exact hpnoncomm (mul_comm' px py)
  have hnotCyclic : ¬ IsCyclic P := by
    intro h
    let : IsCyclic P := h
    let : CommGroup P := IsCyclic.commGroup
    exact hpnoncomm (mul_comm px py)
  have hnotDihedral (z : ℕ) : ¬ Nonempty (P ≃* DihedralGroup z) := by
    rintro ⟨ez⟩
    have hox : orderOf (ez px) = p := by
      rw [ez.orderOf_eq, hxorder]
    have hoy : orderOf (ez py) = p := by
      rw [ez.orderOf_eq, hyorder]
    have hxrot : ∃ i : ZMod z, ez px = DihedralGroup.r i := by
      generalize heqx : ez px = gx at hox ⊢
      cases gx with
      | r i => exact ⟨i, rfl⟩
      | sr i =>
          rw [DihedralGroup.orderOf_sr] at hox
          exact (hpodd hox.symm).elim
    have hyrot : ∃ i : ZMod z, ez py = DihedralGroup.r i := by
      generalize heqy : ez py = gy at hoy ⊢
      cases gy with
      | r i => exact ⟨i, rfl⟩
      | sr i =>
          rw [DihedralGroup.orderOf_sr] at hoy
          exact (hpodd hoy.symm).elim
    rcases hxrot with ⟨i, hxi⟩
    rcases hyrot with ⟨j, hyj⟩
    apply hpnoncomm
    apply ez.injective
    rw [map_mul, map_mul, hxi, hyj, DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_r, add_comm]
  have hnotS4 : ¬ Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
    rintro ⟨e4⟩
    have hpdiv : p ∣ 24 := by
      have hd := orderOf_dvd_natCard (e4 px)
      rw [e4.orderOf_eq, hxorder, Nat.card_perm, Nat.card_fin, Nat.factorial] at hd
      norm_num at hd ⊢
      exact hd
    have hp3 : p = 3 := by
      have hpdiv' : p ∣ 3 * 8 := by norm_num at hpdiv ⊢; exact hpdiv
      rcases (Fact.out : p.Prime).dvd_mul.mp hpdiv' with hpdiv3 | hpdiv8
      · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (by decide : Nat.Prime 3)).mp hpdiv3
      · have hpdiv2 : p ∣ 2 := by
          have hpdivpow : p ∣ 2 ^ 3 := by simpa using hpdiv8
          exact (Fact.out : p.Prime).dvd_of_dvd_pow hpdivpow
        exact (hpodd
          ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpdiv2)).elim
    have hodd_mem (g : Equiv.Perm (Fin 4)) (hg : orderOf g = p) :
        g ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs | hs
      · exact hs
      · exfalso
        have hd := orderOf_map_dvd Equiv.Perm.sign g
        rw [hs, hg, hp3] at hd
        have hminus : orderOf (-1 : ℤˣ) = 2 :=
          orderOf_eq_prime (Int.units_sq _) (by decide)
        rw [hminus] at hd
        norm_num at hd
    have hxA : e4 px ∈ alternatingGroup (Fin 4) :=
      hodd_mem (e4 px) (by rw [e4.orderOf_eq, hxorder])
    have hyA : e4 py ∈ alternatingGroup (Fin 4) :=
      hodd_mem (e4 py) (by rw [e4.orderOf_eq, hyorder])
    let Q4 : Subgroup (Equiv.Perm (Fin 4)) :=
      Subgroup.closure ({e4 px, e4 py} : Set (Equiv.Perm (Fin 4)))
    have hgen4 : Q4 = ⊤ := by
      have hxQ : px ∈ Q4.comap e4.toMonoidHom := by
        change e4 px ∈ Q4
        exact Subgroup.subset_closure (by simp)
      have hyQ : py ∈ Q4.comap e4.toMonoidHom := by
        change e4 py ∈ Q4
        exact Subgroup.subset_closure (by simp)
      have hle : Subgroup.closure ({px, py} : Set P) ≤ Q4.comap e4.toMonoidHom := by
        rw [Subgroup.closure_le]
        intro z hz
        have hz' : z = px ∨ z = py := by simpa using hz
        rcases hz' with rfl | rfl
        · exact hxQ
        · exact hyQ
      apply top_unique
      intro g _hg
      rcases e4.surjective g with ⟨z, rfl⟩
      exact hle (hpgen ▸ (trivial : z ∈ (⊤ : Subgroup P)))
    have hQA : Q4 ≤ alternatingGroup (Fin 4) := by
      rw [Subgroup.closure_le]
      intro z hz
      have hz' : z = e4 px ∨ z = e4 py := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hxA
      · exact hyA
    have hswap : Equiv.swap (0 : Fin 4) 1 ∈ alternatingGroup (Fin 4) :=
      hQA (hgen4 ▸ (trivial : Equiv.swap (0 : Fin 4) 1 ∈
        (⊤ : Subgroup (Equiv.Perm (Fin 4)))))
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hswap
    norm_num at hswap
  have hnotSemidirect (m t : ℕ) (N C : Subgroup P)
      (hNnormal : N.Normal) (hNelem : IsElementaryAbelian p N)
      (hCcard : Nat.card C = t)
      (htAmbient : t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2)
      (hsup : N ⊔ C = ⊤) : False := by
    have hfne : f ≠ 0 := Dickson.huppert_II_8_27_field_exponent_ne_zero hKcard
    have htPow : t ∣ p ^ f - 1 :=
      dvd_trans htAmbient (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (p ^ f - 1) 2))
    have hpNotPowSub : ¬ p ∣ p ^ f - 1 := by
      intro hpSub
      have hpPow : p ∣ p ^ f := dvd_pow_self p hfne
      have hpowPos : 0 < p ^ f := pow_pos (Fact.out : p.Prime).pos f
      have hsum : p ∣ (p ^ f - 1) + 1 := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ p ^ f)]
        exact hpPow
      have hpOne : p ∣ 1 := (Nat.dvd_add_iff_right hpSub).2 hsum
      exact (Fact.out : p.Prime).not_dvd_one hpOne
    have hpt : Nat.Coprime p t :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun hptDvd =>
        hpNotPowSub (dvd_trans hptDvd htPow)
    let : N.Normal := hNnormal
    have memN_of_pow (g : P) (hgp : g ^ p = 1) : g ∈ N := by
      have hgSup : g ∈ N ⊔ C := hsup.symm ▸ (trivial : g ∈ (⊤ : Subgroup P))
      rcases Subgroup.mem_sup_of_normal_left.mp hgSup with ⟨n, hn, c, hc, hnc⟩
      let qN : P →* P ⧸ N := QuotientGroup.mk' N
      have hqeq : qN g = qN c := by
        have hqn : qN n = 1 := by
          dsimp [qN]
          exact (QuotientGroup.eq_one_iff n).2 hn
        rw [← hnc, map_mul, hqn, one_mul]
      have hqpow : (qN g) ^ p = 1 := by
        rw [← map_pow, hgp, map_one]
      have horderP : orderOf (qN g) ∣ p := orderOf_dvd_of_pow_eq_one hqpow
      let cc : C := ⟨c, hc⟩
      have horderMap : orderOf ((qN.comp C.subtype) cc) ∣ orderOf cc :=
        orderOf_map_dvd (qN.comp C.subtype) cc
      have hmapEq : (qN.comp C.subtype) cc = qN g := by
        exact hqeq.symm
      rw [hmapEq] at horderMap
      have horderCard : orderOf cc ∣ t := by
        rw [← hCcard]
        exact orderOf_dvd_natCard cc
      have horderT : orderOf (qN g) ∣ t := dvd_trans horderMap horderCard
      have horderOne : orderOf (qN g) = 1 :=
        Nat.eq_one_of_dvd_coprimes hpt horderP horderT
      exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp horderOne)
    have hxN : px ∈ N := memN_of_pow px hxpowp
    have hyN : py ∈ N := memN_of_pow py hypowp
    let : IsElementaryAbelian p N := hNelem
    have hcommN : (⟨px, hxN⟩ : N) * ⟨py, hyN⟩ =
        (⟨py, hyN⟩ : N) * ⟨px, hxN⟩ := mul_comm' _ _
    exact hpnoncomm (congrArg Subtype.val hcommN)
  rcases hclassification with hElementary | hCyclic | hDihedral | hA4 |
      hS4 | hA5 | hSemidirect | hPSL | hPGL
  · exact (hnotElementary hElementary).elim
  · rcases hCyclic with ⟨_z, _hz, _hcard, hcyclic⟩
    exact (hnotCyclic hcyclic).elim
  · rcases hDihedral with ⟨z, _hz, _hcard, hdihedral⟩
    exact (hnotDihedral z hdihedral).elim
  · rcases hA4 with ⟨_hparity, ⟨e4⟩⟩
    have hene : e4 (px * py) ≠ 1 := by
      intro he
      apply hxyne
      apply e4.injective
      simpa using he
    have hpowers :
        (e4 (px * py)) ^ 2 = 1 ∨ (e4 (px * py)) ^ 3 = 1 := by
      have hsmall : ∀ g : alternatingGroup (Fin 4), g ≠ 1 →
          g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide
      exact hsmall _ hene
    rcases hpowers with hpow2 | hpow3
    · have horder : orderOf (px * py) = 2 := by
        have heorder : orderOf (e4 (px * py)) = 2 :=
          orderOf_eq_prime hpow2 hene
        rwa [e4.orderOf_eq] at heorder
      exact Or.inl (hSL_of_f_eq_one
        (hf_eq_one_of_add_nat 2 (hpoly_two horder)))
    · have horder : orderOf (px * py) = 3 := by
        have heorder : orderOf (e4 (px * py)) = 3 :=
          orderOf_eq_prime hpow3 hene
        rwa [e4.orderOf_eq] at heorder
      rcases mul_eq_zero.mp (hpoly_three horder) with hr1 | hr3
      · exact Or.inl (hSL_of_f_eq_one
          (hf_eq_one_of_add_nat 1 (by simpa using hr1)))
      · exact Or.inl (hSL_of_f_eq_one (hf_eq_one_of_add_nat 3 hr3))
  · exact (hnotS4 hS4.2).elim
  · rcases hA5 with ⟨_hfive, ⟨e5⟩⟩
    have hpdiv : p ∣ 60 := by
      have hd := orderOf_dvd_natCard (e5 px)
      rw [e5.orderOf_eq, hxorder, nat_card_alternatingGroup,
        Nat.card_fin, Nat.factorial] at hd
      norm_num at hd ⊢
      exact hd
    have hp35 : p = 3 ∨ p = 5 := by
      have hpdiv' : p ∣ 3 * (4 * 5) := by
        norm_num at hpdiv ⊢
        exact hpdiv
      rcases (Fact.out : p.Prime).dvd_mul.mp hpdiv' with hp3 | hp20
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (by decide : Nat.Prime 3)).mp hp3)
      · rcases (Fact.out : p.Prime).dvd_mul.mp hp20 with hp4 | hp5
        · have hp2 : p ∣ 2 := by
            have hp4' : p ∣ 2 ^ 2 := by
              norm_num at hp4 ⊢
              exact hp4
            apply (Fact.out : p.Prime).dvd_of_dvd_pow
            exact hp4'
          exact (hpodd
            ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
              Nat.prime_two).mp hp2)).elim
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
            (by decide : Nat.Prime 5)).mp hp5)
    have hene : e5 (px * py) ≠ 1 := by
      intro he
      apply hxyne
      apply e5.injective
      simpa using he
    have hpowers : (e5 (px * py)) ^ 2 = 1 ∨
        (e5 (px * py)) ^ 3 = 1 ∨ (e5 (px * py)) ^ 5 = 1 := by
      have hsmall : ∀ g : alternatingGroup (Fin 5), g ≠ 1 →
          g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
        set_option maxRecDepth 10000 in
          decide
      exact hsmall _ hene
    have horders : orderOf (px * py) = 2 ∨
        orderOf (px * py) = 3 ∨ orderOf (px * py) = 5 := by
      rcases hpowers with hpow2 | hpow3 | hpow5
      · left
        have heorder : orderOf (e5 (px * py)) = 2 :=
          orderOf_eq_prime hpow2 hene
        rwa [e5.orderOf_eq] at heorder
      · right; left
        have heorder : orderOf (e5 (px * py)) = 3 :=
          orderOf_eq_prime hpow3 hene
        rwa [e5.orderOf_eq] at heorder
      · right; right
        let : Fact (Nat.Prime 5) := ⟨by decide⟩
        have heorder : orderOf (e5 (px * py)) = 5 :=
          orderOf_eq_prime hpow5 hene
        rwa [e5.orderOf_eq] at heorder
    rcases hp35 with rfl | rfl
    · rcases horders with horder2 | horder3 | horder5
      · exact Or.inl (hSL_of_f_eq_one
          (hf_eq_one_of_add_nat 2 (hpoly_two horder2)))
      · rcases mul_eq_zero.mp (hpoly_three horder3) with hr1 | hr3
        · exact Or.inl (hSL_of_f_eq_one
            (hf_eq_one_of_add_nat 1 (by simpa using hr1)))
        · exact Or.inl (hSL_of_f_eq_one (hf_eq_one_of_add_nat 3 hr3))
      · rcases mul_eq_zero.mp (hpoly_five horder5) with hrfirst | hrsecond
        · have hrquad : r ^ 2 +
              algebraMap (ZMod 3) K 0 * r +
              algebraMap (ZMod 3) K 1 = 0 := by
            have hrquad' : r ^ 2 + 1 = 0 := by
              linear_combination hrfirst - r * hpcast
            simpa using hrquad'
          have hfle : f ≤ 2 := hf_le_two_of_quadratic 0 1 hrquad
          have hfcase : f = 1 ∨ f = 2 := by omega
          rcases hfcase with hf1 | hf2
          · exact Or.inl (hSL_of_f_eq_one hf1)
          · have hcard9 : Nat.card K = 9 := by
              rw [hKcard, hf2]
              norm_num
            let X : Matrix.SpecialLinearGroup (Fin 2) K :=
              ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
            let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
              ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
            have hxEq : rhoSL x = X := by
              apply Subtype.ext
              exact hxmatrixSL
            have hyEq : rhoSL y = Y := by
              apply Subtype.ext
              exact hymatrixSL
            have hrangeClosure : rhoSL.range =
                Subgroup.closure ({X, Y} : Set _) := by
              simpa [hxEq, hyEq] using hrange_eq_closure
            have hrquad' : r ^ 2 + 1 = 0 := by
              linear_combination hrfirst - r * hpcast
            rcases exceptionalF9_two_transvections_equiv_sl2_five hcard9 r hrquad' with ⟨eExceptional⟩
            exact Or.inr ⟨hcard9, hrquad', ⟨
              (MonoidHom.ofInjective hrhoSL).trans
                ((MulEquiv.subgroupCongr hrangeClosure).trans eExceptional)⟩⟩
        · have hrquad : r ^ 2 +
              algebraMap (ZMod 3) K 2 * r +
              algebraMap (ZMod 3) K 2 = 0 := by
            have hrquad' : r ^ 2 + 2 * r + 2 = 0 := by
              linear_combination hrsecond - (r + 1) * hpcast
            simpa only [map_ofNat] using hrquad'
          have hfle : f ≤ 2 := hf_le_two_of_quadratic 2 2 hrquad
          have hfcase : f = 1 ∨ f = 2 := by omega
          rcases hfcase with hf1 | hf2
          · exact Or.inl (hSL_of_f_eq_one hf1)
          · have hcard9 : Nat.card K = 9 := by
              rw [hKcard, hf2]
              norm_num
            let X : Matrix.SpecialLinearGroup (Fin 2) K :=
              ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
            let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
              ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
            have hxEq : rhoSL x = X := by
              apply Subtype.ext
              exact hxmatrixSL
            have hyEq : rhoSL y = Y := by
              apply Subtype.ext
              exact hymatrixSL
            have hgen : Subgroup.closure ({X, Y} : Set _) = ⊤ := by
              exact secondF9_two_transvections_generate hcard9 r
                (by linear_combination hrsecond - (r + 1) * hpcast)
            have hrangeTop : rhoSL.range = ⊤ := by
              rw [hrange_eq_closure, hxEq, hyEq]
              exact hgen
            have hrhoSLsurj : Function.Surjective rhoSL := by
              rw [← MonoidHom.range_eq_top]
              exact hrangeTop
            exact Or.inl hrhoSLsurj
    · rcases horders with horder2 | horder3 | horder5
      · exact Or.inl (hSL_of_f_eq_one
          (hf_eq_one_of_add_nat 2 (hpoly_two horder2)))
      · rcases mul_eq_zero.mp (hpoly_three horder3) with hr1 | hr3
        · exact Or.inl (hSL_of_f_eq_one
            (hf_eq_one_of_add_nat 1 (by simpa using hr1)))
        · exact Or.inl (hSL_of_f_eq_one (hf_eq_one_of_add_nat 3 hr3))
      · rcases mul_eq_zero.mp (hpoly_five horder5) with hrfirst | hrsecond
        · have hsquare : (r - 1) ^ 2 = 0 := by
            linear_combination hrfirst - r * hpcast
          have hre : r = 1 :=
            sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsquare)
          have hr4 : r + 4 = 0 := by
            calc
              r + 4 = (5 : K) := by rw [hre]; norm_num
              _ = 0 := hpcast
          exact Or.inl (hSL_of_f_eq_one (hf_eq_one_of_add_nat 4 hr4))
        · have hrsquare : r ^ 2 = 0 := by
            linear_combination hrsecond - (r + 1) * hpcast
          exact (hrne (eq_zero_of_pow_eq_zero hrsquare)).elim
  · rcases hSemidirect with
      ⟨m, t, _htsmall, htAmbient, N, C, hNnormal, hNelem,
        _hNcard, _hCcyclic, hCcard, _hdisjoint, hsup⟩
    exact (hnotSemidirect m t N C hNnormal hNelem hCcard htAmbient hsup).elim
  · rcases hPSL with ⟨m, hmne, hmdiv, ⟨eP⟩, ⟨W⟩⟩
    let : Fintype K := Fintype.ofFinite K
    let : CharP K p := charP_of_card_eq_prime_pow (by
      simpa [Nat.card_eq_fintype_card] using hKcard)
    have hfm : f ≤ m := hdegree_le_of_witness m W
    have hmf : m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hfne) hmdiv
    have hmfEq : m = f := by omega
    have htwoK : (2 : K) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hpodd
    have htwoGF : (2 : GaloisField p m) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (GaloisField p m) Nat.prime_two hpodd
    have hGFcard : Nat.card (GaloisField p m) = p ^ m :=
      GaloisField.card p m hmne
    have hPcard : Nat.card P =
        Nat.card (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) := by
      calc
        Nat.card P = Nat.card
            (BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p m)) :=
          Nat.card_congr eP.toEquiv
        _ = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
          rw [hpsl_card_formula _ htwoGF, hGFcard]
        _ = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by rw [hmfEq]
        _ = Nat.card (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) := by
          rw [hpsl_card_formula _ htwoK, hKcard]
    have hPtop : P = ⊤ := Subgroup.eq_top_of_card_eq P hPcard
    by_cases hf1 : f = 1
    · exact Or.inl (hSL_of_f_eq_one hf1)
    · have hrsq : r ^ 2 ≠ 1 := by
        intro hrsq
        have hfactor : (r - 1) * (r + 1) = 0 := by
          calc
            (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
            _ = 0 := sub_eq_zero.mpr hrsq
        rcases mul_eq_zero.mp hfactor with hrone | hrneg
        · apply hf1
          apply hf_eq_one_of_mem_base
          refine ⟨1, ?_⟩
          simp [sub_eq_zero.mp hrone]
        · apply hf1
          apply hf_eq_one_of_mem_base
          refine ⟨-1, ?_⟩
          simp [eq_neg_of_add_eq_zero_left hrneg]
      let R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := rhoSL.range
      let Z : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)
      have hsup : R ⊔ Z = ⊤ := by
        apply top_unique
        intro g _hg
        have hgP : qSL g ∈ P := by
          rw [hPtop]
          trivial
        rcases hgP with ⟨h, hh⟩
        change qSL (rhoSL h) = qSL g at hh
        have hz : rhoSL h / g ∈ Z := QuotientGroup.eq_iff_div_mem.mp hh
        have hrange : rhoSL h ∈ R := ⟨h, rfl⟩
        have hzsup : (rhoSL h / g)⁻¹ ∈ R ⊔ Z :=
          (R ⊔ Z).inv_mem ((le_sup_right : Z ≤ R ⊔ Z) hz)
        have hrsup : rhoSL h ∈ R ⊔ Z :=
          (le_sup_left : R ≤ R ⊔ Z) hrange
        rw [show g = (rhoSL h / g)⁻¹ * rhoSL h by
          simp [div_eq_mul_inv]]
        exact (R ⊔ Z).mul_mem hzsup hrsup
      have hnormalizer : Subgroup.normalizer
          (R : Set (Matrix.SpecialLinearGroup (Fin 2) K)) = ⊤ := by
        apply top_unique
        rw [← hsup]
        exact sup_le R.le_normalizer
          (Subgroup.center_le_normalizer
            (R : Set (Matrix.SpecialLinearGroup (Fin 2) K)))
      let : R.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
      have hcommLe : _root_.commutator
          (Matrix.SpecialLinearGroup (Fin 2) K) ≤ R :=
        Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
          hsup (by infer_instance)
      have hcommTop : _root_.commutator
          (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
        Matrix.SL2.commutator_eq_top hrne hrsq
      have hRtop : R = ⊤ := by
        apply top_unique
        rw [← hcommTop]
        exact hcommLe
      have hrhoSLsurj : Function.Surjective rhoSL := by
        rw [← MonoidHom.range_eq_top]
        exact hRtop
      exact Or.inl hrhoSLsurj
  · rcases hPGL with ⟨m, hmne, hdiv, _ePGL, ⟨W⟩⟩
    have hfm : f ≤ m := hdegree_le_of_witness m W
    have htwomf : 2 * m ≤ f :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hfne) hdiv
    omega

/-- The abstract classification endpoint, obtained by forgetting the aligned
representation data and the exceptional root equation. -/
public theorem two_transvections_classification
    (rhoF : H →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hrhoF : Function.Injective rhoF)
    (K : Type) [Field K] [Algebra (ZMod p) K] [Module K V] [Finite K]
    (hlinear : ∀ h : H, ∀ k : K, ∀ v : V,
      (rhoF h : V →ₗ[ZMod p] V) (k • v) =
        k • (rhoF h : V →ₗ[ZMod p] V) v) :
      ∀ coord : LinearEquiv (RingHom.id K) V (K × K),
      ∀ r : K, ∀ x y : H,
      Module.finrank (ZMod p) K = (minpoly (ZMod p) r).natDegree →
      r ≠ 0 →
      Subgroup.closure ({x, y} : Set H) = ⊤ →
      (∀ a c : K,
        coord.toFun ((rhoF x : V →ₗ[ZMod p] V)
          (coord.symm.toFun (a, c))) = (a + r * c, c)) →
      (∀ a c : K,
        coord.toFun ((rhoF y : V →ₗ[ZMod p] V)
          (coord.symm.toFun (a, c))) = (a, c + a)) →
      Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∨
        (Nat.card K = 9 ∧
          Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) := by
  intro coord r x y hdegree hrne hcl hxmodel hymodel
  rcases two_transvections_classification_aligned (hpodd := hpodd)
      rhoF hrhoF K hlinear coord r x y hdegree hrne hcl hxmodel hymodel with
    ⟨_coordFin, rhoSL, hrhoSL, _hxmat, _hymat, _haction, hfull | hexceptional⟩
  · exact Or.inl ⟨MulEquiv.ofBijective rhoSL ⟨hrhoSL, hfull⟩⟩
  · exact Or.inr ⟨hexceptional.1, hexceptional.2.2⟩

end Dickson
end CFSG.Glauberman
