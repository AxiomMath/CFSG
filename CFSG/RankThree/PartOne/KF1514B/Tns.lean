module

public import CFSG.RankThree.PartOne.KF1514B.Param
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open Matrix CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section Mat

variable {K : Type} [Field K] [CharP K 2] (b c : K)

@[expose] def nrm (z : K × K) : K := z.1 ^ 2 + b * z.1 * z.2 + c * z.2 ^ 2

@[expose] def Mmat (z : K × K) : Matrix (Fin 2) (Fin 2) K := !![z.1, c * z.2; z.2, z.1 + b * z.2]

@[expose] def zmul (z w : K × K) : K × K :=
  (z.1 * w.1 + c * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2)

theorem Mmat_mul (z w : K × K) : Mmat b c z * Mmat b c w = Mmat b c (zmul b c z w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mmat, zmul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Mmat_one : Mmat b c (1, 0) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mmat]

theorem det_Mmat (z : K × K) : (Mmat b c z).det = nrm b c z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two]
  simp only [Mmat, nrm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination (-c * z.2 ^ 2) * h2

theorem nrm_zmul (z w : K × K) : nrm b c (zmul b c z w) = nrm b c z * nrm b c w := by
  rw [← det_Mmat, ← Mmat_mul, Matrix.det_mul, det_Mmat, det_Mmat]

theorem zmul_comm (z w : K × K) : zmul b c z w = zmul b c w z := by
  simp only [zmul]
  ext <;> simp <;> ring

@[expose] def zconj (z : K × K) : K × K := (z.1 + b * z.2, z.2)

theorem zmul_zconj (z : K × K) : zmul b c z (zconj b z) = (nrm b c z, 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [zmul, zconj, nrm]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    linear_combination (z.1 * z.2 + b * z.2 ^ 2) * h2

theorem nrm_zconj (z : K × K) : nrm b c (zconj b z) = nrm b c z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [zconj, nrm]
  linear_combination (b * z.1 * z.2 + b ^ 2 * z.2 ^ 2) * h2

theorem Mmat_isometry (z : K × K) (a : Fin 2 → K) :
    minusTailForm K b c ((Mmat b c z).mulVec a) = nrm b c z * minusTailForm K b c a := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [minusTailForm_apply, minusTailForm_apply]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Mmat, nrm, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination (a 0 * a 1 * b * c * z.2 ^ 2 + 2 * a 0 * a 1 * c * z.1 * z.2 +
    a 1 ^ 2 * b ^ 2 * c * z.2 ^ 2 + a 1 ^ 2 * b * c * z.1 * z.2) * h2

end Mat

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

variable (b c) in
@[expose] noncomputable def Tns : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∃ z : K × K, nrm b c z = 1 ∧ (g : Matrix (Fin 2) (Fin 2) K) = Mmat b c z}
  one_mem' := ⟨(1, 0), by simp [nrm], by rw [Units.val_one, Mmat_one]⟩
  mul_mem' := by
    rintro g g' ⟨z, hz, hgz⟩ ⟨w, hw, hgw⟩
    refine ⟨zmul b c z w, by rw [nrm_zmul, hz, hw, one_mul], ?_⟩
    rw [Units.val_mul, hgz, hgw, Mmat_mul]
  inv_mem' := by
    rintro g ⟨z, hz, hgz⟩
    refine ⟨zconj b z, by rw [nrm_zconj, hz], ?_⟩
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * Mmat b c (zconj b z) = 1 := by
      rw [hgz, Mmat_mul, zmul_zconj, hz, Mmat_one]
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_right_inv h1

theorem det_of_mem_Tns {g : GL (Fin 2) K} (hg : g ∈ Tns b c) :
    (g : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  obtain ⟨z, hz, hgz⟩ := hg
  rw [hgz, det_Mmat, hz]

theorem isometry_of_mem_Tns {g : GL (Fin 2) K} (hg : g ∈ Tns b c) (a : Fin 2 → K) :
    minusTailForm K b c ((g : Matrix (Fin 2) (Fin 2) K).mulVec a) = minusTailForm K b c a := by
  obtain ⟨z, hz, hgz⟩ := hg
  rw [hgz, Mmat_isometry, hz, one_mul]

theorem comm_of_mem_Tns {g g' : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg' : g' ∈ Tns b c) :
    g * g' = g' * g := by
  obtain ⟨z, -, hgz⟩ := hg
  obtain ⟨w, -, hgw⟩ := hg'
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hgz, hgw, Mmat_mul, Mmat_mul, zmul_comm]

theorem eq_of_col_eq {g g' : GL (Fin 2) K} (hg : g ∈ Tns b c) (hg' : g' ∈ Tns b c)
    (h0 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = (g' : Matrix (Fin 2) (Fin 2) K) 0 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = (g' : Matrix (Fin 2) (Fin 2) K) 1 0) : g = g' := by
  obtain ⟨z, -, hgz⟩ := hg
  obtain ⟨w, -, hgw⟩ := hg'
  refine Units.ext ?_
  rw [hgz, hgw] at h0 h1 ⊢
  simp only [Mmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have : z = w := Prod.ext h0 h1
  rw [this]

@[expose] noncomputable def ofNrm (z : K × K) (hz : nrm b c z = 1) : GL (Fin 2) K :=
  ⟨Mmat b c z, Mmat b c (zconj b z), by rw [Mmat_mul, zmul_zconj, hz, Mmat_one],
    by rw [Mmat_mul, zmul_comm, zmul_zconj, hz, Mmat_one]⟩

theorem ofNrm_mem (z : K × K) (hz : nrm b c z = 1) : ofNrm z hz ∈ Tns b c := ⟨z, hz, rfl⟩

theorem card_Tns : Nat.card (Tns b c) = Nat.card K + 1 := by
  let f : Tns b c → {z : K × K // nrm b c z = 1} := fun g =>
    ⟨((g : GL (Fin 2) K).val 0 0, (g : GL (Fin 2) K).val 1 0), by
      obtain ⟨z, hz, hgz⟩ := g.2
      have h0 : (g : GL (Fin 2) K).val 0 0 = z.1 := by rw [hgz]; rfl
      have h1 : (g : GL (Fin 2) K).val 1 0 = z.2 := by rw [hgz]; rfl
      rw [h0, h1]
      exact hz⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro g g' h
      have h' := congrArg Subtype.val h
      simp only [f, Prod.mk.injEq] at h'
      exact Subtype.ext (eq_of_col_eq g.2 g'.2 h'.1 h'.2)
    · rintro ⟨z, hz⟩
      refine ⟨⟨ofNrm z hz, ofNrm_mem z hz⟩, Subtype.ext ?_⟩
      show (((ofNrm z hz : GL (Fin 2) K).val 0 0, (ofNrm z hz : GL (Fin 2) K).val 1 0)) = z
      exact Prod.ext rfl rfl
  have h1 := Nat.card_congr (Equiv.ofBijective f hbij)
  have h2 : Nat.card {z : K × K // nrm b c z = 1} =
      Nat.card {x : Fin 2 → K // minusTailForm K b c x = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (finTwoArrowEquiv K).symm ?_)
    intro z
    rw [finTwoArrowEquiv_symm_apply, minusTailForm_apply]
    simp [nrm]
  have hani : ∀ x : Fin 2 → K, x ≠ 0 → minusTailForm K b c x ≠ 0 := fun x hx h =>
    hx (anisotropic_minusTailForm (AnisoPair.hirr (b := b) (c := c)) x h)
  rw [h1, h2]
  exact CFSG.Timmesfeld.ClassicalOrders.card_norm_eq_one finrank_fin_two_fun hani

end Group

section Cyclic

open Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

variable (b c) in
noncomputable def qpoly : K[X] := X ^ 2 + C b * X + C c

theorem qpoly_monic : (qpoly b c).Monic := by
  unfold qpoly
  monicity!

theorem qpoly_natDegree : (qpoly b c).natDegree = 2 := by
  unfold qpoly
  compute_degree!

theorem qpoly_irreducible : Irreducible (qpoly b c) := by
  rw [qpoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [qpoly_natDegree])
    (by rw [qpoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun s hs => ?_
  rw [mem_roots qpoly_monic.ne_zero] at hs
  have h := hs.eq_zero
  simp only [qpoly, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  exact AnisoPair.hirr s h

theorem isCyclic_Tns : IsCyclic (Tns b c) := by
  have : Fact (Irreducible (qpoly b c)) := ⟨qpoly_irreducible⟩
  let ω : AdjoinRoot (qpoly b c) := AdjoinRoot.root (qpoly b c)
  have h0 : ω ^ 2 + algebraMap K (AdjoinRoot (qpoly b c)) b * ω +
      algebraMap K (AdjoinRoot (qpoly b c)) c = 0 := by
    have h : AdjoinRoot.mk (qpoly b c) (X ^ 2 + C b * X + C c) = 0 := AdjoinRoot.mk_self
    simpa only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.algebraMap_eq] using h
  have hCharF : CharP (AdjoinRoot (qpoly b c)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (qpoly b c))).injective 2
  have h2F : (2 : AdjoinRoot (qpoly b c)) = 0 := CharTwo.two_eq_zero
  have hω : ω ^ 2 = algebraMap K (AdjoinRoot (qpoly b c)) b * ω +
      algebraMap K (AdjoinRoot (qpoly b c)) c := by
    linear_combination h0 - (algebraMap K (AdjoinRoot (qpoly b c)) b * ω +
      algebraMap K (AdjoinRoot (qpoly b c)) c) * h2F
  have hli : ∀ x y : K, algebraMap K (AdjoinRoot (qpoly b c)) x +
      algebraMap K (AdjoinRoot (qpoly b c)) y * ω = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, zero_mul, add_zero] at h
      exact ⟨(map_eq_zero_iff _ (algebraMap K (AdjoinRoot (qpoly b c))).injective).1 h, rfl⟩
    · exfalso
      have hy' : algebraMap K (AdjoinRoot (qpoly b c)) y ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K (AdjoinRoot (qpoly b c))).injective).2 hy
      have hωs : ω = algebraMap K (AdjoinRoot (qpoly b c)) (-x / y) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [hωs] at h0
      have : algebraMap K (AdjoinRoot (qpoly b c)) ((-x / y) ^ 2 + b * (-x / y) + c) = 0 := by
        simpa using h0
      exact AnisoPair.hirr (-x / y)
        ((map_eq_zero_iff _ (algebraMap K (AdjoinRoot (qpoly b c))).injective).1 this)
  let φ : Tns b c →* AdjoinRoot (qpoly b c) :=
    { toFun := fun g => algebraMap K (AdjoinRoot (qpoly b c)) ((g : GL (Fin 2) K).val 0 0) +
        algebraMap K (AdjoinRoot (qpoly b c)) ((g : GL (Fin 2) K).val 1 0) * ω
      map_one' := by simp
      map_mul' := by
        intro g g'
        obtain ⟨z, -, hz⟩ := g.2
        obtain ⟨w, -, hw⟩ := g'.2
        have hp : (((g * g' : Tns b c) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            Mmat b c (zmul b c z w) := by
          rw [Subgroup.coe_mul, Units.val_mul, hz, hw, Mmat_mul]
        have e1 : (((g * g' : Tns b c) : GL (Fin 2) K)).val 0 0 = (zmul b c z w).1 := by
          rw [hp]; rfl
        have e2 : (((g * g' : Tns b c) : GL (Fin 2) K)).val 1 0 = (zmul b c z w).2 := by
          rw [hp]; rfl
        have f1 : (g : GL (Fin 2) K).val 0 0 = z.1 := by rw [hz]; rfl
        have f2 : (g : GL (Fin 2) K).val 1 0 = z.2 := by rw [hz]; rfl
        have f3 : (g' : GL (Fin 2) K).val 0 0 = w.1 := by rw [hw]; rfl
        have f4 : (g' : GL (Fin 2) K).val 1 0 = w.2 := by rw [hw]; rfl
        simp only [e1, e2, f1, f2, f3, f4, zmul, map_add, map_mul]
        linear_combination (-(algebraMap K (AdjoinRoot (qpoly b c)) z.2 *
          algebraMap K (AdjoinRoot (qpoly b c)) w.2)) * hω }
  have hinj : Function.Injective φ := by
    intro g g' h
    have h' : algebraMap K (AdjoinRoot (qpoly b c))
        ((g : GL (Fin 2) K).val 0 0 - (g' : GL (Fin 2) K).val 0 0) +
        algebraMap K (AdjoinRoot (qpoly b c))
        ((g : GL (Fin 2) K).val 1 0 - (g' : GL (Fin 2) K).val 1 0) * ω = 0 := by
      have : φ g - φ g' = 0 := sub_eq_zero.2 h
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_sub] at this ⊢
      linear_combination this
    obtain ⟨h1, h2⟩ := hli _ _ h'
    exact Subtype.ext (eq_of_col_eq g.2 g'.2 (sub_eq_zero.1 h1) (sub_eq_zero.1 h2))
  exact isCyclic_of_injective_ringHom φ hinj

end Cyclic

end CFSG.RankThree.PartOne.KF1514B
