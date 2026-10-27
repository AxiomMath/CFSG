module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

private def psuC3_mat {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (psuAlg B)ˣ) : Matrix (Fin n) (Fin n) K :=
  ((t : psuAlg B) : Matrix (Fin n) (Fin n) K)

private theorem psuC3_mat_mul {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (u v : (psuAlg B)ˣ) :
    psuC3_mat B (u * v) = psuC3_mat B u * psuC3_mat B v := by
  rw [psuC3_mat, psuC3_mat, psuC3_mat, Units.val_mul, Subalgebra.coe_mul]

private def psuC3_subHom {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    (psuAlg B)ˣ →* GL (Fin n) K :=
  Units.map (Subalgebra.val (psuAlg B)).toRingHom.toMonoidHom

private theorem psuC3_subHom_coe {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (psuAlg B)ˣ) :
    (psuC3_subHom B t : Matrix (Fin n) (Fin n) K) = psuC3_mat B t := by
  rw [psuC3_subHom, Units.coe_map]
  rfl

private theorem psuC3_mat_ne_zero {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (u : (psuAlg B)ˣ) : psuC3_mat B u ≠ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by have := S.four_le; omega⟩⟩
  exact IsUnit.ne_zero ⟨psuC3_subHom B u, psuC3_subHom_coe B u⟩

private theorem psuC3_J_mul_J (n : ℕ) (K : Type) [Field K] :
    psuJ n K * psuJ n K = (1 : Matrix (Fin n) (Fin n) K) := by
  simpa [psuJ, AutPSU.coe_gramJ] using
    (CFSG.LieType.Universal.Unitary.antidiag_mul_self (F := K) n)

private theorem psuC3_J_inv (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)⁻¹ = psuJ n K := by
  exact Matrix.inv_eq_right_inv (psuC3_J_mul_J n K)

private theorem psuC3_dag_eq {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h a = psuJ n K * (a.map h.bar)ᵀ * psuJ n K := by
  simp only [psuDag, formAdj, psuC3_J_inv]

private theorem psuC3_map_det {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) : (a.map h.bar).det = h.bar a.det := by
  exact (RingHom.map_det h.bar a).symm

private theorem psuC3_dag_det {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    (psuDag h a).det = h.bar a.det := by
  have hJ : (psuJ n K).det * (psuJ n K).det = 1 := by
    rw [← Matrix.det_mul, psuC3_J_mul_J, Matrix.det_one]
  rw [psuC3_dag_eq h a, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    psuC3_map_det h a]
  calc (psuJ n K).det * h.bar a.det * (psuJ n K).det
      = h.bar a.det * ((psuJ n K).det * (psuJ n K).det) := by ring
    _ = h.bar a.det := by rw [hJ, mul_one]

private theorem psuC3_det_theta {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) :
    (psuTheta h X a).det = h.bar a.det := by
  have hXX : (X : Matrix (Fin n) (Fin n) K) *
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet := congrArg Matrix.det hXX
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hXinv : (((X⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).det =
      ((X : Matrix (Fin n) (Fin n) K).det)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hdet).symm
  rw [psuTheta, Matrix.det_mul, Matrix.det_mul, hXinv, psuC3_map_det h a]
  have hd : (X : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    simpa using (Matrix.GeneralLinearGroup.det X).ne_zero
  rw [mul_assoc, mul_comm (h.bar a.det) ((X : Matrix (Fin n) (Fin n) K).det)⁻¹,
    ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem psuC3_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hgen : ∀ a ∈ psuAlg B, a * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * a := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => x * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * x) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rfl
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · intro x y hx hy hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro x y hx hy hpx hpy
      rw [Matrix.mul_assoc x y (B : Matrix (Fin n) (Fin n) K), hpy,
        ← Matrix.mul_assoc x (B : Matrix (Fin n) (Fin n) K) y, hpx,
        Matrix.mul_assoc (B : Matrix (Fin n) (Fin n) K) x y]
  intro a ha b hb
  refine Algebra.adjoin_induction (p := fun x _ => a * x = x * a) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hgen a ha
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc a x y, hpx, Matrix.mul_assoc x a y, hpy,
      ← Matrix.mul_assoc x y a]

private noncomputable def psuC3_psiMonoid {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    (psuAlg B) →* (psuAlg B) where
  toFun a := ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
    (psuGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2).2⟩
  map_one' := by
    apply Subtype.ext
    show psuPsi h X (((1 : psuAlg B) : Matrix (Fin n) (Fin n) K)) =
      (1 : Matrix (Fin n) (Fin n) K)
    rw [Subalgebra.coe_one, psuPsi_one]
  map_mul' := by
    intro a b
    apply Subtype.ext
    show psuPsi h X (((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K)) =
      psuPsi h X ((a : Matrix (Fin n) (Fin n) K)) *
        psuPsi h X ((b : Matrix (Fin n) (Fin n) K))
    rw [Subalgebra.coe_mul, psuPsi_mul]
    exact psuC3_comm B _ (psuGraph_star_mem S _ b.2).2 _
      (psuGraph_star_mem S _ a.2).2

private noncomputable def psuC3_psiUnit {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    (psuAlg B)ˣ →* (psuAlg B)ˣ :=
  Units.map (psuC3_psiMonoid S)

private def psuC3_F1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    Subgroup (psuAlg B)ˣ where
  carrier := {t | psuDag h (psuC3_mat B t) * psuC3_mat B t = 1}
  mul_mem' := by
    rintro t u ht hu
    show psuDag h (psuC3_mat B (t * u)) * psuC3_mat B (t * u) = 1
    rw [psuC3_mat_mul, psuDag_mul]
    calc (psuDag h (psuC3_mat B u) * psuDag h (psuC3_mat B t)) *
          (psuC3_mat B t * psuC3_mat B u)
        = psuDag h (psuC3_mat B u) *
            (psuDag h (psuC3_mat B t) * psuC3_mat B t) * psuC3_mat B u := by
          noncomm_ring
      _ = psuDag h (psuC3_mat B u) * 1 * psuC3_mat B u := by rw [ht]
      _ = psuDag h (psuC3_mat B u) * psuC3_mat B u := by rw [Matrix.mul_one]
      _ = 1 := hu
  one_mem' := by
    change psuDag h (psuC3_mat B (1 : (psuAlg B)ˣ)) * psuC3_mat B (1 : (psuAlg B)ˣ) = 1
    rw [show psuC3_mat B (1 : (psuAlg B)ˣ) = 1 by
      rw [psuC3_mat, Units.val_one, Subalgebra.coe_one]]
    rw [psuDag_one, Matrix.one_mul]
  inv_mem' := by
    rintro t ht
    have htmem : psuC3_mat B t ∈ psuAlg B := (t : psuAlg B).2
    have hdmem : psuDag h (psuC3_mat B t) ∈ psuAlg B :=
      (psuGraph_star_mem S _ htmem).1
    have hpt : psuC3_mat B t * psuDag h (psuC3_mat B t) = 1 := by
      rw [psuC3_comm B _ htmem _ hdmem]
      exact ht
    have hti : (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) *
        psuC3_mat B t = 1 := by
      rw [psuC3_mat, ← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Subalgebra.coe_one]
    have hinv : (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) =
        psuDag h (psuC3_mat B t) := by
      calc (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K)
          = (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) * 1 :=
            (Matrix.mul_one _).symm
        _ = (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) *
              (psuC3_mat B t * psuDag h (psuC3_mat B t)) := by rw [hpt]
        _ = ((((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) *
              psuC3_mat B t) * psuDag h (psuC3_mat B t) := by rw [Matrix.mul_assoc]
        _ = 1 * psuDag h (psuC3_mat B t) := by rw [hti]
        _ = psuDag h (psuC3_mat B t) := Matrix.one_mul _
    change psuDag h (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) *
      (((t⁻¹ : (psuAlg B)ˣ) : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1
    rw [hinv, psuDag_dag]
    exact hpt

private noncomputable def psuC3_det {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    psuC3_F1 S →* Kˣ :=
  (Matrix.GeneralLinearGroup.det).comp ((psuC3_subHom B).comp (psuC3_F1 S).subtype)

private theorem psuC3_det_apply {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuC3_F1 S) :
    (psuC3_det S t : K) = (psuC3_mat B (t : (psuAlg B)ˣ)).det := by
  rw [psuC3_det, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change ((psuC3_subHom B (t : (psuAlg B)ˣ) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = (psuC3_mat B (t : (psuAlg B)ˣ)).det
  rw [psuC3_subHom_coe]

private theorem psuC3_det_eq_one {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) :
    (psuC3_mat B (t : psuC3_F1 S)).det = 1 := by
  have h : (psuC3_det S (t : psuC3_F1 S) : K) = 1 :=
    congrArg (fun z : Kˣ => (z : K)) (MonoidHom.mem_ker.mp t.2)
  rwa [psuC3_det_apply] at h

private theorem psuC3_det_pow {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuC3_F1 S) :
    psuC3_det S t ^ (2 ^ f + 1) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have hun : psuDag h (psuC3_mat B (t : (psuAlg B)ˣ)) * psuC3_mat B (t : (psuAlg B)ˣ) = 1 :=
    t.2
  have hdet := congrArg Matrix.det hun
  rw [Matrix.det_mul, Matrix.det_one, psuC3_dag_det,
    UnitaryFieldData.bar_apply] at hdet
  rw [psuC3_det_apply, pow_succ]
  exact hdet

private theorem psuC3_units_mul_comm {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (u v : (psuAlg B)ˣ) : u * v = v * u := by
  apply Units.ext
  apply Subtype.ext
  exact psuC3_comm B (u : psuAlg B) (u : psuAlg B).2 (v : psuAlg B) (v : psuAlg B).2

private theorem psuC3_mul_mul_mul_comm {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (a b c d : (psuAlg B)ˣ) : (a * b) * (c * d) = (a * c) * (b * d) := by
  calc (a * b) * (c * d) = a * (b * (c * d)) := mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := congrArg (fun z => a * z) (mul_assoc b c d).symm
    _ = a * ((c * b) * d) := congrArg (fun z => a * (z * d)) (psuC3_units_mul_comm b c)
    _ = a * (c * (b * d)) := congrArg (fun z => a * z) (mul_assoc c b d)
    _ = (a * c) * (b * d) := (mul_assoc a c (b * d)).symm

private noncomputable def psuC3_N {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    psuC3_F1 S →* (psuAlg B)ˣ :=
  MonoidHom.mk' (fun t => psuC3_psiUnit S (t : (psuAlg B)ˣ) * (t : (psuAlg B)ˣ)) (by
    intro a b
    rw [Subgroup.coe_mul, map_mul]
    exact psuC3_mul_mul_mul_comm _ _ _ _)

private theorem psuC3_N_apply {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuC3_F1 S) :
    psuC3_N S t = psuC3_psiUnit S (t : (psuAlg B)ˣ) * (t : (psuAlg B)ˣ) :=
  rfl

private theorem psuC3_N_coe {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuC3_F1 S) :
    ((psuC3_N S t : (psuAlg B)ˣ) : Matrix (Fin n) (Fin n) K) =
      psuPsi h X (psuC3_mat B (t : (psuAlg B)ˣ)) * psuC3_mat B (t : (psuAlg B)ˣ) := by
  rw [psuC3_N_apply, Units.val_mul, Subalgebra.coe_mul]
  congr 1

private theorem psuC3_scalar_unique {n : ℕ} {K : Type} [Field K]
    {d d' : Kˣ} {a : Matrix (Fin n) (Fin n) K} (ha : a ≠ 0)
    (h : (d : K) • a = (d' : K) • a) : d = d' := by
  have h0 : ((d : K) - (d' : K)) = 0 := by
    have h1 : ((d : K) - (d' : K)) • a = 0 := by
      rw [sub_smul, h, sub_self]
    rcases (smul_eq_zero.mp h1) with h2 | h2
    · exact h2
    · exact absurd h2 ha
  exact Units.ext (sub_eq_zero.mp h0)

private noncomputable def psuC3_toXJ {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (t : (psuAlg B)ˣ)
    (hun : psuDag h (psuC3_mat B t) * psuC3_mat B t = 1)
    (hdet : (psuC3_mat B t).det = 1) : AutPSU.XJ h n :=
  ⟨psuC3_subHom B t, by
    rw [AutPSU.XJ, mem_gramSU]
    refine ⟨?_, ?_⟩
    · have h1 : psuDag h (psuC3_mat B t) =
          psuJ n K * ((psuC3_mat B t).map h.bar)ᵀ * psuJ n K := psuC3_dag_eq h _
      have h2 : psuJ n K * ((psuC3_mat B t).map h.bar)ᵀ * psuJ n K * psuC3_mat B t = 1 := by
        rw [← h1]; exact hun
      have h4 : psuJ n K * (psuJ n K * ((psuC3_mat B t).map h.bar)ᵀ * psuJ n K *
          psuC3_mat B t) = psuJ n K := by rw [h2, Matrix.mul_one]
      have h5 : psuJ n K * (psuJ n K * ((psuC3_mat B t).map h.bar)ᵀ * psuJ n K *
          psuC3_mat B t) =
          (psuJ n K * psuJ n K) * (((psuC3_mat B t).map h.bar)ᵀ * psuJ n K *
            psuC3_mat B t) := by noncomm_ring
      rw [h5, psuC3_J_mul_J, Matrix.one_mul] at h4
      show ((↑(psuC3_subHom B t) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
          (↑(psuC3_subHom B t) : Matrix (Fin n) (Fin n) K) = psuJ n K
      rw [psuC3_subHom_coe]
      exact h4
    · rw [psuC3_subHom_coe]; exact hdet⟩

private theorem psuC3_mem_chat {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (t : (psuAlg B)ˣ)
    (hun : psuDag h (psuC3_mat B t) * psuC3_mat B t = 1)
    (hdet : (psuC3_mat B t).det = 1) :
    psuC3_toXJ (h := h) (B := B) t hun hdet ∈ psuChat h B := by
  refine ⟨1, ?_⟩
  change ((t : psuAlg B) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
    (1 : K) • ((B : Matrix (Fin n) (Fin n) K) * ((t : psuAlg B) : Matrix (Fin n) (Fin n) K))
  rw [psuC3_comm B _ (t : psuAlg B).2 _ (Algebra.subset_adjoin ⟨B, rfl, rfl⟩), one_smul]

private theorem psuC3_theta_exists {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) :
    ∃ d : Kˣ, psuTheta h X (psuC3_mat B (t : psuC3_F1 S)) =
      (d : K) • psuC3_mat B (t : psuC3_F1 S) := by
  have hun : psuDag h (psuC3_mat B (t : psuC3_F1 S)) * psuC3_mat B (t : psuC3_F1 S) = 1 :=
    (t : psuC3_F1 S).2
  have hdet : (psuC3_mat B (t : psuC3_F1 S)).det = 1 := psuC3_det_eq_one S t
  obtain ⟨d, hd⟩ := S.fix (psuC3_toXJ (h := h) (B := B) (t : psuC3_F1 S) hun hdet)
    (psuC3_mem_chat (h := h) (B := B) (t : psuC3_F1 S) hun hdet)
  refine ⟨d, ?_⟩
  have hx : ((psuC3_toXJ (h := h) (B := B) (t : psuC3_F1 S) hun hdet : AutPSU.XJ h n) : GL (Fin n) K) =
      psuC3_subHom B (t : (psuAlg B)ˣ) := rfl
  rw [hx, psuC3_subHom_coe] at hd
  exact hd

private noncomputable def psuC3_cFun {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) : Kˣ :=
  Classical.choose (psuC3_theta_exists S t)

private theorem psuC3_cFun_spec {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) :
    psuTheta h X (psuC3_mat B (t : psuC3_F1 S)) =
      (psuC3_cFun S t : K) • psuC3_mat B (t : psuC3_F1 S) :=
  Classical.choose_spec (psuC3_theta_exists S t)

private theorem psuC3_cFun_mul {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a b : (psuC3_det S).ker) :
    psuC3_cFun S (a * b) = psuC3_cFun S a * psuC3_cFun S b := by
  have ha := psuC3_cFun_spec S a
  have hb := psuC3_cFun_spec S b
  have hab := psuC3_cFun_spec S (a * b)
  have hmat : psuC3_mat B ((a * b : (psuC3_det S).ker) : psuC3_F1 S) =
      psuC3_mat B (a : psuC3_F1 S) * psuC3_mat B (b : psuC3_F1 S) := by
    change psuC3_mat B ((a : (psuAlg B)ˣ) * (b : (psuAlg B)ˣ)) = _
    rw [psuC3_mat_mul]
  rw [hmat] at hab
  have hne : psuC3_mat B (a : psuC3_F1 S) * psuC3_mat B (b : psuC3_F1 S) ≠ 0 := by
    rw [← psuC3_mat_mul]
    exact psuC3_mat_ne_zero S ((a : psuC3_F1 S) * (b : psuC3_F1 S))
  refine psuC3_scalar_unique hne ?_
  rw [← hab, psuTheta_mul, ha, hb, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul]

private noncomputable def psuC3_c {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    (psuC3_det S).ker →* Kˣ :=
  MonoidHom.mk' (psuC3_cFun S) (psuC3_cFun_mul S)

private theorem psuC3_c_pow_n {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) :
    psuC3_c S t ^ n = 1 := by
  have hspec := psuC3_cFun_spec S t
  have hdet : (psuC3_mat B (t : psuC3_F1 S)).det = 1 := psuC3_det_eq_one S t
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (psuC3_cFun S t : K) ^ n = 1
  have h := congrArg Matrix.det hspec
  rw [psuC3_det_theta, Matrix.det_smul, hdet, mul_one, map_one,
    Fintype.card_fin] at h
  exact h.symm

private theorem psuC3_c_pow_q1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) :
    psuC3_c S t ^ (2 ^ f + 1) = 1 := by
  have hspec := psuC3_cFun_spec S t
  have hun : psuDag h (psuC3_mat B (t : psuC3_F1 S)) * psuC3_mat B (t : psuC3_F1 S) = 1 :=
    (t : psuC3_F1 S).2
  have h1 : psuDag h (psuTheta h X (psuC3_mat B (t : psuC3_F1 S))) *
      psuTheta h X (psuC3_mat B (t : psuC3_F1 S)) = 1 := by
    rw [← psuTheta_dag h X S.X_mem S.X_sq, ← psuTheta_mul, hun, psuTheta_one]
  rw [hspec, psuDag_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hun] at h1
  have h3 : h.bar (psuC3_cFun S t : K) * (psuC3_cFun S t : K) = 1 := by
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      M ⟨0, by have := S.four_le; omega⟩ ⟨0, by have := S.four_le; omega⟩) h1
    simpa using h4
  rw [UnitaryFieldData.bar_apply] at h3
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (psuC3_cFun S t : K) ^ (2 ^ f + 1) = 1
  rw [pow_succ]
  exact h3

private theorem psuC3_ker {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : (psuC3_det S).ker) (ht : psuC3_c S t = 1) :
    psuC3_N S (t : psuC3_F1 S) = 1 := by
  have hspec := psuC3_cFun_spec S t
  rw [show psuC3_cFun S t = 1 from ht] at hspec
  rw [show (↑(1 : Kˣ) : K) = 1 from rfl, one_smul] at hspec
  apply Units.ext
  apply Subtype.ext
  rw [psuC3_N_coe, Units.val_one, Subalgebra.coe_one]
  have hpsi : psuPsi h X (psuC3_mat B (t : psuC3_F1 S)) =
      psuDag h (psuC3_mat B (t : psuC3_F1 S)) := by
    rw [psuPsi, psuTheta_dag h X S.X_mem S.X_sq, hspec]
  rw [hpsi, (t : psuC3_F1 S).2]

private noncomputable def psuC3_unitOfUnitary {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (t : Matrix (Fin n) (Fin n) K)
    (ht : t ∈ psuUnitaryPart h B) : (psuAlg B)ˣ :=
  Units.mk ⟨t, ht.1⟩ ⟨psuDag h t, (psuGraph_star_mem S t ht.1).1⟩
    (by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_one]
      exact (psuC3_comm B t ht.1 (psuDag h t) (psuGraph_star_mem S t ht.1).1).trans ht.2)
    (by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_one]
      exact ht.2)

private theorem psuC3_unitOfUnitary_mem {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (t : Matrix (Fin n) (Fin n) K)
    (ht : t ∈ psuUnitaryPart h B) :
    psuC3_unitOfUnitary S t ht ∈ psuC3_F1 S := by
  show psuDag h (psuC3_mat B (psuC3_unitOfUnitary S t ht)) *
      psuC3_mat B (psuC3_unitOfUnitary S t ht) = 1
  rw [show psuC3_mat B (psuC3_unitOfUnitary S t ht) = t from rfl]
  exact ht.2

private theorem psuC3_unitOfUnitary_N_coe {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (t : Matrix (Fin n) (Fin n) K)
    (ht : t ∈ psuUnitaryPart h B) :
    ((psuC3_N S ⟨psuC3_unitOfUnitary S t ht, psuC3_unitOfUnitary_mem S t ht⟩ :
        (psuAlg B)ˣ) : Matrix (Fin n) (Fin n) K) = psuPsi h X t * t := by
  rw [psuC3_N_coe]
  rfl

private theorem psuC3_normImage_le_range {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    Nat.card (psuNormImage h X B) ≤ Nat.card (psuC3_N S).range := by
  classical
  have hinj : Function.Injective (fun m : ↥(psuNormImage h X B) =>
      (⟨psuC3_N S ⟨psuC3_unitOfUnitary S (Classical.choose m.2)
            (Classical.choose_spec m.2).1,
          psuC3_unitOfUnitary_mem S (Classical.choose m.2) (Classical.choose_spec m.2).1⟩,
        ⟨_, rfl⟩⟩ : ↥((psuC3_N S).range))) := by
    intro m m' hm
    apply Subtype.ext
    have h2 : ((psuC3_N S ⟨psuC3_unitOfUnitary S (Classical.choose m.2)
          (Classical.choose_spec m.2).1,
          psuC3_unitOfUnitary_mem S (Classical.choose m.2)
            (Classical.choose_spec m.2).1⟩ : (psuAlg B)ˣ) :
          Matrix (Fin n) (Fin n) K) =
        ((psuC3_N S ⟨psuC3_unitOfUnitary S (Classical.choose m'.2)
          (Classical.choose_spec m'.2).1,
          psuC3_unitOfUnitary_mem S (Classical.choose m'.2)
            (Classical.choose_spec m'.2).1⟩ : (psuAlg B)ˣ) :
          Matrix (Fin n) (Fin n) K) :=
      congrArg (fun z : (psuAlg B)ˣ => ((z : psuAlg B) : Matrix (Fin n) (Fin n) K))
        (congrArg Subtype.val hm)
    rw [psuC3_unitOfUnitary_N_coe, psuC3_unitOfUnitary_N_coe] at h2
    calc (m : Matrix (Fin n) (Fin n) K)
        = psuPsi h X (Classical.choose m.2 : Matrix (Fin n) (Fin n) K) *
            (Classical.choose m.2 : Matrix (Fin n) (Fin n) K) :=
          (Classical.choose_spec m.2).2
      _ = psuPsi h X (Classical.choose m'.2 : Matrix (Fin n) (Fin n) K) *
            (Classical.choose m'.2 : Matrix (Fin n) (Fin n) K) := h2
      _ = (m' : Matrix (Fin n) (Fin n) K) := (Classical.choose_spec m'.2).2.symm
  exact Nat.card_le_card_of_injective _ hinj

private theorem psuC3_card_le_of_pow_eq_one {K : Type} [Field K]
    (m : ℕ) [NeZero m] (C : Subgroup Kˣ)
    (hC : ∀ x ∈ C, x ^ m = 1) : Nat.card C ≤ m := by
  have hle : C ≤ rootsOfUnity m K := fun x hx => (mem_rootsOfUnity m x).mpr (hC x hx)
  exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity K m)

private theorem psuC3_count {A A' C D : Type} [Group A] [Group A'] [Group C] [Group D]
    [Finite A]
    (N : A →* A') (δ : A →* C) (c : δ.ker →* D)
    (h : ∀ t : δ.ker, c t = 1 → N (t : A) = 1) :
    Nat.card N.range ≤ Nat.card δ.range * Nat.card c.range := by
  have hN := Subgroup.card_ker_mul_card_range N
  have hδ := Subgroup.card_ker_mul_card_range δ
  have hc := Subgroup.card_ker_mul_card_range c
  have hinj : Function.Injective (fun t : c.ker =>
      (⟨(t : δ.ker), h (t : δ.ker) (MonoidHom.mem_ker.mp t.2)⟩ : N.ker)) := by
    intro a b hab
    have h1 : ((a : δ.ker) : A) = ((b : δ.ker) : A) :=
      congrArg (fun z : N.ker => (z : A)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcard : Nat.card c.ker ≤ Nat.card N.ker :=
    Nat.card_le_card_of_injective _ hinj
  have h1 : Nat.card N.range * Nat.card N.ker = Nat.card δ.ker * Nat.card δ.range := by
    rw [mul_comm (Nat.card N.range) (Nat.card N.ker), hN, hδ]
  have h2 : Nat.card δ.ker * Nat.card δ.range =
      (Nat.card c.ker * Nat.card c.range) * Nat.card δ.range := by rw [hc]
  have h3 : (Nat.card c.ker * Nat.card c.range) * Nat.card δ.range ≤
      (Nat.card N.ker * Nat.card c.range) * Nat.card δ.range :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard)
  have h4 : (Nat.card N.ker * Nat.card c.range) * Nat.card δ.range =
      Nat.card N.ker * (Nat.card c.range * Nat.card δ.range) := by ring
  have h5 : Nat.card N.range * Nat.card N.ker ≤
      Nat.card N.ker * (Nat.card c.range * Nat.card δ.range) := by
    rw [h1, h2]; exact h3.trans (le_of_eq h4)
  rw [mul_comm (Nat.card N.range) (Nat.card N.ker)] at h5
  haveI : Nonempty N.ker := ⟨1⟩
  have h6 : Nat.card N.range ≤ Nat.card c.range * Nat.card δ.range :=
    Nat.le_of_mul_le_mul_left h5 Nat.card_pos
  rwa [mul_comm] at h6

theorem psuGraph_torus_bound {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    Nat.card (psuNormImage h X B) ≤ (2 ^ f + 1) * Nat.gcd n (2 ^ f + 1) := by
  classical
  haveI : NeZero (2 ^ f + 1) := ⟨Nat.succ_ne_zero _⟩
  haveI : NeZero (Nat.gcd n (2 ^ f + 1)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_right n (Nat.succ_pos _))⟩
  have hcount := psuC3_count (psuC3_N S) (psuC3_det S) (psuC3_c S) (psuC3_ker S)
  have hdetle : Nat.card (psuC3_det S).range ≤ 2 ^ f + 1 := by
    refine psuC3_card_le_of_pow_eq_one (2 ^ f + 1) _ ?_
    rintro x ⟨t, rfl⟩
    exact psuC3_det_pow S t
  have hcle : Nat.card (psuC3_c S).range ≤ Nat.gcd n (2 ^ f + 1) := by
    refine psuC3_card_le_of_pow_eq_one (Nat.gcd n (2 ^ f + 1)) _ ?_
    rintro x ⟨t, rfl⟩
    exact pow_gcd_eq_one.mpr ⟨psuC3_c_pow_n S t, psuC3_c_pow_q1 S t⟩
  calc Nat.card (psuNormImage h X B)
      ≤ Nat.card (psuC3_N S).range := psuC3_normImage_le_range S
    _ ≤ Nat.card (psuC3_det S).range * Nat.card (psuC3_c S).range := hcount
    _ ≤ (2 ^ f + 1) * Nat.gcd n (2 ^ f + 1) := Nat.mul_le_mul hdetle hcle

end CFSG.StandardType
