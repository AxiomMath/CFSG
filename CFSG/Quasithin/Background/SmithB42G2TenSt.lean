module

public import CFSG.Quasithin.Background.SmithB42G2TenLie

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8
open scoped Kronecker

variable {F : Type} [Field F]

@[expose] def ι3f (w : Ix3 × LIdx → F) : Ix3 × (Ix3 × Ix3) → F :=
  ((1 : Matrix Ix3 Ix3 F) ⊗ₖ secL F).mulVec w

theorem ι3f_apply (w : Ix3 × LIdx → F) (a : Ix3) (q : Ix3 × Ix3) :
    ι3f w (a, q) = ∑ p, secL F q p * w (a, p) := by
  simp only [ι3f, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

theorem ι3f_lP (w : Ix3 × LIdx → F) (a : Ix3) (p : LIdx) : ι3f w (a, lP p) = w (a, p) := by
  rw [ι3f_apply]
  simp only [secL_apply, secB_coord, decide_eq_true_eq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem ι3f_lP_swap (w : Ix3 × LIdx → F) (a : Ix3) (p : LIdx) :
    ι3f w (a, (lP p).swap) = w (a, p) := by
  rw [← ι3f_lP w a p, ι3f_apply, ι3f_apply]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [secL_apply, secL_apply, secB_swap]

theorem ι3f_u2v2 (w : Ix3 × LIdx → F) (a : Ix3) :
    ι3f w (a, (.inl 2, .inr 2)) = w (a, 2) + w (a, 7) := by
  rw [ι3f_apply]
  have h : ∀ p : LIdx, secB (.inl 2, .inr 2) p = (decide (p = 2) || decide (p = 7)) := by decide
  simp only [secL_apply, h, Bool.or_eq_true, decide_eq_true_eq, ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ]

theorem ι3f_v2u2 (w : Ix3 × LIdx → F) (a : Ix3) :
    ι3f w (a, (.inr 2, .inl 2)) = w (a, 2) + w (a, 7) := by
  rw [← ι3f_u2v2, ι3f_apply, ι3f_apply]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [secL_apply, secL_apply, ← secB_swap]
  rfl

theorem ι3f_symm (w : Ix3 × LIdx → F) (a b c : Ix3) : ι3f w (a, (b, c)) = ι3f w (a, (c, b)) := by
  rw [ι3f_apply, ι3f_apply]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [secL_apply, secL_apply, ← secB_swap]
  rfl

theorem ι3f_diag (w : Ix3 × LIdx → F) (a b : Ix3) : ι3f w (a, (b, b)) = 0 := by
  rw [ι3f_apply]
  refine Finset.sum_eq_zero fun p' _ => ?_
  rw [secL_apply, secB_diag]
  simp

@[expose] def cycE : Ix3 × (Ix3 × Ix3) ≃ Ix3 × (Ix3 × Ix3) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def cycL : (Ix3 × (Ix3 × Ix3) → F) →ₗ[F] (Ix3 × (Ix3 × Ix3) → F) where
  toFun T x := T x + T (cycE x) + T (cycE (cycE x))
  map_add' T T' := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c T := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem cycL_apply (T : Ix3 × (Ix3 × Ix3) → F) (i j k : Ix3) :
    cycL T (i, (j, k)) = T (i, (j, k)) + T (j, (k, i)) + T (k, (i, j)) := rfl

@[expose] def wedgeL : (Ix3 × LIdx → F) →ₗ[F] (Ix3 × (Ix3 × Ix3) → F) :=
  cycL ∘ₗ Matrix.mulVecLin ((1 : Matrix Ix3 Ix3 F) ⊗ₖ secL F)

theorem wedgeL_eq (w : Ix3 × LIdx → F) : wedgeL w = cycL (ι3f w) := by
  rw [wedgeL, LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rfl

theorem wedgeL_apply (w : Ix3 × LIdx → F) (i j k : Ix3) :
    wedgeL w (i, (j, k)) = ι3f w (i, (j, k)) + ι3f w (j, (k, i)) + ι3f w (k, (i, j)) := by
  rw [wedgeL_eq, cycL_apply]

@[expose] def stSub (F : Type) [Field F] : Submodule F (Ix3 × LIdx → F) :=
  LinearMap.ker (wedgeL (F := F))

theorem mem_stSub {w : Ix3 × LIdx → F} :
    w ∈ stSub F ↔ ∀ i j k : Ix3, ι3f w (i, (j, k)) + ι3f w (j, (k, i)) + ι3f w (k, (i, j)) = 0 := by
  rw [stSub, LinearMap.mem_ker]
  refine ⟨fun h i j k => ?_, fun h => funext fun x => ?_⟩
  · rw [← wedgeL_apply, h, Pi.zero_apply]
  · obtain ⟨i, j, k⟩ := x
    rw [wedgeL_apply, h, Pi.zero_apply]

theorem alt3_eq_zero {A : Ix3 → Ix3 → Ix3 → F} (h23 : ∀ i j k, A i j k = A i k j)
    (hcyc : ∀ i j k, A i j k = A j k i) (hdiag : ∀ i j, A i j j = 0)
    (hs : ∀ i j k, rk i < rk j → rk j < rk k → A i j k = 0) (i j k : Ix3) : A i j k = 0 := by
  rcases lt_trichotomy (rk i) (rk j) with h1 | h1 | h1 <;>
    rcases lt_trichotomy (rk j) (rk k) with h2 | h2 | h2 <;>
    rcases lt_trichotomy (rk i) (rk k) with h3 | h3 | h3
  all_goals first
    | omega
    | exact hs i j k h1 h2
    | (rw [h23]; exact hs i k j h3 (by omega))
    | (rw [hcyc, h23]; exact hs j i k h1 h3)
    | (rw [hcyc]; exact hs j k i h2 (by omega))
    | (rw [hcyc, hcyc]; exact hs k i j h3 h1)
    | (rw [hcyc, hcyc, h23]; exact hs k j i h2 h1)
    | (have := rk_injective h2; subst this; exact hdiag i j)
    | (have := rk_injective h1; subst this; rw [h23, hcyc]; exact hdiag k i)
    | (have := rk_injective h3; subst this; rw [hcyc]; exact hdiag j i)

variable [CharP F 2]

theorem wedgeL_alt (w : Ix3 × LIdx → F) :
    (∀ i j k, wedgeL w (i, (j, k)) = wedgeL w (i, (k, j))) ∧
      (∀ i j k, wedgeL w (i, (j, k)) = wedgeL w (j, (k, i))) ∧
      ∀ i j, wedgeL w (i, (j, j)) = 0 := by
  refine ⟨fun i j k => ?_, fun i j k => ?_, fun i j => ?_⟩
  · rw [wedgeL_apply, wedgeL_apply, ι3f_symm w i j k, ι3f_symm w j k i, ι3f_symm w k i j]
    ring
  · rw [wedgeL_apply, wedgeL_apply]
    ring
  · rw [wedgeL_apply, ι3f_diag, ι3f_symm w j j i, zero_add, CharTwo.add_self_eq_zero]

abbrev Trip : Type := {x : Ix3 × (Ix3 × Ix3) // rk x.1 < rk x.2.1 ∧ rk x.2.1 < rk x.2.2}

theorem card_Trip : Fintype.card Trip = 20 := by decide

@[expose] def wedge20 : (Ix3 × LIdx → F) →ₗ[F] (Trip → F) :=
  (LinearMap.pi fun t : Trip => LinearMap.proj t.1) ∘ₗ wedgeL

theorem ker_wedge20_le : LinearMap.ker (wedge20 (F := F)) ≤ stSub F := by
  intro w hw
  rw [LinearMap.mem_ker] at hw
  have hA := wedgeL_alt w
  refine LinearMap.mem_ker.mpr (funext fun x => ?_)
  obtain ⟨i, j, k⟩ := x
  refine alt3_eq_zero (A := fun i j k => wedgeL w (i, (j, k))) hA.1 hA.2.1 hA.2.2
    (fun i j k hij hjk => ?_) i j k
  have := congrFun hw ⟨(i, (j, k)), hij, hjk⟩
  simpa [wedge20] using this

@[expose] def repQL : ↥(cayleyGroup F) →* Matrix (Ix3 × LIdx) (Ix3 × LIdx) F :=
  kron2Rep repQ repLie

@[expose] def rep3 : ↥(cayleyGroup F) →* Matrix (Ix3 × (Ix3 × Ix3)) (Ix3 × (Ix3 × Ix3)) F :=
  kron2Rep repQ rep2

theorem ι3f_repQL (g : ↥(cayleyGroup F)) (w : Ix3 × LIdx → F) :
    ι3f ((repQL g).mulVec w) = (rep3 g).mulVec (ι3f w) := by
  simp only [ι3f, repQL, rep3, kron2Rep_apply, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  rw [show secL F * repLie g = rep2 g * secL F from sec_mul_pivotRep isPivot_lie g]

theorem rep3_comp_cycE (g : ↥(cayleyGroup F)) (T : Ix3 × (Ix3 × Ix3) → F) :
    (rep3 g).mulVec (fun x => T (cycE x)) = fun x => (rep3 g).mulVec T (cycE x) := by
  funext x
  simp only [Matrix.mulVec, dotProduct]
  refine Fintype.sum_equiv cycE _ _ fun y => ?_
  obtain ⟨i, j, k⟩ := x
  obtain ⟨a, b, c⟩ := y
  simp only [rep3, rep2, kron2Rep_apply, Matrix.kroneckerMap_apply, cycE, Equiv.coe_fn_mk]
  ring

theorem cycL_rep3 (g : ↥(cayleyGroup F)) (T : Ix3 × (Ix3 × Ix3) → F) :
    cycL ((rep3 g).mulVec T) = (rep3 g).mulVec (cycL T) := by
  have e : cycL T = T + (fun x => T (cycE x)) + fun x => T (cycE (cycE x)) := rfl
  rw [e, Matrix.mulVec_add, Matrix.mulVec_add, rep3_comp_cycE, rep3_comp_cycE g (fun x => T _),
    rep3_comp_cycE]
  rfl

theorem repQL_mem_stSub (g : ↥(cayleyGroup F)) {w : Ix3 × LIdx → F} (hw : w ∈ stSub F) :
    (repQL g).mulVec w ∈ stSub F := by
  rw [stSub, LinearMap.mem_ker] at hw ⊢
  rw [wedgeL_eq, ι3f_repQL, cycL_rep3, ← wedgeL_eq, hw, Matrix.mulVec_zero]

@[expose] def depList : List (Ix3 × LIdx) :=
  [(.inl 1, 1), (.inl 1, 2), (.inl 0, 7), (.inl 0, 8), (.inl 2, 2), (.inl 2, 3), (.inr 2, 1),
    (.inr 1, 2), (.inl 0, 12), (.inr 1, 4), (.inl 2, 6), (.inr 1, 5), (.inr 2, 5), (.inl 1, 11),
    (.inl 1, 12), (.inr 2, 7), (.inl 2, 11), (.inl 2, 12), (.inr 2, 10), (.inr 1, 12)]

abbrev SIdx : Type := {c : Ix3 × LIdx // c ∉ depList}

theorem card_SIdx : Fintype.card SIdx = 64 := by decide

omit [CharP F 2] in
theorem eq_zero_of_sP [CharP F 2] {w : Ix3 × LIdx → F} (hw : w ∈ stSub F)
    (h0 : ∀ π : SIdx, w π.1 = 0) : w = 0 := by
  have hE := mem_stSub.mp hw
  have q0 : w (.inl 1, 1) = 0 := by
    have h := hE (.inl 0) (.inl 1) (.inl 2)
    rw [show ι3f w (.inl 0, (.inl 1, .inl 2)) = w (.inl 0, 5) from ι3f_lP w _ 5,
      show ι3f w (.inl 1, (.inl 2, .inl 0)) = w (.inl 1, 1) from ι3f_lP_swap w _ 1,
      show ι3f w (.inl 2, (.inl 0, .inl 1)) = w (.inl 2, 0) from ι3f_lP w _ 0] at h
    simp only [h0 ⟨(.inl 0, 5), by decide⟩, h0 ⟨(.inl 2, 0), by decide⟩] at h
    simpa using h
  have q1 : w (.inl 1, 2) = 0 := by
    have h := hE (.inl 0) (.inl 1) (.inr 0)
    rw [show ι3f w (.inl 0, (.inl 1, .inr 0)) = w (.inl 0, 6) from ι3f_lP w _ 6,
      show ι3f w (.inl 1, (.inr 0, .inl 0)) = w (.inl 1, 2) from ι3f_lP_swap w _ 2,
      show ι3f w (.inr 0, (.inl 0, .inl 1)) = w (.inr 0, 0) from ι3f_lP w _ 0] at h
    simp only [h0 ⟨(.inl 0, 6), by decide⟩, h0 ⟨(.inr 0, 0), by decide⟩] at h
    simpa using h
  have q2 : w (.inl 0, 7) = 0 := by
    have h := hE (.inl 0) (.inl 1) (.inr 1)
    rw [show ι3f w (.inl 0, (.inl 1, .inr 1)) = w (.inl 0, 7) from ι3f_lP w _ 7,
      show ι3f w (.inl 1, (.inr 1, .inl 0)) = w (.inl 1, 3) from ι3f_lP_swap w _ 3,
      show ι3f w (.inr 1, (.inl 0, .inl 1)) = w (.inr 1, 0) from ι3f_lP w _ 0] at h
    simp only [h0 ⟨(.inl 1, 3), by decide⟩, h0 ⟨(.inr 1, 0), by decide⟩] at h
    simpa using h
  have q3 : w (.inl 0, 8) = 0 := by
    have h := hE (.inl 0) (.inl 1) (.inr 2)
    rw [show ι3f w (.inl 0, (.inl 1, .inr 2)) = w (.inl 0, 8) from ι3f_lP w _ 8,
      show ι3f w (.inl 1, (.inr 2, .inl 0)) = w (.inl 1, 4) from ι3f_lP_swap w _ 4,
      show ι3f w (.inr 2, (.inl 0, .inl 1)) = w (.inr 2, 0) from ι3f_lP w _ 0] at h
    simp only [h0 ⟨(.inl 1, 4), by decide⟩, h0 ⟨(.inr 2, 0), by decide⟩] at h
    simpa using h
  have q4 : w (.inl 2, 2) = 0 := by
    have h := hE (.inl 0) (.inl 2) (.inr 0)
    rw [show ι3f w (.inl 0, (.inl 2, .inr 0)) = w (.inl 0, 9) from ι3f_lP w _ 9,
      show ι3f w (.inl 2, (.inr 0, .inl 0)) = w (.inl 2, 2) from ι3f_lP_swap w _ 2,
      show ι3f w (.inr 0, (.inl 0, .inl 2)) = w (.inr 0, 1) from ι3f_lP w _ 1] at h
    simp only [h0 ⟨(.inl 0, 9), by decide⟩, h0 ⟨(.inr 0, 1), by decide⟩] at h
    simpa using h
  have q5 : w (.inl 2, 3) = 0 := by
    have h := hE (.inl 0) (.inl 2) (.inr 1)
    rw [show ι3f w (.inl 0, (.inl 2, .inr 1)) = w (.inl 0, 10) from ι3f_lP w _ 10,
      show ι3f w (.inl 2, (.inr 1, .inl 0)) = w (.inl 2, 3) from ι3f_lP_swap w _ 3,
      show ι3f w (.inr 1, (.inl 0, .inl 2)) = w (.inr 1, 1) from ι3f_lP w _ 1] at h
    simp only [h0 ⟨(.inl 0, 10), by decide⟩, h0 ⟨(.inr 1, 1), by decide⟩] at h
    simpa using h
  have q6 : w (.inr 2, 1) = 0 := by
    have h := hE (.inl 0) (.inl 2) (.inr 2)
    rw [ι3f_u2v2 w (.inl 0),
      show ι3f w (.inl 2, (.inr 2, .inl 0)) = w (.inl 2, 4) from ι3f_lP_swap w _ 4,
      show ι3f w (.inr 2, (.inl 0, .inl 2)) = w (.inr 2, 1) from ι3f_lP w _ 1] at h
    simp only [h0 ⟨(.inl 0, 2), by decide⟩, q2, h0 ⟨(.inl 2, 4), by decide⟩] at h
    simpa using h
  have q7 : w (.inr 1, 2) = 0 := by
    have h := hE (.inl 0) (.inr 0) (.inr 1)
    rw [show ι3f w (.inl 0, (.inr 0, .inr 1)) = w (.inl 0, 11) from ι3f_lP w _ 11,
      show ι3f w (.inr 0, (.inr 1, .inl 0)) = w (.inr 0, 3) from ι3f_lP_swap w _ 3,
      show ι3f w (.inr 1, (.inl 0, .inr 0)) = w (.inr 1, 2) from ι3f_lP w _ 2] at h
    simp only [h0 ⟨(.inl 0, 11), by decide⟩, h0 ⟨(.inr 0, 3), by decide⟩] at h
    simpa using h
  have q8 : w (.inl 0, 12) = 0 := by
    have h := hE (.inl 0) (.inr 0) (.inr 2)
    rw [show ι3f w (.inl 0, (.inr 0, .inr 2)) = w (.inl 0, 12) from ι3f_lP w _ 12,
      show ι3f w (.inr 0, (.inr 2, .inl 0)) = w (.inr 0, 4) from ι3f_lP_swap w _ 4,
      show ι3f w (.inr 2, (.inl 0, .inr 0)) = w (.inr 2, 2) from ι3f_lP w _ 2] at h
    simp only [h0 ⟨(.inr 0, 4), by decide⟩, h0 ⟨(.inr 2, 2), by decide⟩] at h
    simpa using h
  have q9 : w (.inr 1, 4) = 0 := by
    have h := hE (.inl 0) (.inr 1) (.inr 2)
    rw [show ι3f w (.inl 0, (.inr 1, .inr 2)) = w (.inl 0, 13) from ι3f_lP w _ 13,
      show ι3f w (.inr 1, (.inr 2, .inl 0)) = w (.inr 1, 4) from ι3f_lP_swap w _ 4,
      show ι3f w (.inr 2, (.inl 0, .inr 1)) = w (.inr 2, 3) from ι3f_lP w _ 3] at h
    simp only [h0 ⟨(.inl 0, 13), by decide⟩, h0 ⟨(.inr 2, 3), by decide⟩] at h
    simpa using h
  have q10 : w (.inl 2, 6) = 0 := by
    have h := hE (.inl 1) (.inl 2) (.inr 0)
    rw [show ι3f w (.inl 1, (.inl 2, .inr 0)) = w (.inl 1, 9) from ι3f_lP w _ 9,
      show ι3f w (.inl 2, (.inr 0, .inl 1)) = w (.inl 2, 6) from ι3f_lP_swap w _ 6,
      show ι3f w (.inr 0, (.inl 1, .inl 2)) = w (.inr 0, 5) from ι3f_lP w _ 5] at h
    simp only [h0 ⟨(.inl 1, 9), by decide⟩, h0 ⟨(.inr 0, 5), by decide⟩] at h
    simpa using h
  have q11 : w (.inr 1, 5) = 0 := by
    have h := hE (.inl 1) (.inl 2) (.inr 1)
    rw [show ι3f w (.inl 1, (.inl 2, .inr 1)) = w (.inl 1, 10) from ι3f_lP w _ 10,
      show ι3f w (.inl 2, (.inr 1, .inl 1)) = w (.inl 2, 7) from ι3f_lP_swap w _ 7,
      show ι3f w (.inr 1, (.inl 1, .inl 2)) = w (.inr 1, 5) from ι3f_lP w _ 5] at h
    simp only [h0 ⟨(.inl 1, 10), by decide⟩, h0 ⟨(.inl 2, 7), by decide⟩] at h
    simpa using h
  have q12 : w (.inr 2, 5) = 0 := by
    have h := hE (.inl 1) (.inl 2) (.inr 2)
    rw [ι3f_u2v2 w (.inl 1),
      show ι3f w (.inl 2, (.inr 2, .inl 1)) = w (.inl 2, 8) from ι3f_lP_swap w _ 8,
      show ι3f w (.inr 2, (.inl 1, .inl 2)) = w (.inr 2, 5) from ι3f_lP w _ 5] at h
    simp only [q1, h0 ⟨(.inl 1, 7), by decide⟩, h0 ⟨(.inl 2, 8), by decide⟩] at h
    simpa using h
  have q13 : w (.inl 1, 11) = 0 := by
    have h := hE (.inl 1) (.inr 0) (.inr 1)
    rw [show ι3f w (.inl 1, (.inr 0, .inr 1)) = w (.inl 1, 11) from ι3f_lP w _ 11,
      show ι3f w (.inr 0, (.inr 1, .inl 1)) = w (.inr 0, 7) from ι3f_lP_swap w _ 7,
      show ι3f w (.inr 1, (.inl 1, .inr 0)) = w (.inr 1, 6) from ι3f_lP w _ 6] at h
    simp only [h0 ⟨(.inr 0, 7), by decide⟩, h0 ⟨(.inr 1, 6), by decide⟩] at h
    simpa using h
  have q14 : w (.inl 1, 12) = 0 := by
    have h := hE (.inl 1) (.inr 0) (.inr 2)
    rw [show ι3f w (.inl 1, (.inr 0, .inr 2)) = w (.inl 1, 12) from ι3f_lP w _ 12,
      show ι3f w (.inr 0, (.inr 2, .inl 1)) = w (.inr 0, 8) from ι3f_lP_swap w _ 8,
      show ι3f w (.inr 2, (.inl 1, .inr 0)) = w (.inr 2, 6) from ι3f_lP w _ 6] at h
    simp only [h0 ⟨(.inr 0, 8), by decide⟩, h0 ⟨(.inr 2, 6), by decide⟩] at h
    simpa using h
  have q15 : w (.inr 2, 7) = 0 := by
    have h := hE (.inl 1) (.inr 1) (.inr 2)
    rw [show ι3f w (.inl 1, (.inr 1, .inr 2)) = w (.inl 1, 13) from ι3f_lP w _ 13,
      show ι3f w (.inr 1, (.inr 2, .inl 1)) = w (.inr 1, 8) from ι3f_lP_swap w _ 8,
      show ι3f w (.inr 2, (.inl 1, .inr 1)) = w (.inr 2, 7) from ι3f_lP w _ 7] at h
    simp only [h0 ⟨(.inl 1, 13), by decide⟩, h0 ⟨(.inr 1, 8), by decide⟩] at h
    simpa using h
  have q16 : w (.inl 2, 11) = 0 := by
    have h := hE (.inl 2) (.inr 0) (.inr 1)
    rw [show ι3f w (.inl 2, (.inr 0, .inr 1)) = w (.inl 2, 11) from ι3f_lP w _ 11,
      show ι3f w (.inr 0, (.inr 1, .inl 2)) = w (.inr 0, 10) from ι3f_lP_swap w _ 10,
      show ι3f w (.inr 1, (.inl 2, .inr 0)) = w (.inr 1, 9) from ι3f_lP w _ 9] at h
    simp only [h0 ⟨(.inr 0, 10), by decide⟩, h0 ⟨(.inr 1, 9), by decide⟩] at h
    simpa using h
  have q17 : w (.inl 2, 12) = 0 := by
    have h := hE (.inl 2) (.inr 0) (.inr 2)
    rw [show ι3f w (.inl 2, (.inr 0, .inr 2)) = w (.inl 2, 12) from ι3f_lP w _ 12,
      ι3f_v2u2 w (.inr 0),
      show ι3f w (.inr 2, (.inl 2, .inr 0)) = w (.inr 2, 9) from ι3f_lP w _ 9] at h
    simp only [h0 ⟨(.inr 0, 2), by decide⟩, h0 ⟨(.inr 0, 7), by decide⟩,
      h0 ⟨(.inr 2, 9), by decide⟩] at h
    simpa using h
  have q18 : w (.inr 2, 10) = 0 := by
    have h := hE (.inl 2) (.inr 1) (.inr 2)
    rw [show ι3f w (.inl 2, (.inr 1, .inr 2)) = w (.inl 2, 13) from ι3f_lP w _ 13,
      ι3f_v2u2 w (.inr 1),
      show ι3f w (.inr 2, (.inl 2, .inr 1)) = w (.inr 2, 10) from ι3f_lP w _ 10] at h
    simp only [h0 ⟨(.inl 2, 13), by decide⟩, q7, h0 ⟨(.inr 1, 7), by decide⟩] at h
    simpa using h
  have q19 : w (.inr 1, 12) = 0 := by
    have h := hE (.inr 0) (.inr 1) (.inr 2)
    rw [show ι3f w (.inr 0, (.inr 1, .inr 2)) = w (.inr 0, 13) from ι3f_lP w _ 13,
      show ι3f w (.inr 1, (.inr 2, .inr 0)) = w (.inr 1, 12) from ι3f_lP_swap w _ 12,
      show ι3f w (.inr 2, (.inr 0, .inr 1)) = w (.inr 2, 11) from ι3f_lP w _ 11] at h
    simp only [h0 ⟨(.inr 0, 13), by decide⟩, h0 ⟨(.inr 2, 11), by decide⟩] at h
    simpa using h
  funext c
  by_cases hc : c ∈ depList
  · simp only [depList, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact h0 ⟨c, hc⟩

theorem finrank_stSub : Module.finrank F (stSub F) = 64 := by
  have hinj : Function.Injective (fun w : stSub F => fun π : SIdx => w.1 π.1) := by
    intro w w' h
    have := eq_zero_of_sP (w := w.1 - w'.1) (sub_mem w.2 w'.2) fun π => by
      have e := congrFun h π
      simp only at e
      rw [Pi.sub_apply, e, sub_self]
    exact Subtype.ext (sub_eq_zero.mp this)
  let r : stSub F →ₗ[F] (SIdx → F) :=
    { toFun := fun w π => w.1 π.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : Module.finrank F (stSub F) ≤ 64 := by
    have := LinearMap.finrank_le_finrank_of_injective (f := r) hinj
    rwa [Module.finrank_fintype_fun_eq_card, card_SIdx] at this
  have h1 := LinearMap.finrank_range_add_finrank_ker (wedge20 (F := F))
  have h2 : Module.finrank F (Ix3 × LIdx → F) = 84 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have h3 : Module.finrank F (LinearMap.range (wedge20 (F := F))) ≤ 20 := by
    have := Submodule.finrank_le (LinearMap.range (wedge20 (F := F)))
    rwa [Module.finrank_fintype_fun_eq_card, card_Trip] at this
  have h4 := Submodule.finrank_mono (ker_wedge20_le (F := F))
  omega

@[expose] def resSt : stSub F ≃ₗ[F] (SIdx → F) :=
  LinearEquiv.ofBijective
    { toFun := fun w π => w.1 π.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by
      have hinj : Function.Injective (fun w : stSub F => fun π : SIdx => w.1 π.1) := by
        intro w w' h
        have := eq_zero_of_sP (w := w.1 - w'.1) (sub_mem w.2 w'.2) fun π => by
          have e := congrFun h π
          simp only at e
          rw [Pi.sub_apply, e, sub_self]
        exact Subtype.ext (sub_eq_zero.mp this)
      refine ⟨hinj, ?_⟩
      refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
      rw [finrank_stSub, Module.finrank_fintype_fun_eq_card, card_SIdx])

theorem resSt_apply (w : stSub F) (π : SIdx) : resSt w π = w.1 π.1 := rfl

@[expose] def secSt (F : Type) [Field F] [CharP F 2] : Matrix (Ix3 × LIdx) SIdx F :=
  LinearMap.toMatrix' ((stSub F).subtype ∘ₗ (resSt (F := F)).symm.toLinearMap)

theorem secSt_mulVec (x : SIdx → F) :
    (secSt F).mulVec x = ((resSt (F := F)).symm x : stSub F).1 := by
  rw [secSt, LinearMap.toMatrix'_mulVec]
  rfl

theorem secSt_mulVec_mem (x : SIdx → F) : (secSt F).mulVec x ∈ stSub F := by
  rw [secSt_mulVec]
  exact Submodule.coe_mem _

theorem secSt_submatrix : (secSt F).submatrix (Subtype.val : SIdx → Ix3 × LIdx) id = 1 := by
  ext π π'
  have h := congrFun ((resSt (F := F)).apply_symm_apply (Pi.single π' 1)) π
  rw [resSt_apply, ← secSt_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [Matrix.submatrix_apply, id, Matrix.one_apply, h, Pi.single_apply]

theorem isPivot_st : IsPivot (repQL (F := F)) Subtype.val (secSt F) :=
  IsPivot.of_subspace' (stSub F) (fun g _ hw => repQL_mem_stSub g hw) secSt_mulVec_mem
    secSt_submatrix fun _ hz h0 => eq_zero_of_sP hz h0

@[expose] def repSt : ↥(cayleyGroup F) →* Matrix SIdx SIdx F := pivotRep isPivot_st

theorem repSt_mulVec (g : ↥(cayleyGroup F)) (x : SIdx → F) (π : SIdx) :
    (repSt g).mulVec x π = (repQL g).mulVec ((secSt F).mulVec x) π.1 :=
  pivotRep_mulVec isPivot_st g x π

theorem secSt_restrict {w : Ix3 × LIdx → F} (hw : w ∈ stSub F) :
    (secSt F).mulVec (fun π => w π.1) = w := by
  have h := eq_zero_of_sP (w := (secSt F).mulVec (fun π => w π.1) - w)
    (sub_mem (secSt_mulVec_mem _) hw) fun π => by
      rw [Pi.sub_apply, sec_mulVec_restrict isPivot_st, sub_self]
  exact sub_eq_zero.mp h

omit [CharP F 2] in
theorem ι3f_single (a : Ix3) (p : LIdx) (b : Ix3) (q : Ix3 × Ix3) :
    ι3f (Pi.single (a, p) (1 : F)) (b, q) = if b = a ∧ secB q p = true then 1 else 0 := by
  rw [ι3f_apply, Finset.sum_eq_single p]
  · rw [secL_apply]
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  · intro p' _ hp'
    rw [Pi.single_eq_of_ne (by simp [hp']), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CharP F 2] in
theorem ite3_eq_zero [CharP F 2] (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
    (h : (decide a ^^ decide b ^^ decide c) = false) :
    ((if a then 1 else 0 : F) + (if b then 1 else 0) + (if c then 1 else 0)) = 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    simp_all [CharTwo.add_self_eq_zero]

theorem wedge_hw_free : ∀ i j k : Ix3,
    (decide (i = .inl 0 ∧ secB (j, k) hwL = true) ^^ decide (j = .inl 0 ∧ secB (k, i) hwL = true) ^^
      decide (k = .inl 0 ∧ secB (i, j) hwL = true)) = false := by decide

theorem wedge_low_free : ∀ i j k : Ix3,
    (decide (i = .inr 0 ∧ secB (j, k) lowL = true) ^^
      decide (j = .inr 0 ∧ secB (k, i) lowL = true) ^^
      decide (k = .inr 0 ∧ secB (i, j) lowL = true)) = false := by decide

theorem single_hw_mem : Pi.single (.inl 0, hwL) (1 : F) ∈ stSub F := by
  refine mem_stSub.mpr fun i j k => ?_
  rw [ι3f_single, ι3f_single, ι3f_single]
  exact ite3_eq_zero _ _ _ (wedge_hw_free i j k)

theorem single_low_mem : Pi.single (.inr 0, lowL) (1 : F) ∈ stSub F := by
  refine mem_stSub.mpr fun i j k => ?_
  rw [ι3f_single, ι3f_single, ι3f_single]
  exact ite3_eq_zero _ _ _ (wedge_low_free i j k)

@[expose] def hwS : SIdx := ⟨(.inl 0, hwL), by decide⟩

@[expose] def lowS : SIdx := ⟨(.inr 0, lowL), by decide⟩

theorem secSt_single (π : SIdx) (h : Pi.single π.1 (1 : F) ∈ stSub F) :
    (secSt F).mulVec (Pi.single π 1) = Pi.single π.1 1 := by
  rw [← secSt_restrict h]
  congr 1
  funext π'
  rw [Pi.single_apply, Pi.single_apply]
  exact if_congr Subtype.ext_iff rfl rfl

theorem secSt_hwS : (secSt F).mulVec (Pi.single hwS 1) = Pi.single (.inl 0, hwL) 1 :=
  secSt_single hwS single_hw_mem

theorem secSt_lowS : (secSt F).mulVec (Pi.single lowS 1) = Pi.single (.inr 0, lowL) 1 :=
  secSt_single lowS single_low_mem

theorem repQL_single (g : ↥(cayleyGroup F)) (a : Ix3) (p : LIdx) (c : Ix3 × LIdx) :
    (repQL g).mulVec (Pi.single (a, p) 1) c =
      repQ g c.1 a * (repLie g).mulVec (Pi.single p (1 : F)) c.2 := by
  have e : (Pi.single (a, p) (1 : F) : Ix3 × LIdx → F) =
      fun c : Ix3 × LIdx => (Pi.single a (1 : F) : Ix3 → F) c.1 *
        (Pi.single p (1 : F) : LIdx → F) c.2 := by
    funext c
    obtain ⟨b, p'⟩ := c
    by_cases hb : b = a <;> by_cases hp : p' = p <;> simp [hb, hp]
  rw [e, repQL, kron2Rep_apply, kron2_mulVec, Matrix.mulVec_single_one]
  rfl

theorem repSt_lowS (g : ↥(cayleyGroup F)) (π : SIdx) :
    (repSt g).mulVec (Pi.single lowS 1) π =
      repQ g π.1.1 (.inr 0) * (repLie g).mulVec (Pi.single lowL (1 : F)) π.1.2 := by
  rw [repSt_mulVec, secSt_lowS, repQL_single]

theorem repSt_hwS (g : ↥(cayleyGroup F)) (π : SIdx) :
    (repSt g).mulVec (Pi.single hwS 1) π =
      repQ g π.1.1 (.inl 0) * (repLie g).mulVec (Pi.single hwL (1 : F)) π.1.2 := by
  rw [repSt_mulVec, secSt_hwS, repQL_single]

theorem repSt_U0_hw {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    (repSt u).mulVec (Pi.single hwS 1) = Pi.single hwS 1 := by
  funext π
  rw [repSt_hwS, repLie_U0_hw hu, repQ_U0_apply hu (Nat.zero_le _)]
  simp only [Pi.single_apply]
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  by_cases ha : a = .inl 0 <;> by_cases hp : p = hwL <;> simp [ha, hp, hwS]

theorem repSt_g2Sw_hw :
    (repSt (g2Sw : ↥(cayleyGroup F))).mulVec (Pi.single hwS 1) = Pi.single lowS 1 := by
  funext π
  rw [repSt_hwS, repLie_g2Sw_hw, repQ_g2Sw, formQ_apply]
  simp only [Pi.single_apply]
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  by_cases ha : a = .inr 0 <;> by_cases hp : p = lowL
  · subst ha hp
    simp [lowS]
  · simp [hp, lowS]
  · have : (Sum.inl 0 : Ix3) ≠ a.swap := fun h => ha (by rw [← Sum.swap_swap a, ← h]; rfl)
    simp [this, ha, lowS]
  · simp [hp, lowS]

end CFSG.Quasithin.B42G2Ten
