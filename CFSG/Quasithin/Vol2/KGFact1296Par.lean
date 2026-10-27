module

public import CFSG.Quasithin.Vol2.KGFact1296Red
public import CFSG.Quasithin.Vol2.KGFactH91B
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag

public section

namespace CFSG.Quasithin.H13.KG1296

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.SLnTwo
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm

variable {n : ℕ}

abbrev Pone (n : ℕ) : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  flagStabilizer n (ZMod 2) {1}

theorem Pone_stab {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ Pone n) :
    g ∈ stabilizer (flagSpace n (ZMod 2) 1) :=
  mem_flagStabilizer.1 hg 1 rfl

theorem Pone_apply_zero (hn : 1 ≤ n) {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ Pone n) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  have h00 : blkAt 0 1 (by omega) (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
    blkAt_one_eq_one (Nat.card_zmod 2) (Pone n) 0 (by omega) (blockLeft_zero _ 1)
      (blockRight_of_stabilizer fun _ hx => Pone_stab hx) ⟨g, hg⟩
  have h00' := congrFun (congrFun h00 0) 0
  simpa [blkAt_apply] using h00'

theorem mem_Pone_iff (hn : 1 ≤ n) {g : SpecialLinearGroup (Fin n) (ZMod 2)} :
    g ∈ Pone n ↔ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) (ZMod 2)) i ⟨0, by omega⟩ =
      if (i : ℕ) = 0 then 1 else 0 := by
  constructor
  · intro hg i
    split_ifs with hi
    · have : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [this]
      exact Pone_apply_zero hn hg
    · exact stabilizer_entries (Pone_stab hg) (l := ⟨0, by omega⟩) (by simp) (by omega)
  · intro hg
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    rw [Set.mem_singleton_iff] at hc
    rw [hc] at hl hk
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simp only; omega)
    rw [hl0, hg k]
    split_ifs with hk0
    · omega
    · rfl

theorem Pone_mulVec (hn : 1 ≤ n) {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ Pone n) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨0, by omega⟩ 1 =
      Pi.single ⟨0, by omega⟩ 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  show (g : Matrix (Fin n) (Fin n) (ZMod 2)) i ⟨0, by omega⟩ = _
  rw [(mem_Pone_iff hn).1 hg i]
  by_cases hi : (i : ℕ) = 0
  · rw [ite_eq_left hi, show i = ⟨0, by omega⟩ from Fin.ext hi, Pi.single_eq_same]
  · rw [ite_eq_right hi, Pi.single_eq_of_ne (fun h => hi (by rw [h]))]

theorem transvection_mem_Pone (hn : 1 ≤ n) {i j : Fin n} (hij : i ≠ j) (hj : (j : ℕ) ≠ 0) :
    SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ Pone n := by
  rw [mem_Pone_iff hn]
  intro k
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
  have hj' : ¬ j = (⟨0, by omega⟩ : Fin n) := fun h => hj (by rw [h])
  simp only [hj', and_false, ite_false, add_zero, Matrix.one_apply]
  by_cases hk : (k : ℕ) = 0
  · rw [ite_eq_left (Fin.ext hk), ite_eq_left hk]
  · rw [ite_eq_right (fun h => hk (by rw [h])), ite_eq_right hk]

theorem fixed_Pone (hn : 2 ≤ n) {x : Fin n → ZMod 2}
    (h : ∀ g ∈ Pone n, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x) :
    ∀ j : Fin n, (j : ℕ) ≠ 0 → x j = 0 := by
  intro j hj
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ j := fun h' => hj (by rw [← h'])
  have := h _ (transvection_mem_Pone (by omega) h0 hj)
  rw [mulVec_transvection] at this
  have h2 := congrFun this ⟨0, by omega⟩
  simpa using h2

theorem fixed_graph_Pone (hn : 3 ≤ n) {x : Fin n → ZMod 2}
    (h : ∀ g ∈ Pone n, (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x) :
    x = 0 := by
  have hδ : ∀ {i j : Fin n} (hij : i ≠ j), (j : ℕ) ≠ 0 →
      (slGraphAut n (ZMod 2) (SpecialLinearGroup.transvection hij (1 : ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x + Pi.single j (x i) := by
    intro i j hij hj
    have ht : (SpecialLinearGroup.transvection hij (1 : ZMod 2))⁻¹ =
        SpecialLinearGroup.transvection hij (1 : ZMod 2) :=
      inv_eq_of_mul_eq_one_right (transvection_mul_self hij)
    rw [slGraphAut_matrix, ht, SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec]
    congr 1
    ext k
    by_cases hk : k = j
    · subst hk
      simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
    · simp [Matrix.mulVec, dotProduct, Ne.symm hk, hk]
  ext i
  rw [Pi.zero_apply]
  obtain ⟨j, hji, hj0⟩ : ∃ j : Fin n, j ≠ i ∧ (j : ℕ) ≠ 0 := by
    by_cases hi : (i : ℕ) = 1
    · exact ⟨⟨2, by omega⟩, fun h => by rw [← h] at hi; simp at hi, by simp⟩
    · exact ⟨⟨1, by omega⟩, fun h => hi (by rw [← h]), by simp⟩
  have := h _ (transvection_mem_Pone (by omega) (Ne.symm hji) hj0)
  rw [hδ (Ne.symm hji) hj0] at this
  have h2 := congrFun this j
  simpa using h2

section Levi

variable {k : ℕ}

theorem Pone_col {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} (hg : g ∈ Pone (k + 1))
    (i : Fin (k + 1)) : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i 0 =
      if i = 0 then 1 else 0 := by
  have h := (mem_Pone_iff (by omega)).1 hg i
  show (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i ⟨0, by omega⟩ = _
  rw [h]
  by_cases hi : i = 0
  · rw [ite_eq_left (show (i : ℕ) = 0 by rw [hi]; rfl), ite_eq_left hi]
  · rw [ite_eq_right (show ¬ ((i : ℕ) = 0) from fun h' => hi (Fin.ext (by simpa using h'))),
      ite_eq_right hi]

theorem mem_Pone_of_col {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)}
    (h : ∀ i : Fin (k + 1), (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i 0 =
      if i = 0 then 1 else 0) : g ∈ Pone (k + 1) := by
  refine (mem_Pone_iff (by omega)).2 fun i => ?_
  show (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i 0 = _
  rw [h i]
  by_cases hi : i = 0
  · rw [ite_eq_left hi, ite_eq_left (show (i : ℕ) = 0 by rw [hi]; rfl)]
  · rw [ite_eq_right hi,
      ite_eq_right (show ¬ ((i : ℕ) = 0) from fun h' => hi (Fin.ext (by simpa using h')))]

@[expose] def blk (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun i j => g i.succ j.succ

theorem blk_apply (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) (i j : Fin k) :
    blk g i j = g i.succ j.succ := rfl

theorem blk_mul {g h : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)}
    (hg : ∀ i : Fin k, g i.succ 0 = 0) : blk (g * h) = blk g * blk h := by
  ext i j
  simp only [blk_apply, Matrix.mul_apply, Fin.sum_univ_succ, hg i, zero_mul, zero_add]

theorem blk_one : blk (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = 1 := by
  ext i j
  simp [blk_apply, Matrix.one_apply, Fin.succ_inj]

theorem det_eq_det_blk {g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)}
    (hg : ∀ i : Fin (k + 1), g i 0 = if i = 0 then 1 else 0) : g.det = (blk g).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hg, Fin.succ_ne_zero, ite_false, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, ite_true, Fin.val_zero, pow_zero, one_mul]
  rfl

@[expose] noncomputable def betaOne (k : ℕ) :
    ↥(Pone (k + 1)) →* SpecialLinearGroup (Fin k) (ZMod 2) where
  toFun g := ⟨blk (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)), by
    rw [← det_eq_det_blk (Pone_col g.2)]
    exact (g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)).2⟩
  map_one' := Subtype.ext blk_one
  map_mul' g h := Subtype.ext (blk_mul fun i => by
    rw [Pone_col g.2]
    exact ite_eq_right (Fin.succ_ne_zero i))

theorem betaOne_apply (g : ↥(Pone (k + 1))) (i j : Fin k) :
    ((betaOne k g : SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) i j =
      ((g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1))
        (ZMod 2)) i.succ j.succ := rfl

@[expose] def liftMat (M : Matrix (Fin k) (Fin k) (ZMod 2)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2) :=
  Matrix.of (Fin.cases (Fin.cases 1 fun _ => 0) fun i => Fin.cases 0 fun j => M i j)

theorem liftMat_col (M : Matrix (Fin k) (Fin k) (ZMod 2)) (i : Fin (k + 1)) :
    liftMat M i 0 = if i = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [liftMat, Fin.succ_ne_zero]

theorem blk_liftMat (M : Matrix (Fin k) (Fin k) (ZMod 2)) : blk (liftMat M) = M := by
  ext i j
  rfl

@[expose] noncomputable def liftOne (M : SpecialLinearGroup (Fin k) (ZMod 2)) : ↥(Pone (k + 1)) :=
  ⟨⟨liftMat M, by rw [det_eq_det_blk (liftMat_col _), blk_liftMat]; exact M.2⟩,
    mem_Pone_of_col (liftMat_col _)⟩

theorem betaOne_liftOne (M : SpecialLinearGroup (Fin k) (ZMod 2)) : betaOne k (liftOne M) = M :=
  Subtype.ext (blk_liftMat _)

theorem betaOne_surjective : Function.Surjective (betaOne k) := fun M =>
  ⟨liftOne M, betaOne_liftOne M⟩

@[expose] def radOne (k : ℕ) : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) where
  carrier := {g | ∃ φ : Fin (k + 1) → ZMod 2, φ 0 = 0 ∧
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = 1 + vecMulVec (Pi.single 0 1) φ}
  one_mem' := ⟨0, rfl, by simp⟩
  mul_mem' := by
    rintro g h ⟨φ, hφ, hg⟩ ⟨ψ, hψ, hh⟩
    refine ⟨φ + ψ, by simp [hφ, hψ], ?_⟩
    have h0 : vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
        vecMulVec (Pi.single 0 1) ψ = 0 := by
      rw [vecMulVec_mul_vecMulVec, dotProduct_single, hφ, zero_mul, zero_smul, vecMulVec_zero]
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, vecMulVec_add]
    calc (1 + vecMulVec (Pi.single 0 1) φ) * (1 + vecMulVec (Pi.single 0 1) ψ)
        = 1 + (vecMulVec (Pi.single 0 1) φ + vecMulVec (Pi.single 0 1) ψ) +
            vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
              vecMulVec (Pi.single 0 1) ψ := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  inv_mem' := by
    rintro g ⟨φ, hφ, hg⟩
    have h2 : g * g = 1 := by
      apply Subtype.ext
      have h0 : vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
          vecMulVec (Pi.single 0 1) φ = 0 := by
        rw [vecMulVec_mul_vecMulVec, dotProduct_single, hφ, zero_mul, zero_smul, vecMulVec_zero]
      have h22 : vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ +
          vecMulVec (Pi.single 0 1) φ = 0 := CharTwo.add_self_eq_zero _
      rw [Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
      calc (1 + vecMulVec (Pi.single 0 1) φ) * (1 + vecMulVec (Pi.single 0 1) φ)
          = 1 + (vecMulVec (Pi.single 0 1) φ + vecMulVec (Pi.single 0 1) φ) +
              vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
                vecMulVec (Pi.single 0 1) φ := by noncomm_ring
        _ = 1 := by rw [h0, h22, add_zero, add_zero]
    rw [inv_eq_of_mul_eq_one_right h2]
    exact ⟨φ, hφ, hg⟩

@[expose] noncomputable def radElt (φ : Fin (k + 1) → ZMod 2) (hφ : φ 0 = 0) :
    SpecialLinearGroup (Fin (k + 1)) (ZMod 2) :=
  ⟨1 + vecMulVec (Pi.single 0 1) φ, by
    rw [vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow, dotProduct_single, hφ,
      mul_one, add_zero]⟩

theorem radElt_mem (φ : Fin (k + 1) → ZMod 2) (hφ : φ 0 = 0) : radElt φ hφ ∈ radOne k :=
  ⟨φ, hφ, rfl⟩

theorem radOne_le_Pone : radOne k ≤ Pone (k + 1) := by
  rintro g ⟨φ, hφ, hg⟩
  refine mem_Pone_of_col fun i => ?_
  rw [hg, Matrix.add_apply, vecMulVec_apply, hφ, mul_zero, add_zero, Matrix.one_apply]

theorem radOne_mul_self {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} (hg : g ∈ radOne k) :
    g * g = 1 := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  apply Subtype.ext
  have h0 : vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
      vecMulVec (Pi.single 0 1) φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, dotProduct_single, hφ, zero_mul, zero_smul, vecMulVec_zero]
  have h22 : vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ +
      vecMulVec (Pi.single 0 1) φ = 0 := CharTwo.add_self_eq_zero _
  rw [Matrix.SpecialLinearGroup.coe_mul, hgφ, Matrix.SpecialLinearGroup.coe_one]
  calc (1 + vecMulVec (Pi.single 0 1) φ) * (1 + vecMulVec (Pi.single 0 1) φ)
      = 1 + (vecMulVec (Pi.single 0 1) φ + vecMulVec (Pi.single 0 1) φ) +
          vecMulVec (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2)) φ *
            vecMulVec (Pi.single 0 1) φ := by noncomm_ring
    _ = 1 := by rw [h0, h22, add_zero, add_zero]

theorem isPGroup_radOne : IsPGroup 2 (radOne k) := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, sq]; exact radOne_mul_self x.2)⟩

theorem conj_radElt {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} (hg : g ∈ Pone (k + 1))
    {x : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} {φ : Fin (k + 1) → ZMod 2}
    (hx : (x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = 1 + vecMulVec (Pi.single 0 1) φ) :
    ((g * x * g⁻¹ : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) =
      1 + vecMulVec (Pi.single 0 1)
        (φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2))) := by
  have hge : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
    funext i
    rw [Matrix.mulVec_single_one]
    show (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i 0 = _
    rw [Pone_col hg i, Pi.single_apply]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, mul_vecMulVec, vecMulVec_mul, hge, coe_mul_inv]

theorem vecMul_zero_of_Pone {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)}
    (hg : g ∈ Pone (k + 1)) {φ : Fin (k + 1) → ZMod 2} (hφ : φ 0 = 0) :
    (φ ᵥ* (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2))) 0 = 0 := by
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, hφ, zero_mul, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) i.succ 0 = 0 by
    rw [Pone_col hg]; exact ite_eq_right (Fin.succ_ne_zero i), mul_zero]

theorem Pone_le_normalizer_radOne :
    Pone (k + 1) ≤ Subgroup.normalizer ((radOne k : Subgroup _) : Set _) := by
  refine le_normalizer_of_forall fun g hg x hx => ?_
  obtain ⟨φ, hφ, hxφ⟩ := hx
  exact ⟨_, vecMul_zero_of_Pone (inv_mem hg) hφ, conj_radElt hg hxφ⟩

end Levi

section Irreducible

variable {k : ℕ}

theorem exists_vecMul_eq (hk : 1 ≤ k) {u v : Fin k → ZMod 2} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin k) (ZMod 2), u ᵥ* (M : Matrix (Fin k) (Fin k) (ZMod 2)) = v := by
  obtain ⟨a, ha⟩ := exists_mulVec_eq hk hu
  obtain ⟨b, hb⟩ := exists_mulVec_eq hk hv
  refine ⟨(b * a⁻¹).transpose, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.vecMul_transpose, ← ha,
    Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hb]

theorem vecMul_liftMat (ψ : Fin (k + 1) → ZMod 2) (M : Matrix (Fin k) (Fin k) (ZMod 2)) :
    ψ ᵥ* liftMat M = Fin.cons (ψ 0) (Fin.tail ψ ᵥ* M) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, liftMat]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, liftMat, Fin.tail]

theorem eq_one_of_tail {x : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} {φ : Fin (k + 1) → ZMod 2}
    (hφ0 : φ 0 = 0) (hφ : Fin.tail φ = 0)
    (hx : (x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = 1 + vecMulVec (Pi.single 0 1) φ) :
    x = 1 := by
  have : φ = 0 := by
    funext j
    refine Fin.cases hφ0 (fun j => ?_) j
    exact congrFun hφ j
  apply Subtype.ext
  rw [hx, this, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]

theorem eq_radOne_of_normalized (hk : 1 ≤ k)
    {Q : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))} (hQR : Q ≤ radOne k)
    (hQN : Pone (k + 1) ≤ Subgroup.normalizer (Q : Set _)) (hQ : Q ≠ ⊥) :
    Q = radOne k := by
  obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hQ (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨φ, hφ0, hxφ⟩ := hQR hxQ
  have hφ : Fin.tail φ ≠ 0 := fun h => hx1 (eq_one_of_tail hφ0 h hxφ)
  refine le_antisymm hQR ?_
  rintro y ⟨ψ, hψ0, hyψ⟩
  by_cases hψ : Fin.tail ψ = 0
  · rw [eq_one_of_tail hψ0 hψ hyψ]
    exact Q.one_mem
  · obtain ⟨M, hM⟩ := exists_vecMul_eq hk hψ hφ
    set g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2) :=
      ((liftOne M : ↥(Pone (k + 1))) : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) with hg
    have hgP : g ∈ Pone (k + 1) := (liftOne M).2
    have hψg : ψ ᵥ* (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = φ := by
      show ψ ᵥ* liftMat M = φ
      rw [vecMul_liftMat, hψ0, hM]
      conv_rhs => rw [← Fin.cons_self_tail φ, hφ0]
    have hφg : φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = ψ := by
      rw [← hψg, Matrix.vecMul_vecMul, coe_mul_inv, Matrix.vecMul_one]
    have hconj : g * x * g⁻¹ = y := by
      apply Subtype.ext
      rw [conj_radElt hgP hxφ, hφg, hyψ]
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.1 (hQN hgP) x).1 hxQ

theorem mem_radOne_of_betaOne {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)}
    (hg : g ∈ Pone (k + 1)) (h : betaOne k ⟨g, hg⟩ = 1) : g ∈ radOne k := by
  refine ⟨fun j => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) 0 j - if j = 0 then 1 else 0,
    by simp [Pone_col hg 0], ?_⟩
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply, Matrix.one_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Pi.single_eq_same, one_mul]
    by_cases hj : j = 0
    · subst hj
      rw [ite_eq_left rfl]
      ring
    · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj]
      ring
  · have hi : (Pi.single (0 : Fin (k + 1)) (1 : ZMod 2) : Fin (k + 1) → ZMod 2) i.succ = 0 :=
      Pi.single_eq_of_ne (Fin.succ_ne_zero i) _
    rw [hi, zero_mul, add_zero]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Pone_col hg i.succ]
    · have := congrFun (congrFun (congrArg (fun M : SpecialLinearGroup (Fin k) (ZMod 2) =>
        (M : Matrix (Fin k) (Fin k) (ZMod 2))) h) i) j
      rw [betaOne_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] at this
      rw [this]
      simp [Fin.succ_inj]

theorem pCoreOf_Pone (hk : 3 ≤ k) : pCoreOf 2 (Pone (k + 1)) = radOne k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro g hg
    have hgP : g ∈ Pone (k + 1) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hg
    refine mem_radOne_of_betaOne hgP ?_
    set N := ((pCoreOf 2 (Pone (k + 1))).subgroupOf (Pone (k + 1))).map (betaOne k) with hN
    have hNn : N.Normal := by
      refine Subgroup.Normal.map ?_ _ betaOne_surjective
      refine ⟨fun x hx y => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ y.2) _).1 hx
    have hN2 : IsPGroup 2 N :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype).map _
    have hbot := CFSG.Quasithin.H13.KGH91.NatCoord.eq_bot_of_normal_isPGroup hk hN2
    have : betaOne k ⟨g, hgP⟩ ∈ N := ⟨⟨g, hgP⟩, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 radOne_le_Pone
      Pone_le_normalizer_radOne isPGroup_radOne

end Irreducible

section Normal

variable {k : ℕ}

theorem not_isPGroup_of_modO2 {M : Type} [Group M] {B : Subgroup M} {H : Type*} [Group H]
    [Nontrivial H] (hB : Nonempty (ModO2 B ≃* H)) : ¬ IsPGroup 2 B := by
  intro h2
  obtain ⟨e⟩ := hB
  have htop : CFSG.pCore 2 ↥B = ⊤ := by
    refine eq_top_iff.2 (le_pCore_of_normal (N := ⊤) Subgroup.normal_top fun x => ?_)
    obtain ⟨m, hm⟩ := h2 x.1
    exact ⟨m, Subtype.ext (by rw [Subgroup.coe_pow, hm]; rfl)⟩
  have hq : ∀ q : ModO2 B, q = 1 := fun q => QuotientGroup.induction_on q fun b =>
    (QuotientGroup.eq_one_iff b).2 (by rw [htop]; exact Subgroup.mem_top b)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne H
  exact hxy (e.symm.injective ((hq _).trans (hq _).symm))

theorem vecMul_eq_of_conj {g : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)} (hg : g ∈ Pone (k + 1))
    {φ : Fin (k + 1) → ZMod 2} (hφ : φ 0 = 0) (h : g * radElt φ hφ * g⁻¹ = radElt φ hφ) :
    φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) = φ := by
  have h1 := conj_radElt hg (x := radElt φ hφ) rfl
  rw [h] at h1
  change 1 + vecMulVec (Pi.single 0 1) φ = _ at h1
  funext j
  have h2 := congrFun (congrFun h1 0) j
  rw [Matrix.add_apply, Matrix.add_apply, vecMulVec_apply, vecMulVec_apply, Pi.single_eq_same,
    one_mul, one_mul] at h2
  exact (add_left_cancel h2).symm

theorem eq_Pone_of_normal (hk : 3 ≤ k) {B : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))}
    (hBP : B ≤ Pone (k + 1)) (hN : Pone (k + 1) ≤ Subgroup.normalizer (B : Set _))
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin k) (ZMod 2))) : B = Pone (k + 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := sl_isSimple_of_card_two (K := ZMod 2) (Nat.card_zmod 2) hk
  have hnotR : ¬ B ≤ radOne k := fun h => not_isPGroup_of_modO2 hB (isPGroup_radOne.to_le h)
  set N := (B.subgroupOf (Pone (k + 1))).map (betaOne k) with hNdef
  have hNn : N.Normal := by
    refine Subgroup.Normal.map ⟨fun x hx y => ?_⟩ _ betaOne_surjective
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hN y.2) _).1 hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · refine absurd (fun b hb => mem_radOne_of_betaOne (hBP hb) ?_) hnotR
    have : betaOne k ⟨b, hBP hb⟩ ∈ N := ⟨⟨b, hBP hb⟩, hb, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hBRN : Pone (k + 1) ≤ Subgroup.normalizer ((B ⊓ radOne k : Subgroup _) : Set _) :=
    le_normalizer_of_forall fun g hg x hx =>
      ⟨(Subgroup.mem_normalizer_iff.1 (hN hg) x).1 hx.1,
        (Subgroup.mem_normalizer_iff.1 (Pone_le_normalizer_radOne hg) x).1 hx.2⟩
  by_cases h1 : B ⊓ radOne k = ⊥
  ·
    exfalso
    have hcomm : ∀ b ∈ B, ∀ r ∈ radOne k, b * r * b⁻¹ = r := by
      intro b hb r hr
      have h1' : b * r * b⁻¹ * r⁻¹ ∈ B ⊓ radOne k := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have : r * b⁻¹ * r⁻¹ ∈ B :=
            (Subgroup.mem_normalizer_iff.1 (hN (radOne_le_Pone hr)) _).1 (inv_mem hb)
          rw [show b * r * b⁻¹ * r⁻¹ = b * (r * b⁻¹ * r⁻¹) by group]
          exact mul_mem hb this
        · have : b * r * b⁻¹ ∈ radOne k :=
            (Subgroup.mem_normalizer_iff.1 (Pone_le_normalizer_radOne (hBP hb)) r).1 hr
          exact mul_mem this (inv_mem hr)
      rw [h1, Subgroup.mem_bot] at h1'
      exact mul_inv_eq_one.1 h1'
    refine hnotR fun b hb => mem_radOne_of_betaOne (hBP hb) (Subtype.ext ?_)
    ext i j
    rw [betaOne_apply, Matrix.SpecialLinearGroup.coe_one]
    have hφ : (Pi.single i.succ 1 : Fin (k + 1) → ZMod 2) 0 = 0 :=
      Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm _
    have hv := vecMul_eq_of_conj (inv_mem (hBP hb)) hφ
      (hcomm _ (inv_mem hb) _ (radElt_mem _ hφ))
    rw [inv_inv, single_one_vecMul] at hv
    have := congrFun hv j.succ
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp only [Fin.succ_inj, eq_comm]
  ·
    have hR : radOne k ≤ B := by
      have h2 := eq_radOne_of_normalized (by omega) inf_le_right hBRN h1
      rw [← h2]
      exact inf_le_left
    refine le_antisymm hBP fun g hg => ?_
    have : betaOne k ⟨g, hg⟩ ∈ N := htop ▸ Subgroup.mem_top _
    obtain ⟨⟨b, hbP⟩, hb, hbg⟩ := this
    have hker : b⁻¹ * g ∈ radOne k := mem_radOne_of_betaOne (mul_mem (inv_mem hbP) hg) (by
      show betaOne k (⟨b, hbP⟩⁻¹ * ⟨g, hg⟩) = 1
      rw [map_mul, map_inv, hbg, inv_mul_cancel])
    have := mul_mem (Subgroup.mem_subgroupOf.1 hb) (hR hker)
    rwa [mul_inv_cancel_left] at this

end Normal

section Closed

variable {k : ℕ}

theorem coe_slConjugation (A : GL (Fin n) (ZMod 2)) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((slConjugation n (ZMod 2) A g : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have := congrArg Units.val (toGL_slConjugation n (ZMod 2) A g)
  rw [Units.val_mul, Units.val_mul] at this
  exact this

theorem innClosed_Pone (hk : 2 ≤ k) : InnClosed (Pone (k + 1)) := by
  intro α hα _
  obtain ⟨A, ε, hε, rfl⟩ := exists_conj_graph (by omega) α
  set e₀ : Fin (k + 1) → ZMod 2 := Pi.single 0 1 with he₀
  set v : Fin (k + 1) → ZMod 2 := ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ e₀ with hv
  have hAv : (A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ v = e₀ := by
    rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hAv
    have := congrFun hAv 0
    rw [he₀, Pi.single_eq_same, Pi.zero_apply] at this
    exact zero_ne_one this
  have hconj : ∀ y : SpecialLinearGroup (Fin (k + 1)) (ZMod 2),
      slConjugation (k + 1) (ZMod 2) A y ∈ Pone (k + 1) →
        (y : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ v = v := by
    intro y hy
    have h1 : ((slConjugation (k + 1) (ZMod 2) A y : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ e₀ = e₀ := Pone_mulVec (by omega) hy
    rw [coe_slConjugation] at h1
    have hA : ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *
        ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) * (y : Matrix _ _ (ZMod 2)) *
          ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2))) =
        (y : Matrix _ _ (ZMod 2)) *
          ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) := by
      rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    calc (y : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ v
        = ((y : Matrix _ _ (ZMod 2)) *
            ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2))) *ᵥ
              e₀ := by rw [hv, Matrix.mulVec_mulVec]
      _ = ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) *ᵥ
            (((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) * (y : Matrix _ _ (ZMod 2)) *
              ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2))) *ᵥ e₀) := by
          rw [Matrix.mulVec_mulVec, hA]
      _ = v := by rw [h1]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have hvj := fixed_Pone (by omega) fun x hx => hconj x (hα x hx)
    have hv00 : v 0 = 1 := by
      rcases zmod_two_cases (v 0) with h | h
      · exfalso
        apply hv0
        funext j
        refine Fin.cases h (fun j => ?_) j
        exact hvj _ (by simp)
      · exact h
    have hve : v = e₀ := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hv00, he₀, Pi.single_eq_same]
      · rw [hvj _ (by simp), he₀, Pi.single_eq_of_ne (Fin.succ_ne_zero j)]
    rw [hve] at hAv
    set a := (slEquivGL (k + 1)).symm A with ha
    have haA : (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) =
        (A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) := by
      rw [← coe_slEquivGL, ha, MulEquiv.apply_symm_apply]
    have hainv : ((a⁻¹ : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) =
        ((A⁻¹ : GL (Fin (k + 1)) (ZMod 2)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) := by
      rw [← coe_slEquivGL, map_inv, ha, MulEquiv.apply_symm_apply]
    have haP : a ∈ Pone (k + 1) := by
      refine mem_Pone_of_col fun i => ?_
      have := congrFun hAv i
      rw [he₀, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
      rw [haA, this]
    refine ⟨a, haP, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [coe_slConjugation, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, haA, hainv]
  · exfalso
    rw [pow_one] at hα
    exact hv0 (fixed_graph_Pone (by omega) fun x hx => hconj _ (hα x hx))

theorem parConclusion_Pone (hk : 3 ≤ k) (m : ℕ) : ParConclusion (Pone (k + 1)) m := by
  intro Q hQ hQne hQbot hQN _
  rw [pCoreOf_Pone hk] at hQ hQne
  exact absurd (eq_radOne_of_normalized (by omega) hQ hQN hQbot) hQne

end Closed

end CFSG.Quasithin.H13.KG1296
