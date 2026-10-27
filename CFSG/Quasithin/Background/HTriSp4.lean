module

public import CFSG.Quasithin.Background.HTriangular

public section

namespace CFSG.Quasithin

namespace H

namespace Tri

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type*} [Field K]

@[expose] noncomputable def uniGL (n : ℕ) (K : Type*) [Field K] : Subgroup (GL (Fin n) K) :=
  (LinearFlag.unitriangular n K).map Matrix.SpecialLinearGroup.toGL

theorem uniGL_entries {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ uniGL n K) :
    (∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) K) i i = 1 := by
  obtain ⟨u, hu, rfl⟩ := hg
  exact LinearFlag.mem_unitriangular.mp hu

theorem mem_uniGL_of {n : ℕ} {g : GL (Fin n) K}
    (h1 : ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) K) i j = 0)
    (h2 : ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) K) i i = 1) : g ∈ uniGL n K := by
  have hU : (g : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun i j hij => h1 i j hij
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    simp [h2]
  let u : Matrix.SpecialLinearGroup (Fin n) K := ⟨g, hdet⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, LinearFlag.mem_unitriangular]
  exact ⟨h1, h2⟩

theorem uniGL_le_borGL (n : ℕ) : uniGL n K ≤ borGL n K := fun _ hg =>
  mem_borGL.mpr (uniGL_entries hg).1

theorem card_uniGL [Finite K] (n : ℕ) :
    Nat.card (uniGL n K) = Nat.card K ^ (n * (n - 1) / 2) := by
  rw [uniGL, Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective,
    LinearFlag.card_unitriangular]

theorem isPGroup_uniGL [Finite K] [CharP K 2] (n : ℕ) : IsPGroup 2 (uniGL n K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := k * (n * (n - 1) / 2)) ?_
  rw [card_uniGL, Nat.card_eq_fintype_card, hk, ← pow_mul]

theorem pow_card_sub_one_eq_one [Finite K] [CharP K 2] {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ borGL n K) (hodd : Odd (orderOf A)) : A ^ (Nat.card K - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hdiag : ∀ (k : ℕ) (i : Fin n), ((A ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((A : Matrix (Fin n) (Fin n) K) i i) ^ k := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, LinearFlag.mul_apply_self_of_isUpperTriangular
        ((borGL n K).pow_mem hA k) hA, ih, pow_succ]
  have hne : ∀ i, (A : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro i h
    have hdet : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
    rw [Matrix.det_of_isUpperTriangular hA] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h)
  set D := A ^ (Nat.card K - 1) with hDdef
  have hD : D ∈ borGL n K := (borGL n K).pow_mem hA _
  have hDU : D ∈ uniGL n K := by
    refine mem_uniGL_of (mem_borGL.mp hD) fun i => ?_
    rw [hDdef, hdiag, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (hne i)
  obtain ⟨j, hj⟩ := isPGroup_uniGL n ⟨D, hDU⟩
  have hDj : D ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf A ∣ (Nat.card K - 1) * 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hDj)
  have hcop : Nat.Coprime (orderOf A) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h1)

@[expose] def flagStab (n k : ℕ) (K : Type*) [Field K] : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K).BlockTriangular
    fun i : Fin n => if (i : ℕ) < k then 0 else 1}
  mul_mem' := fun {a b} ha hb => by
    change ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular _
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    change ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular _
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular _
    have := a.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular ha

theorem mem_flagStab {n k : ℕ} {g : GL (Fin n) K} :
    g ∈ flagStab n k K ↔ ∀ i j : Fin n, (j : ℕ) < k → k ≤ (i : ℕ) →
      (g : Matrix (Fin n) (Fin n) K) i j = 0 := by
  constructor
  · intro h i j hj hi
    refine h ?_
    have h1 : ¬ (i : ℕ) < k := by omega
    simp only [hj, h1, ↓reduceIte, zero_lt_one]
  · intro h i j hij
    simp only at hij
    by_cases hj : (j : ℕ) < k
    · by_cases hi : (i : ℕ) < k
      · simp only [hj, hi, ↓reduceIte, lt_irrefl] at hij
      · exact h i j hj (by omega)
    · simp only [hj, ↓reduceIte] at hij
      split_ifs at hij <;> omega

theorem borGL_le_flagStab (n k : ℕ) : borGL n K ≤ flagStab n k K := fun g hg =>
  mem_flagStab.mpr fun i j hj hi => mem_borGL.mp hg i j (Fin.lt_def.mpr (by omega))

@[expose] def succMat {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => g i.succ j.succ

theorem succMat_mul {n : ℕ} {g h : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hg : ∀ i : Fin n, g i.succ 0 = 0) : succMat (g * h) = succMat g * succMat h := by
  ext i j
  simp only [succMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_succ, hg, zero_mul,
    zero_add]

theorem succMat_one {n : ℕ} : succMat (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1 := by
  ext i j
  simp [succMat, Matrix.one_apply, Fin.succ_inj]

@[expose] def succHom {n : ℕ} {Q : Subgroup (GL (Fin (n + 1)) K)}
    (hQ : ∀ g ∈ Q, ∀ i : Fin n, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i.succ 0 = 0) :
    ↥Q →* GL (Fin n) K where
  toFun g :=
    { val := succMat ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
      inv := succMat (((g : GL (Fin (n + 1)) K)⁻¹ : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K)
      val_inv := by
        rw [← succMat_mul (hQ _ g.2), ← Units.val_mul, mul_inv_cancel, Units.val_one,
          succMat_one]
      inv_val := by
        rw [← succMat_mul (hQ _ (Q.inv_mem g.2)), ← Units.val_mul, inv_mul_cancel,
          Units.val_one, succMat_one] }
  map_one' := Units.ext (by
    change succMat ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1
    rw [Units.val_one, succMat_one])
  map_mul' a b := Units.ext (by
    change succMat (((a * b : ↥Q) : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      succMat ((a : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        succMat ((b : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    rw [Subgroup.coe_mul, Units.val_mul, succMat_mul (hQ _ a.2)])

@[expose] def topMat {n k : ℕ} (hk : k ≤ n) (g : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => g (Fin.castLE hk i) (Fin.castLE hk j)

theorem topMat_mul {n k : ℕ} (hk : k ≤ n) {g h : Matrix (Fin n) (Fin n) K}
    (hh : ∀ i j : Fin n, (j : ℕ) < k → k ≤ (i : ℕ) → h i j = 0) :
    topMat hk (g * h) = topMat hk g * topMat hk h := by
  ext i j
  simp only [topMat, Matrix.of_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ fun l => rfl
  intro l hl
  have hlk : k ≤ (l : ℕ) := by
    by_contra h'
    exact hl ⟨⟨l, by omega⟩, Fin.ext rfl⟩
  rw [hh l _ (by simp) hlk, mul_zero]

theorem topMat_one {n k : ℕ} (hk : k ≤ n) : topMat hk (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  simp only [topMat, Matrix.of_apply, Matrix.one_apply, Fin.castLE_inj]

@[expose] def topHom {n k : ℕ} (hk : k ≤ n) {Q : Subgroup (GL (Fin n) K)}
    (hQ : Q ≤ flagStab n k K) : ↥Q →* GL (Fin k) K where
  toFun g :=
    { val := topMat hk ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      inv := topMat hk (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      val_inv := by
        rw [← topMat_mul hk (mem_flagStab.mp (hQ (Q.inv_mem g.2))), ← Units.val_mul,
          mul_inv_cancel, Units.val_one, topMat_one]
      inv_val := by
        rw [← topMat_mul hk (mem_flagStab.mp (hQ g.2)), ← Units.val_mul, inv_mul_cancel,
          Units.val_one, topMat_one] }
  map_one' := Units.ext (by
    change topMat hk ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_one, topMat_one])
  map_mul' a b := Units.ext (by
    change topMat hk (((a * b : ↥Q) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      topMat hk ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        topMat hk ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Subgroup.coe_mul, Units.val_mul, topMat_mul hk (mem_flagStab.mp (hQ b.2))])

@[expose] def spMat (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a, c + a * d, b + a * c; 0, 1, d, c; 0, 0, 1, -a; 0, 0, 0, 1]

theorem spMat_lower (a b c d : K) : ∀ i j : Fin 4, j < i → spMat a b c d i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [spMat]

theorem spMat_diag (a b c d : K) : ∀ i : Fin 4, spMat a b c d i i = 1 := by
  intro i
  fin_cases i <;> simp [spMat]

@[expose] noncomputable def spN (a b c d : K) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (spMat a b c d) (by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => spMat_lower a b c d i j hij)]
    simp [spMat_diag])

theorem coe_spN (a b c d : K) :
    ((spN a b c d : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = spMat a b c d := rfl

theorem trGL_eq_spN (b : K) : trGL (0 : Fin 4) 3 (by decide) b = spN 0 b 0 0 := by
  apply Units.ext
  rw [coe_trGL, coe_spN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spMat, transvection]

theorem single_mem_flagSpace {n m : ℕ} {j : Fin n} (hj : (j : ℕ) < m) :
    (Pi.single j 1 : Fin n → K) ∈ LinearFlag.flagSpace n K m :=
  Submodule.subset_span ⟨j, hj, rfl⟩

theorem flagSpace_le_of {n m : ℕ} {W : Submodule K (Fin n → K)}
    (h : ∀ j : Fin n, (j : ℕ) < m → (Pi.single j 1 : Fin n → K) ∈ W) :
    LinearFlag.flagSpace n K m ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, hj, rfl⟩
  exact h j hj

theorem eq_flagSpace_of_spInvariant {W : Submodule K (Fin 4 → K)}
    (hW : ∀ a b c d : K, ∀ v ∈ W, spMat a b c d *ᵥ v ∈ W) :
    ∃ m ≤ 4, W = LinearFlag.flagSpace 4 K m := by
  classical
  have hdiff : ∀ a b c d : K, ∀ v ∈ W,
      (![a * v 1 + (c + a * d) * v 2 + (b + a * c) * v 3, d * v 2 + c * v 3, -a * v 3, 0] :
        Fin 4 → K) ∈ W := by
    intro a b c d v hv
    have h := W.sub_mem (hW a b c d v hv) hv
    convert h using 1
    ext i
    fin_cases i <;> simp [spMat, dotProduct, Fin.sum_univ_four] <;> ring
  have he : ∀ (x₀ x₁ x₂ x₃ : K), (![x₀, x₁, x₂, x₃] : Fin 4 → K) =
      x₀ • Pi.single 0 1 + x₁ • Pi.single 1 1 + x₂ • Pi.single 2 1 + x₃ • Pi.single 3 1 := by
    intro x₀ x₁ x₂ x₃
    ext i
    fin_cases i <;> simp
  have hv : ∀ v : Fin 4 → K, v = ![v 0, v 1, v 2, v 3] := fun v => by
    ext i
    fin_cases i <;> rfl
  by_cases h3 : ∃ v ∈ W, v 3 ≠ 0
  · obtain ⟨v, hvW, hv3⟩ := h3
    have e0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 3)⁻¹ (hdiff 0 1 0 0 v hvW)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv3]
    have e1 : (Pi.single 1 1 : Fin 4 → K) ∈ W := by
      have h := W.sub_mem (W.smul_mem (v 3)⁻¹ (hdiff 0 0 1 0 v hvW))
        (W.smul_mem ((v 3)⁻¹ * v 2) e0)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv3]
    have e2 : (Pi.single 2 1 : Fin 4 → K) ∈ W := by
      have h := W.add_mem (W.smul_mem (-(v 3)⁻¹) (hdiff 1 0 0 0 v hvW))
        (W.smul_mem ((v 3)⁻¹ * v 1) e0)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv3]
    have e3 : (Pi.single 3 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 3)⁻¹ (W.sub_mem (W.sub_mem (W.sub_mem hvW (W.smul_mem (v 0) e0))
        (W.smul_mem (v 1) e1)) (W.smul_mem (v 2) e2))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv3]
    refine ⟨4, le_rfl, le_antisymm (fun x _ => ?_) (flagSpace_le_of fun j _ => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      exact absurd j.2 (by omega)
    · fin_cases j
      exacts [e0, e1, e2, e3]
  push Not at h3
  by_cases h2 : ∃ v ∈ W, v 2 ≠ 0
  · obtain ⟨v, hvW, hv2⟩ := h2
    have hv3 := h3 v hvW
    have e0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ (hdiff 0 0 1 0 v hvW)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv2, hv3]
    have e1 : (Pi.single 1 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ (hdiff 0 0 0 1 v hvW)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv2, hv3]
    have e2 : (Pi.single 2 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ (W.sub_mem (W.sub_mem hvW (W.smul_mem (v 0) e0))
        (W.smul_mem (v 1) e1))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv2, hv3]
    refine ⟨3, by norm_num, le_antisymm (fun x hx => ?_) (flagSpace_le_of fun j hj => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj
      exact h3 x hx
    · fin_cases j <;> simp at hj
      exacts [e0, e1, e2]
  push Not at h2
  by_cases h1 : ∃ v ∈ W, v 1 ≠ 0
  · obtain ⟨v, hvW, hv1⟩ := h1
    have hv3 := h3 v hvW
    have hv2 := h2 v hvW
    have e0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 1)⁻¹ (hdiff 1 0 0 0 v hvW)
      convert h using 1
      ext i
      fin_cases i <;> simp [hv1, hv2, hv3]
    have e1 : (Pi.single 1 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 1)⁻¹ (W.sub_mem hvW (W.smul_mem (v 0) e0))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv1, hv2, hv3]
    refine ⟨2, by norm_num, le_antisymm (fun x hx => ?_) (flagSpace_le_of fun j hj => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj
      exacts [h2 x hx, h3 x hx]
    · fin_cases j <;> simp at hj
      exacts [e0, e1]
  push Not at h1
  by_cases h0 : ∃ v ∈ W, v 0 ≠ 0
  · obtain ⟨v, hvW, hv0⟩ := h0
    have e0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
      have h := W.smul_mem (v 0)⁻¹ hvW
      convert h using 1
      ext i
      fin_cases i <;> simp [hv0, h1 v hvW, h2 v hvW, h3 v hvW]
    refine ⟨1, by norm_num, le_antisymm (fun x hx => ?_) (flagSpace_le_of fun j hj => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj
      exacts [h1 x hx, h2 x hx, h3 x hx]
    · fin_cases j <;> simp at hj
      exact e0
  push Not at h0
  refine ⟨0, by norm_num, ?_⟩
  rw [LinearFlag.flagSpace_zero, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  ext i
  fin_cases i
  exacts [h0 x hx, h1 x hx, h2 x hx, h3 x hx]

theorem stab_of_normal_sp4 {Q O U : Subgroup (GL (Fin 4) K)} (hUQ : U ≤ Q)
    (hU : U ≤ uniGL 4 K) (hUN : ∀ a b c d : K, spN a b c d ∈ U) (hO1 : O ≠ ⊥) (hOU : O ≤ U)
    (hQN : Q ≤ Subgroup.normalizer (O : Set (GL (Fin 4) K))) :
    ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Q ≤ flagStab 4 m K := by
  classical
  let W : Submodule K (Fin 4 → K) :=
    { carrier := {v | ∀ o ∈ O, (o : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v}
      add_mem' := fun {v w} hv hw o ho => by rw [mulVec_add, hv o ho, hw o ho]
      zero_mem' := fun o _ => mulVec_zero _
      smul_mem' := fun c v hv o ho => by rw [mulVec_smul, hv o ho] }
  have hmemW : ∀ {v : Fin 4 → K}, v ∈ W ↔ ∀ o ∈ O, (o : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v :=
    Iff.rfl
  have hpres : ∀ g ∈ Subgroup.normalizer (O : Set (GL (Fin 4) K)), ∀ v ∈ W,
      (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v ∈ W := by
    intro g hg v hv
    rw [hmemW]
    intro o ho
    have h1 : g⁻¹ * o * g ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) o).mp ho
      simpa using this
    have h2 := hmemW.mp hv _ h1
    have h3 : (g : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ * o * g : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = (o : Matrix (Fin 4) (Fin 4) K) * g := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    calc (o : Matrix (Fin 4) (Fin 4) K) *ᵥ ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
        = (g : Matrix (Fin 4) (Fin 4) K) *ᵥ (((g⁻¹ * o * g : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by rw [mulVec_mulVec, mulVec_mulVec, h3]
      _ = (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v := by rw [h2]
  obtain ⟨m, -, hWm⟩ := eq_flagSpace_of_spInvariant fun a b c d v hv =>
    hpres (spN a b c d) (hQN (hUQ (hUN a b c d))) v hv
  have hcol : ∀ (M : Matrix (Fin 4) (Fin 4) K) (j i : Fin 4),
      (M *ᵥ Pi.single j 1) i = M i j := fun M j i => by
    rw [mulVec_single_one]
    rfl
  have he0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
    rw [hmemW]
    intro o ho
    obtain ⟨hlow, hdiag⟩ := uniGL_entries (hU (hOU ho))
    ext i
    rw [hcol]
    fin_cases i
    · simpa using hdiag 0
    · simpa using hlow 1 0 (by decide)
    · simpa using hlow 2 0 (by decide)
    · simpa using hlow 3 0 (by decide)
  have hWtop : ∃ v, v ∉ W := by
    by_contra h
    push Not at h
    apply hO1
    rw [eq_bot_iff]
    intro o ho
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext i j
    have h1 := congrFun (hmemW.mp (h (Pi.single j 1)) o ho) i
    rw [hcol] at h1
    rw [h1, Units.val_one, one_apply, Pi.single_apply]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [LinearFlag.flagSpace_zero] at hWm
    have h1 : (Pi.single 0 1 : Fin 4 → K) ∈ (⊥ : Submodule K (Fin 4 → K)) := hWm ▸ he0
    rw [Submodule.mem_bot] at h1
    have := congrFun h1 0
    simp at this
  have hm3 : m ≤ 3 := by
    by_contra hm
    obtain ⟨v, hv⟩ := hWtop
    apply hv
    rw [hWm, LinearFlag.mem_flagSpace]
    intro j hj
    have := j.2
    omega
  refine ⟨m, by omega, hm3, fun g hg => mem_flagStab.mpr fun i j hj hi => ?_⟩
  have h := hpres g (hQN hg) _ ((hWm ▸ single_mem_flagSpace hj : _ ∈ W))
  rw [hWm, LinearFlag.mem_flagSpace] at h
  have h' := h i hi
  rw [hcol] at h'
  exact h'

theorem map_succHom_sp {Q U : Subgroup (GL (Fin 4) K)}
    (hQ : ∀ g ∈ Q, ∀ i : Fin 3, (g : Matrix (Fin 4) (Fin 4) K) i.succ 0 = 0) (hUQ : U ≤ Q)
    (hU : U ≤ uniGL 4 K) (hUN : ∀ a b c d : K, spN a b c d ∈ U) :
    (U.subgroupOf Q).map (succHom hQ) = uni3 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hlow, hdiag⟩ := uniGL_entries (hU hu)
    exact mem_uniGL_of (fun i j hij => hlow _ _ (Fin.succ_lt_succ_iff.mpr hij))
      (fun i => hdiag i.succ)
  · intro v hv
    obtain ⟨hlow, hdiag⟩ := uni3_entries hv
    set x := (v : Matrix (Fin 3) (Fin 3) K) 0 1
    set y := (v : Matrix (Fin 3) (Fin 3) K) 1 2
    set z := (v : Matrix (Fin 3) (Fin 3) K) 0 2
    have hmem := hUN (-y) 0 z x
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    change succMat (spMat (-y) 0 z x) = (v : Matrix (Fin 3) (Fin 3) K)
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [succMat, spMat] using (hdiag 0).symm
    · simp [succMat, spMat, x]
    · simp [succMat, spMat, z]
    · simpa [succMat, spMat] using (hlow 1 0 (by decide)).symm
    · simpa [succMat, spMat] using (hdiag 1).symm
    · simp [succMat, spMat, y]
    · simpa [succMat, spMat] using (hlow 2 0 (by decide)).symm
    · simpa [succMat, spMat] using (hlow 2 1 (by decide)).symm
    · simpa [succMat, spMat] using (hdiag 2).symm

theorem map_topHom_three_sp {Q U : Subgroup (GL (Fin 4) K)} (hQ : Q ≤ flagStab 4 3 K)
    (hUQ : U ≤ Q) (hU : U ≤ uniGL 4 K) (hUN : ∀ a b c d : K, spN a b c d ∈ U) :
    (U.subgroupOf Q).map (topHom (by norm_num : 3 ≤ 4) hQ) = uni3 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hlow, hdiag⟩ := uniGL_entries (hU hu)
    exact mem_uniGL_of (fun i j hij => hlow _ _ (Fin.lt_def.mpr (Fin.lt_def.mp hij)))
      (fun i => hdiag _)
  · intro v hv
    obtain ⟨hlow, hdiag⟩ := uni3_entries hv
    set x := (v : Matrix (Fin 3) (Fin 3) K) 0 1
    set y := (v : Matrix (Fin 3) (Fin 3) K) 1 2
    set z := (v : Matrix (Fin 3) (Fin 3) K) 0 2
    have hmem := hUN x 0 (z - x * y) y
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    change topMat (by norm_num : 3 ≤ 4) (spMat x 0 (z - x * y) y) = (v : Matrix (Fin 3) (Fin 3) K)
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [topMat, spMat] using (hdiag 0).symm
    · simp [topMat, spMat, x]
    · simp [topMat, spMat, z]
    · simpa [topMat, spMat] using (hlow 1 0 (by decide)).symm
    · simpa [topMat, spMat] using (hdiag 1).symm
    · simp [topMat, spMat, y]
    · simpa [topMat, spMat] using (hlow 2 0 (by decide)).symm
    · simpa [topMat, spMat] using (hlow 2 1 (by decide)).symm
    · simpa [topMat, spMat] using (hdiag 2).symm

theorem map_topHom_two_sp {Q U : Subgroup (GL (Fin 4) K)} (hQ : Q ≤ flagStab 4 2 K)
    (hUQ : U ≤ Q) (hU : U ≤ uniGL 4 K) (hUN : ∀ a b c d : K, spN a b c d ∈ U) :
    (U.subgroupOf Q).map (topHom (by norm_num : 2 ≤ 4) hQ) = uni2 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hlow, hdiag⟩ := uniGL_entries (hU hu)
    refine mem_rootGL.mpr ⟨((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1, ?_⟩
    apply Units.ext
    change topMat (by norm_num : 2 ≤ 4) ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      transvection (0 : Fin 2) 1 _
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [topMat, transvection] using hdiag 0
    · simp [topMat, transvection]
    · simpa [topMat, transvection] using hlow 1 0 (by decide)
    · simpa [topMat, transvection] using hdiag 1
  · rintro _ ⟨c, rfl⟩
    have hmem := hUN (Multiplicative.toAdd c) 0 0 0
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    change topMat (by norm_num : 2 ≤ 4) (spMat (Multiplicative.toAdd c) 0 0 0) =
      transvection (0 : Fin 2) 1 (Multiplicative.toAdd c)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [topMat, spMat, transvection]

theorem map_le_borGL_three [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ}
    {Q B U : Subgroup (GL (Fin m) K)} (ψ : ↥Q →* GL (Fin 3) K) (hBQ : B ≤ Q) (hUQ : U ≤ Q)
    (hψU : (U.subgroupOf Q).map ψ = uni3 K) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin m) K)) * (U : Set (GL (Fin m) K)) = (U : Set (GL (Fin m) K)) * B) :
    (B.subgroupOf Q).map ψ ≤ borGL 3 K := by
  refine triangular_three hK ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab _ ha _ hb)
  · have h1 : Nat.card (B.subgroupOf Q) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
    exact Odd.of_dvd_nat (h1 ▸ hBodd) (Subgroup.card_map_dvd _ _)
  · rw [← hψU, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul,
      subgroupOf_mul_comm hBQ hUQ hBU]

theorem triangular_sp4 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {B U : Subgroup (GL (Fin 4) K)} (hU : U ≤ uniGL 4 K)
    (hUN : ∀ a b c d : K, spN a b c d ∈ U) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 4) K)) * (U : Set (GL (Fin 4) K)) =
      (U : Set (GL (Fin 4) K)) * B) :
    B ≤ borGL 4 K := by
  have hUp : IsPGroup 2 U := (isPGroup_uniGL 4).to_le hU
  have hU1 : U ≤ flagStab 4 1 K := hU.trans ((uniGL_le_borGL 4).trans (borGL_le_flagStab 4 1))
  have key : B ⊔ U ≤ flagStab 4 1 K → B ≤ borGL 4 K := by
    intro hQ
    have hQ' : ∀ g ∈ B ⊔ U, ∀ i : Fin 3,
        (g : Matrix (Fin 4) (Fin 4) K) i.succ 0 = 0 := fun g hg i =>
      mem_flagStab.mp (hQ hg) _ _ (by simp) (by simp)
    have hmap := map_le_borGL_three hK (succHom hQ') le_sup_left le_sup_right
      (map_succHom_sp hQ' le_sup_right hU hUN) hBab hBodd hBU
    intro b hb
    have hbQ : b ∈ B ⊔ U := le_sup_left (b := U) hb
    have hb' : succHom hQ' ⟨b, hbQ⟩ ∈ borGL 3 K := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
    rw [mem_borGL] at hb' ⊢
    intro i j hij
    cases i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact hQ' b hbQ i
      | succ j => exact hb' i j (Fin.succ_lt_succ_iff.mp hij)
  rcases exists_normal_or_le_normalizer hBab hBodd hUp hBU with ⟨O, hO1, hOU, hON⟩ | hN
  · obtain ⟨m, hm1, hm3, hQm⟩ := stab_of_normal_sp4 le_sup_right hU hUN hO1 hOU hON
    have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm with rfl | rfl | rfl
    · exact key hQm
    ·
      have hmap := map_le_borGL_two hK (topHom (by norm_num : 2 ≤ 4) hQm) le_sup_left
        le_sup_right (map_topHom_two_sp hQm le_sup_right hU hUN) hBab hBodd hBU
      have hB1 : B ≤ flagStab 4 1 K := by
        intro b hb
        have hbQ : b ∈ B ⊔ U := le_sup_left (b := U) hb
        have hb' := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
        rw [mem_borGL_two] at hb'
        have h2 := mem_flagStab.mp (hQm hbQ)
        refine mem_flagStab.mpr fun i j hj hi => ?_
        fin_cases j <;> simp at hj
        fin_cases i <;> simp at hi
        · exact hb'
        · exact h2 2 0 (by simp) (by simp)
        · exact h2 3 0 (by simp) (by simp)
      exact key (sup_le hB1 hU1)
    ·
      have hmap := map_le_borGL_three hK (topHom (by norm_num : 3 ≤ 4) hQm) le_sup_left
        le_sup_right (map_topHom_three_sp hQm le_sup_right hU hUN) hBab hBodd hBU
      intro b hb
      have hbQ : b ∈ B ⊔ U := le_sup_left (b := U) hb
      have hb' := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
      have h3 := mem_flagStab.mp (hQm hbQ)
      rw [mem_borGL] at hb' ⊢
      intro i j hij
      by_cases hi : (i : ℕ) < 3
      · have := hb' ⟨i, hi⟩ ⟨j, by have := Fin.lt_def.mp hij; omega⟩ (Fin.lt_def.mpr
          (Fin.lt_def.mp hij))
        exact this
      · exact h3 i j (by have := i.2; have := Fin.lt_def.mp hij; omega) (by omega)
  ·
    have hEU : rootGL (K := K) (0 : Fin 4) 3 (by decide) ≤ U := by
      rintro _ ⟨c, rfl⟩
      rw [trHom_apply, trGL_eq_spN]
      exact hUN _ _ _ _
    have hB1 : B ≤ flagStab 4 1 K := by
      refine le_of_commute (E := rootGL (0 : Fin 4) 3 (by decide)) (hEU.trans hN)
        rootGL_comm rootGL_mul_self (by rw [card_rootGL]; exact hK) hBodd ?_
      intro e he he1 b _ heb
      obtain ⟨c, rfl⟩ := mem_rootGL.mp he
      have hc0 := ne_zero_of_trGL_ne_one he1
      have h1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) heb
      simp only [Units.val_mul, coe_trGL] at h1
      obtain ⟨hr, -⟩ := entry_eq_zero_of_commute hc0 h1
      refine mem_flagStab.mpr fun i j hj hi => ?_
      fin_cases j <;> simp at hj
      exact hr i (fun h => by rw [h] at hi; simp at hi)
    exact key (sup_le hB1 hU1)

end Tri

end H

end CFSG.Quasithin
