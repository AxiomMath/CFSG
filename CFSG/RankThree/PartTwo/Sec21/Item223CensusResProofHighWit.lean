module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

structure HighInv (Y : Type) [Group Y] : Prop where
  elem : ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 ∧
    E ⊓ Subgroup.center Y = ⊥
  nine : ∃ g : Y, orderOf g = 9
  card : 10 ^ 13 ≤ Nat.card Y

namespace Item223CensusResProof

section Roots

variable {K : Type*} [Field K]

@[expose] def zpow3 (ω : K) (t : ZMod 3) : K := ω ^ t.val

theorem zpow3_add {ω : K} (hω : ω ^ 3 = 1) (s t : ZMod 3) :
    zpow3 ω (s + t) = zpow3 ω s * zpow3 ω t := by
  unfold zpow3
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (s.val + t.val) 3, pow_add, pow_mul, hω, one_pow, mul_one]

theorem zpow3_zero (ω : K) : zpow3 ω 0 = 1 := by
  simp [zpow3]

theorem sq_ne_one_of_cube {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h2
  apply hω1
  rw [pow_succ, h2, one_mul] at hω
  exact hω

theorem zpow3_eq_one_iff {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {t : ZMod 3} :
    zpow3 ω t = 1 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ zpow3_zero ω⟩
  fin_cases t
  · rfl
  · exfalso
    apply hω1
    have h' : ω ^ 1 = 1 := h
    rwa [pow_one] at h'
  · exfalso
    exact sq_ne_one_of_cube hω hω1 h

theorem exists_cube_root {K : Type*} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨u, hu3⟩ := exists_prime_orderOf_dvd_card' 3 hu
  refine ⟨u, ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu3, pow_orderOf_eq_one, Units.val_one]
  · have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu3
    norm_num at hu3

end Roots

section Six

variable {K : Type} [Field K] {ω : K}

abbrev Six : Type := Fin 3 ⊕ Fin 3

@[expose] def diag6 (ω : K) (a : Fin 4 → ZMod 3) : Matrix Six Six K :=
  Matrix.diagonal (Sum.elim ![zpow3 ω (a 0), zpow3 ω (a 1), zpow3 ω (a 2)]
    ![zpow3 ω (a 3), zpow3 ω (2 * (a 0 + a 1 + a 2 + a 3)), 1])

theorem det_diag6 (hω : ω ^ 3 = 1) (a : Fin 4 → ZMod 3) : (diag6 ω a).det = 1 := by
  rw [diag6, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp only [Fin.prod_univ_three, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  rw [mul_one, ← zpow3_add hω (a 0) (a 1), ← zpow3_add hω, ← zpow3_add hω (a 3),
    ← zpow3_add hω]
  have h3 : ∀ x : ZMod 3, x + 2 * x = 0 := by decide
  have : a 0 + a 1 + a 2 + (a 3 + 2 * (a 0 + a 1 + a 2 + a 3)) = 0 := by
    rw [← h3 (a 0 + a 1 + a 2 + a 3)]
    ring
  rw [this, zpow3_zero]

theorem diag6_add (hω : ω ^ 3 = 1) (a b : Fin 4 → ZMod 3) :
    diag6 ω (a + b) = diag6 ω a * diag6 ω b := by
  rw [diag6, diag6, diag6, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, Pi.add_apply,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact zpow3_add hω _ _
  · exact zpow3_add hω _ _
  · exact zpow3_add hω _ _
  · exact zpow3_add hω _ _
  · rw [← zpow3_add hω]
    congr 1
    ring
  · rw [mul_one]

theorem diag6_zero : diag6 ω 0 = 1 := by
  rw [diag6, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [zpow3_zero, mul_zero]

@[expose] noncomputable def diagHom (hω : ω ^ 3 = 1) :
    Multiplicative (Fin 4 → ZMod 3) →* SpecialLinearGroup Six K where
  toFun a := ⟨diag6 ω a.toAdd, det_diag6 hω _⟩
  map_one' := Subtype.ext diag6_zero
  map_mul' a b := Subtype.ext (diag6_add hω a.toAdd b.toAdd)

theorem diagHom_injective (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Function.Injective (diagHom hω) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have h := congrArg (fun A : SpecialLinearGroup Six K => (A : Matrix Six Six K)) ha
  have hent : ∀ i, (diag6 ω a.toAdd) i i = 1 := fun i => by
    have h' := congrFun (congrFun h i) i
    change diag6 ω a.toAdd i i = ((1 : SpecialLinearGroup Six K) : Matrix Six Six K) i i at h'
    rw [h']
    simp
  have h0 := hent (Sum.inl 0)
  have h1 := hent (Sum.inl 1)
  have h2 := hent (Sum.inl 2)
  have h3 := hent (Sum.inr 0)
  simp only [diag6, Matrix.diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val] at h0 h1 h2 h3
  rw [zpow3_eq_one_iff hω hω1] at h0 h1 h2 h3
  rw [Subgroup.mem_bot]
  change a = Multiplicative.ofAdd 0
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> assumption

@[expose] noncomputable def diagE (hω : ω ^ 3 = 1) : Subgroup (SpecialLinearGroup Six K) :=
  (diagHom hω).range

theorem card_diagE (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : Nat.card (diagE hω) = 81 := by
  rw [diagE, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (diagHom_injective hω hω1), Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
  rfl

theorem isElemAbelian_diagE (hω : ω ^ 3 = 1) : CFSG.Assembly.IsElemAbelian 3 (diagE hω) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : SpecialLinearGroup Six K) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      change 3 • a.toAdd i = 0
      rw [nsmul_eq_mul]
      have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
      rw [h3, zero_mul]
    rw [this, map_one]

theorem diagE_inf_center (hω : ω ^ 3 = 1) :
    diagE hω ⊓ Subgroup.center (SpecialLinearGroup Six K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨a, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (Sum.inr 2)
  have h1 : ((diagHom hω a : SpecialLinearGroup Six K) : Matrix Six Six K)
      (Sum.inr 2) (Sum.inr 2) = 1 := by
    change diag6 ω a.toAdd (Sum.inr 2) (Sum.inr 2) = 1
    simp [diag6]
  rw [h1, map_one] at hs
  exact Subtype.ext hs.symm

@[expose] def monoC (ω : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, ω; 1, 0, 0; 0, 1, 0]

theorem monoC_cube (ω : K) : monoC ω ^ 3 = Matrix.scalar (Fin 3) ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monoC, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_monoC (ω : K) : (monoC ω).det = ω := by
  simp [monoC, Matrix.det_fin_three]

@[expose] def diagD (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![ω ^ 2, 1, 1]

theorem diagD_cube (hω : ω ^ 3 = 1) : diagD ω ^ 3 = 1 := by
  rw [diagD, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change (ω ^ 2) ^ 3 = 1
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow]
  · simp
  · simp

theorem det_diagD (ω : K) : (diagD ω).det = ω ^ 2 := by
  simp [diagD, Matrix.det_diagonal, Fin.prod_univ_three]

theorem fromBlocks_zero_pow {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] (A : Matrix m m K) (D : Matrix l l K) (k : ℕ) :
    Matrix.fromBlocks A 0 0 D ^ k = Matrix.fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]

@[expose] def g6 (ω : K) : Matrix Six Six K := Matrix.fromBlocks (monoC ω) 0 0 (diagD ω)

theorem det_g6 (hω : ω ^ 3 = 1) : (g6 ω).det = 1 := by
  rw [g6, Matrix.det_fromBlocks_zero₂₁, det_monoC, det_diagD, ← pow_succ', hω]

theorem g6_cube (hω : ω ^ 3 = 1) :
    g6 ω ^ 3 = Matrix.fromBlocks (Matrix.scalar (Fin 3) ω) 0 0 1 := by
  rw [g6, fromBlocks_zero_pow, monoC_cube, diagD_cube hω]

@[expose] noncomputable def gSL (hω : ω ^ 3 = 1) : SpecialLinearGroup Six K :=
  ⟨g6 ω, det_g6 hω⟩

theorem gSL_pow_nine (hω : ω ^ 3 = 1) : gSL hω ^ 9 = 1 := by
  apply Subtype.ext
  change g6 ω ^ (3 * 3) = 1
  rw [pow_mul, g6_cube hω, fromBlocks_zero_pow, ← map_pow, hω, map_one, one_pow,
    Matrix.fromBlocks_one]

theorem gSL_cube_not_mem_center (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    gSL hω ^ 3 ∉ Subgroup.center (SpecialLinearGroup Six K) := by
  intro hc
  have h1 := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (Sum.inl 0)
  have hval : ((gSL hω ^ 3 : SpecialLinearGroup Six K) : Matrix Six Six K) =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) ω) 0 0 1 := g6_cube hω
  rw [hval] at h1
  have h2 := congrFun (congrFun h1 (Sum.inr 0)) (Sum.inr 0)
  simp at h2
  exact hω1 h2

theorem gSL_cube_ne_one (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : gSL hω ^ 3 ≠ 1 := fun h =>
  gSL_cube_not_mem_center hω hω1 (h ▸ Subgroup.one_mem _)

theorem orderOf_gSL (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : orderOf (gSL hω) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime_pow (p := 3) (n := 1) (by rw [pow_one]; exact gSL_cube_ne_one hω hω1)
    (by norm_num; exact gSL_pow_nine hω)

end Six

section Block

variable {K : Type} [Field K] {n : ℕ}

@[expose] def blockEquiv (hn : 6 ≤ n) : Six ⊕ Fin (n - 6) ≃ Fin n :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[expose] def blockMat (hn : 6 ≤ n) (A : Matrix Six Six K) : Matrix (Fin n) (Fin n) K :=
  Matrix.reindex (blockEquiv hn) (blockEquiv hn) (Matrix.fromBlocks A 0 0 1)

theorem blockMat_mul (hn : 6 ≤ n) (A B : Matrix Six Six K) :
    blockMat hn (A * B) = blockMat hn A * blockMat hn B := by
  rw [blockMat, blockMat, blockMat, ← Matrix.coe_reindexRingEquiv, ← map_mul,
    Matrix.fromBlocks_multiply]
  simp

theorem det_blockMat (hn : 6 ≤ n) (A : Matrix Six Six K) : (blockMat hn A).det = A.det := by
  unfold blockMat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMat_one (hn : 6 ≤ n) : blockMat hn (1 : Matrix Six Six K) = 1 := by
  unfold blockMat
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[expose] noncomputable def blockSL (hn : 6 ≤ n) :
    SpecialLinearGroup Six K →* SpecialLinearGroup (Fin n) K where
  toFun A := ⟨blockMat hn (A : Matrix Six Six K), (det_blockMat hn _).trans A.2⟩
  map_one' := Subtype.ext (blockMat_one hn)
  map_mul' A B := Subtype.ext (blockMat_mul hn (A : Matrix Six Six K) B)

theorem blockSL_apply (hn : 6 ≤ n) (A : SpecialLinearGroup Six K) (i j : Six) :
    (blockSL hn A : Matrix (Fin n) (Fin n) K) (blockEquiv hn (Sum.inl i))
      (blockEquiv hn (Sum.inl j)) = (A : Matrix Six Six K) i j := by
  change blockMat hn (A : Matrix Six Six K) _ _ = _
  simp [blockMat, Matrix.reindex_apply]

theorem blockSL_injective (hn : 6 ≤ n) : Function.Injective (blockSL (K := K) hn) := by
  intro A B h
  apply Subtype.ext
  ext i j
  rw [← blockSL_apply hn A i j, ← blockSL_apply hn B i j, h]

theorem mem_center_of_blockSL (hn : 6 ≤ n) {A : SpecialLinearGroup Six K}
    (h : blockSL hn A ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    A ∈ Subgroup.center (SpecialLinearGroup Six K) := by
  rw [Subgroup.mem_center_iff]
  intro B
  apply blockSL_injective hn
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp h (blockSL hn B)

end Block

section Witness

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem isElemAbelian_map_hom {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : CFSG.Assembly.IsElemAbelian 3 (B.map f) :=
  CFSG.Open.IsElemAbelian.map hB _

theorem four_le_card (h : 3 ∣ Nat.card K - 1) : 4 ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k
  · omega
  · omega

theorem card_projectiveSL_ge (hn : 6 ≤ n) (hq : 4 ≤ Nat.card K) :
    10 ^ 13 ≤ Nat.card (projectiveSL n K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set q := Fintype.card K with hqdef
  have hqN : Nat.card K = q := Nat.card_eq_fintype_card
  rw [hqN] at hq
  have hGL : q ^ ((n - 1) * n) ≤ Nat.card (GL (Fin n) K) := by
    rw [Matrix.card_GL_field]
    calc q ^ ((n - 1) * n) = ∏ _i : Fin n, q ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
          refine Finset.prod_le_prod (fun i _ => ?_)
          have hi : (i : ℕ) ≤ n - 1 := by omega
          have h1 : q ^ (i : ℕ) ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) hi
          have h2 : q ^ n = q * q ^ (n - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          have h3 : 2 * q ^ (n - 1) ≤ q * q ^ (n - 1) := Nat.mul_le_mul_right _ (by omega)
          omega
  have hSL := Matrix.card_SL_mul_card_units (n := Fin n) (R := K)
  have hP : Nat.card (SpecialLinearGroup (Fin n) K) =
      Nat.card (projectiveSL n K) * Nat.card (scalars n K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n K)
  have hZ : Nat.card (scalars n K) ≤ q := by
    rw [← hqN]
    refine Nat.card_le_card_of_injective
      (fun A : scalars n K => ((A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        ⟨0, by omega⟩ ⟨0, by omega⟩) fun A B hAB => ?_
    have hAc : (A : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center]; exact A.2
    have hBc : (B : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center]; exact B.2
    have hA := SpecialLinearGroup.scalar_eq_self_of_mem_center hAc (⟨0, by omega⟩ : Fin n)
    have hB := SpecialLinearGroup.scalar_eq_self_of_mem_center hBc (⟨0, by omega⟩ : Fin n)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hA, ← hB]
    exact congrArg _ hAB
  have hU : Nat.card Kˣ ≤ q := by
    rw [Nat.card_units, hqN]
    omega
  have hle : q ^ ((n - 1) * n) ≤ Nat.card (projectiveSL n K) * q * q := by
    calc q ^ ((n - 1) * n) ≤ Nat.card (GL (Fin n) K) := hGL
      _ = Nat.card (projectiveSL n K) * Nat.card (scalars n K) * Nat.card Kˣ := by
          rw [← hSL, hP]
      _ ≤ Nat.card (projectiveSL n K) * q * q := by
          gcongr
  have h30 : 30 ≤ (n - 1) * n := Nat.mul_le_mul (show 5 ≤ n - 1 by omega) hn
  have hexp : (n - 1) * n = ((n - 1) * n - 2) + 2 := by omega
  rw [hexp, pow_add, sq, ← mul_assoc] at hle
  have hle' : q ^ ((n - 1) * n - 2) ≤ Nat.card (projectiveSL n K) :=
    Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right hle (by omega)) (by omega)
  have h28 : 28 ≤ (n - 1) * n - 2 := by omega
  calc 10 ^ 13 ≤ 4 ^ 28 := by norm_num
    _ ≤ q ^ 28 := Nat.pow_le_pow_left hq 28
    _ ≤ q ^ ((n - 1) * n - 2) := Nat.pow_le_pow_right (by omega) h28
    _ ≤ Nat.card (projectiveSL n K) := hle'

theorem highInv_SL (hn : 6 ≤ n) (hK : 3 ∣ Nat.card K - 1) :
    HighInv (SpecialLinearGroup (Fin n) K) := by
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root hK
  refine ⟨⟨(diagE hω).map (blockSL hn), isElemAbelian_map_hom _ (isElemAbelian_diagE hω), ?_,
    ?_⟩, ⟨blockSL hn (gSL hω), ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective (blockSL_injective hn), card_diagE hω hω1]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨y, hy, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    have hy1 : y ∈ diagE hω ⊓ Subgroup.center (SpecialLinearGroup Six K) :=
      Subgroup.mem_inf.mpr ⟨hy, mem_center_of_blockSL hn hc⟩
    rw [diagE_inf_center hω, Subgroup.mem_bot] at hy1
    rw [hy1, map_one]
    exact Subgroup.one_mem _
  · rw [orderOf_injective _ (blockSL_injective hn), orderOf_gSL hω hω1]
  · have h1 := card_projectiveSL_ge (K := K) hn (four_le_card hK)
    have h2 : Nat.card (projectiveSL n K) ≤ Nat.card (SpecialLinearGroup (Fin n) K) := by
      have : Fintype K := Fintype.ofFinite K
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n K)
      rw [this]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    omega

omit [Finite K] in
theorem isSimpleGroup_projectiveSL' (hn : 3 ≤ n) : IsSimpleGroup (projectiveSL n K) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega)
    (Or.inl hn)).2.1
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    n K).symm.isSimpleGroup

theorem highInv_projectiveSL (hn : 6 ≤ n) (hK : 3 ∣ Nat.card K - 1) :
    HighInv (projectiveSL n K) := by
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root hK
  set E := (diagE hω).map (blockSL (K := K) hn)
  have hEZ : E ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨y, hy, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    have hy1 : y ∈ diagE hω ⊓ Subgroup.center (SpecialLinearGroup Six K) :=
      Subgroup.mem_inf.mpr ⟨hy, mem_center_of_blockSL hn hc⟩
    rw [diagE_inf_center hω, Subgroup.mem_bot] at hy1
    rw [hy1, map_one]
    exact Subgroup.one_mem _
  set φ := (proj n K).comp E.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_proj,
      scalars_eq_center] at hx
    have h1 : (x : SpecialLinearGroup (Fin n) K) ∈ E ⊓ Subgroup.center _ :=
      Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [hEZ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have hs := isSimpleGroup_projectiveSL' (K := K) (n := n) (by omega)
  have hZ : Subgroup.center (projectiveSL n K) = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (projectiveSL n K))).resolve_right fun htop => ?_
    have hg : proj n K (blockSL hn (gSL hω)) ∈ Subgroup.center (projectiveSL n K) :=
      htop ▸ Subgroup.mem_top _
    have hcomm : IsMulCommutative (projectiveSL n K) := ⟨⟨fun a b =>
      Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩
    have hp := Group.is_simple_iff_prime_card.mp hs
    have h9 : 9 ∣ Nat.card (projectiveSL n K) := by
      have h1 : orderOf (proj n K (blockSL hn (gSL hω))) = 9 := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
        · rw [pow_one, ← map_pow, ← map_pow, ← MonoidHom.mem_ker, ker_proj, scalars_eq_center]
          exact fun h => gSL_cube_not_mem_center hω hω1 (mem_center_of_blockSL hn h)
        · norm_num
          rw [← map_pow, ← map_pow, gSL_pow_nine hω, map_one, map_one]
      rw [← h1]
      exact orderOf_dvd_natCard _
    have h3 : 3 ∣ Nat.card (projectiveSL n K) := (Dvd.intro 3 rfl).trans h9
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hp] at h3
    rw [← h3] at h9
    norm_num at h9
  refine ⟨⟨φ.range, ?_, ?_, ?_⟩, ⟨proj n K (blockSL hn (gSL hω)), ?_⟩,
    card_projectiveSL_ge hn (four_le_card hK)⟩
  · rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact isElemAbelian_map_hom _ (isElemAbelian_map_hom _ (isElemAbelian_diagE hω))
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
      Subgroup.card_map_of_injective (blockSL_injective hn), card_diagE hω hω1]
  · rw [hZ, inf_bot_eq]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
    · rw [pow_one, ← map_pow, ← map_pow, ← MonoidHom.mem_ker, ker_proj, scalars_eq_center]
      exact fun h => gSL_cube_not_mem_center hω hω1 (mem_center_of_blockSL hn h)
    · norm_num
      rw [← map_pow, ← map_pow, gSL_pow_nine hω, map_one, map_one]

end Witness

end Item223CensusResProof

end CFSG.RankThree.PartTwo.Sec21
