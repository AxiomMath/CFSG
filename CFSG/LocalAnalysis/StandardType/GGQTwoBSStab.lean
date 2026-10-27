module

public import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def blockProd (a b m : ℕ) (h : a + b = m) :
    Su K 2 1 a × Su K 2 1 b →* Su K 2 1 m :=
  MonoidHom.noncommCoprod (blockEmb K 2 1 m a 0 (by omega)) (blockEmb K 2 1 m b a (by omega))
    fun A B => blockEmb_comm _ _ (Or.inl (by omega)) A B

@[expose] noncomputable def swapAt (m a : ℕ) (h : a + 2 ≤ m) : Su K 2 1 m :=
  blockEmb K 2 1 m 2 a h (rotSU (unitaryInvolution K 2 1))

variable {K}

theorem blockProd_apply {a b m : ℕ} (h : a + b = m) (A : Su K 2 1 a) (B : Su K 2 1 b) :
    blockProd K a b m h (A, B) =
      blockEmb K 2 1 m a 0 (by omega) A * blockEmb K 2 1 m b a (by omega) B :=
  rfl

private theorem bss_blockEmb_smul_single_blockIdx {m k i : ℕ} (h : i + k ≤ m)
    (A : Su K 2 1 k) (j : Fin k) :
    blockEmb K 2 1 m k i h A •
        (Pi.single (blockIdx i h j) 1 : Fin m → K) =
      fun x : Fin m =>
        if hx : i ≤ x.val ∧ x.val < i + k then
          (((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ
            (Pi.single j 1 : Fin k → K)) ⟨x.val - i, by omega⟩
        else 0 := by
  funext x
  rw [smul_def, coe_coe_blockEmb]
  by_cases hx : i ≤ x.val ∧ x.val < i + k
  · rw [dite_eq_left hx]
    have hx' : x = blockIdx i h ⟨x.val - i, by omega⟩ :=
      Fin.ext (by simp only [blockIdx_val]; omega)
    conv_lhs => rw [hx']
    rw [blockMat_mulVec_blockIdx]
    congr 1
    funext y
    by_cases hy : y = j
    · subst hy
      simp
    · have hne : blockIdx i h y ≠ blockIdx i h j :=
        fun h' => hy ((blockIdx_injective h) h')
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hy]
  · rw [dite_eq_right hx]
    rw [blockMat_mulVec_of_not_mem _ _ hx]
    have hxne : x ≠ blockIdx i h j := by
      intro h'
      apply hx
      rw [h']
      simp only [blockIdx_val]
      have := j.isLt
      omega
    rw [Pi.single_eq_of_ne hxne]

private theorem bss_blockEmb_eq_one_of_fixes_block {m k i : ℕ} (h : i + k ≤ m)
    (A : Su K 2 1 k)
    (hin : ∀ j : Fin k,
      blockEmb K 2 1 m k i h A • (Pi.single (blockIdx i h j) 1 : Fin m → K) =
        Pi.single (blockIdx i h j) 1) :
    blockEmb K 2 1 m k i h A = 1 := by
  have hmat : (((blockEmb K 2 1 m k i h A : Su K 2 1 m) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro x
    by_cases hx : i ≤ x.val ∧ x.val < i + k
    · have hxlt : x.val - i < k := by omega
      have hx' : x = blockIdx i h ⟨x.val - i, hxlt⟩ := by
        apply Fin.ext
        simp only [blockIdx_val]
        exact (Nat.add_sub_of_le hx.1).symm
      rw [hx', Matrix.one_mulVec]
      simpa only [smul_def] using hin ⟨x.val - i, hxlt⟩
    · have := blockEmb_smul_single_of_not_mem h A hx
      rw [Matrix.one_mulVec]
      simpa only [smul_def] using this
  exact Subtype.ext (Units.ext hmat)

private theorem bss_rotSU_mulVec_zero :
    (((rotSU (unitaryInvolution K 2 1) : SUid (unitaryInvolution K 2 1) 2) :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single (0 : Fin 2) 1 : Fin 2 → K) =
      Pi.single (1 : Fin 2) 1 := by
  funext x
  fin_cases x <;> simp [rotSU, rotMat, Matrix.mulVec, CharTwo.neg_eq]

private theorem bss_rotSU_mulVec_one :
    (((rotSU (unitaryInvolution K 2 1) : SUid (unitaryInvolution K 2 1) 2) :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single (1 : Fin 2) 1 : Fin 2 → K) =
      Pi.single (0 : Fin 2) 1 := by
  funext x
  fin_cases x <;> simp [rotSU, rotMat, Matrix.mulVec, CharTwo.neg_eq]

private theorem bss_blockEmb3_smul_single_of_block_single {c : ℕ} (B : Su K 2 1 3)
    (j k : Fin 3)
    (h : blockEmb K 2 1 (c + 3) 3 c (by omega) B •
        (Pi.single (blockIdx (m := c + 3) c (by omega) j) 1 : Fin (c + 3) → K) =
      Pi.single (blockIdx (m := c + 3) c (by omega) k) 1) :
    B • (Pi.single j 1 : Fin 3 → K) = Pi.single k 1 := by
  funext i
  have h' := congrFun h (blockIdx (m := c + 3) c (by omega) i)
  rw [bss_blockEmb_smul_single_blockIdx] at h'
  rw [smul_def]
  simpa [Matrix.mulVec_single_one, blockIdx_val, Nat.add_sub_cancel_left, Pi.single_apply,
    Fin.ext_iff] using h'

private theorem bss_su3_eq_one_of_fixes_one_two {B : Su K 2 1 3}
    (h1 : B • (Pi.single (1 : Fin 3) 1 : Fin 3 → K) = Pi.single (1 : Fin 3) 1)
    (h2 : B • (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1) :
    B = 1 := by
  set M : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hM1 : ∀ i, M i 1 = (Pi.single (1 : Fin 3) 1 : Fin 3 → K) i := by
    intro i
    have h := congrFun h1 i
    rw [smul_def, Matrix.mulVec_single_one] at h
    exact h
  have hM2 : ∀ i, M i 2 = (Pi.single (2 : Fin 3) 1 : Fin 3 → K) i := by
    intro i
    have h := congrFun h2 i
    rw [smul_def, Matrix.mulVec_single_one] at h
    exact h
  have hXX : conjTr (unitaryInvolution K 2 1) M * M = 1 := B.2.2
  have h10 : M 1 0 = 0 := by
    have h := congrFun (congrFun hXX 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    simpa [conjTr, hM1] using h
  have h20 : M 2 0 = 0 := by
    have h := congrFun (congrFun hXX 2) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    simpa [conjTr, hM2] using h
  have h00 : M 0 0 = 1 := by
    have hdet : M.det = 1 := B.2.1
    simpa [Matrix.det_fin_three, hM1, hM2, h10, h20] using hdet
  have hmat : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [Matrix.one_mulVec, Matrix.mulVec_single_one]
    funext j
    fin_cases i <;> fin_cases j <;> simp [M, hM1, hM2, h00, h10, h20]
  exact Subtype.ext (Units.ext hmat)

private theorem bss_mem_range_blockEmb_of_fixes_last_two {c : ℕ} {y : Su K 2 1 (c + 3)}
    (h1 : y • (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
      Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1)
    (h2 : y • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1) :
    y ∈ (blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega)).range := by
  rw [mem_range_blockEmb_iff]
  intro l hl
  have hlval : l.val = c + 1 ∨ l.val = c + 2 := by
    simp only [Nat.zero_add] at hl
    omega
  rcases hlval with h | h
  · have hl' : l = (⟨c + 1, by omega⟩ : Fin (c + 3)) := Fin.ext h
    rwa [hl']
  · have hl' : l = Fin.last (c + 2) := Fin.ext (by simpa [Fin.last] using h)
    rwa [hl']

private theorem bss_blockProd_eq_one {a b m : ℕ} (h : a + b = m)
    {A : Su K 2 1 a} {B : Su K 2 1 b}
    (hAB : blockProd K a b m h (A, B) = 1) : A = 1 ∧ B = 1 := by
  have h0a : 0 + a ≤ m := by omega
  have hab : a + b ≤ m := by omega
  let q := blockEmb K 2 1 m a 0 h0a A
  let p := blockEmb K 2 1 m b a hab B
  let e0 : Fin a → Fin m → K := fun j => Pi.single (blockIdx (m := m) 0 h0a j) 1
  let ea : Fin b → Fin m → K := fun j => Pi.single (blockIdx (m := m) a hab j) 1
  have hprod : q * p = 1 := by
    have := hAB
    rw [blockProd_apply] at this
    exact this
  have hcomm : q * p = p * q := blockEmb_comm _ _ (Or.inl (by omega)) A B
  have hpq : p * q = 1 := by
    rw [← hcomm]
    exact hprod
  have hq : q = 1 := by
    apply bss_blockEmb_eq_one_of_fixes_block (h := h0a) A
    intro j
    have hp : p • e0 j = e0 j :=
      blockEmb_smul_single_of_not_mem (m := m) (k := b) (i := a) hab B (by
        simp only [blockIdx_val]
        omega)
    have hfix : (q * p) • e0 j = e0 j := by rw [hprod, one_smul]
    rwa [mul_smul, hp] at hfix
  have hp : p = 1 := by
    apply bss_blockEmb_eq_one_of_fixes_block (h := hab) B
    intro j
    have hqfix : q • ea j = ea j :=
      blockEmb_smul_single_of_not_mem (m := m) (k := a) (i := 0) h0a A (by
        simp only [blockIdx_val]
        omega)
    have hfix : (p * q) • ea j = ea j := by rw [hpq, one_smul]
    rwa [mul_smul, hqfix] at hfix
  constructor
  · exact blockEmb_injective h0a (by simpa [q] using hq)
  · exact blockEmb_injective hab (by simpa [p] using hp)

private theorem bss_blockEmb3_pair_action_of_blockProd {c : ℕ}
    {A : Su K 2 1 c} {B : Su K 2 1 3}
    (h : (blockProd K c 3 (c + 3) rfl (A, B) •
          (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
        Pi.single (Fin.last (c + 2)) 1 ∧
      blockProd K c 3 (c + 3) rfl (A, B) •
          (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
        Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1) ∨
     (blockProd K c 3 (c + 3) rfl (A, B) •
          (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
        Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 ∧
      blockProd K c 3 (c + 3) rfl (A, B) •
          (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
        Pi.single (Fin.last (c + 2)) 1)) :
    (blockEmb K 2 1 (c + 3) 3 c (by omega) B •
        (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1 ∧
      blockEmb K 2 1 (c + 3) 3 c (by omega) B •
        (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
      Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1) ∨
    (blockEmb K 2 1 (c + 3) 3 c (by omega) B •
        (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 ∧
      blockEmb K 2 1 (c + 3) 3 c (by omega) B •
        (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1) := by
  have h0c : 0 + c ≤ c + 3 := by omega
  have hc3 : c + 3 ≤ c + 3 := by omega
  have hcomm : blockEmb K 2 1 (c + 3) c 0 h0c A *
      blockEmb K 2 1 (c + 3) 3 c hc3 B =
      blockEmb K 2 1 (c + 3) 3 c hc3 B *
        blockEmb K 2 1 (c + 3) c 0 h0c A :=
    blockEmb_comm _ _ (Or.inl (by omega)) A B
  have key : ∀ (j : Fin (c + 3)) (w : Fin (c + 3) → K), c ≤ (j : ℕ) →
      blockProd K c 3 (c + 3) rfl (A, B) • (Pi.single j 1 : Fin (c + 3) → K) = w →
      blockEmb K 2 1 (c + 3) 3 c hc3 B • (Pi.single j 1 : Fin (c + 3) → K) = w := by
    intro j w hj hw
    have hA : blockEmb K 2 1 (c + 3) c 0 h0c A • (Pi.single j 1 : Fin (c + 3) → K) =
        Pi.single j 1 :=
      blockEmb_smul_single_of_not_mem h0c A (by omega)
    rwa [blockProd_apply, hcomm, mul_smul, hA] at hw
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key _ _ (Nat.le_add_right c 2) h1, key _ _ (Nat.le_succ c) h2⟩
  · exact Or.inr ⟨key _ _ (Nat.le_add_right c 2) h1, key _ _ (Nat.le_succ c) h2⟩

theorem blockProd_injective {a b m : ℕ} (h : a + b = m) :
    Function.Injective (blockProd K a b m h) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ hEq
  have h1 : blockProd K a b m h (A * A'⁻¹, B * B'⁻¹) = 1 := by
    have hmul : (A * A'⁻¹, B * B'⁻¹) = (A, B) * (A', B')⁻¹ := rfl
    rw [hmul, map_mul, map_inv, hEq, mul_inv_cancel]
  obtain ⟨hA, hB⟩ := bss_blockProd_eq_one h h1
  exact Prod.ext (mul_inv_eq_one.mp hA) (mul_inv_eq_one.mp hB)

theorem swapAt_smul_single_left {m a : ℕ} (h : a + 2 ≤ m) :
    swapAt K m a h • (Pi.single (⟨a, by omega⟩ : Fin m) 1 : Fin m → K) =
      Pi.single (⟨a + 1, by omega⟩ : Fin m) 1 := by
  change blockEmb K 2 1 m 2 a h (rotSU (unitaryInvolution K 2 1)) •
      (Pi.single (blockIdx (m := m) a h (0 : Fin 2)) 1 : Fin m → K) =
    Pi.single (blockIdx (m := m) a h (1 : Fin 2)) 1
  rw [bss_blockEmb_smul_single_blockIdx]
  funext x
  by_cases hx : a ≤ x.val ∧ x.val < a + 2
  · rw [dite_eq_left hx]
    have hxval : x.val = a ∨ x.val = a + 1 := by omega
    have hxlt : x.val - a < 2 := by omega
    rcases hxval with hxval | hxval
    · have hx0 : (⟨x.val - a, hxlt⟩ : Fin 2) = 0 := by
        apply Fin.ext
        show x.val - a = 0
        omega
      have hxne : x ≠ blockIdx (m := m) a h (1 : Fin 2) := by
        intro h'
        rw [h'] at hxval
        simp only [blockIdx_val] at hxval
        omega
      rw [hx0, bss_rotSU_mulVec_zero, Pi.single_eq_of_ne hxne]
      simp
    · have hxeq : x = blockIdx (m := m) a h (1 : Fin 2) := by
        apply Fin.ext
        simp only [blockIdx_val]
        omega
      have hx1 : (⟨x.val - a, hxlt⟩ : Fin 2) = 1 := by
        apply Fin.ext
        show x.val - a = 1
        omega
      rw [hx1, bss_rotSU_mulVec_zero, hxeq, Pi.single_eq_same]
      simp
  · rw [dite_eq_right hx]
    have hxne : x ≠ blockIdx (m := m) a h (1 : Fin 2) := by
      intro h'
      apply hx
      rw [h']
      simp only [blockIdx_val]
      omega
    simp [Pi.single_eq_of_ne hxne]

theorem swapAt_smul_single_right {m a : ℕ} (h : a + 2 ≤ m) :
    swapAt K m a h • (Pi.single (⟨a + 1, by omega⟩ : Fin m) 1 : Fin m → K) =
      Pi.single (⟨a, by omega⟩ : Fin m) 1 := by
  change blockEmb K 2 1 m 2 a h (rotSU (unitaryInvolution K 2 1)) •
      (Pi.single (blockIdx (m := m) a h (1 : Fin 2)) 1 : Fin m → K) =
    Pi.single (blockIdx (m := m) a h (0 : Fin 2)) 1
  rw [bss_blockEmb_smul_single_blockIdx]
  funext x
  by_cases hx : a ≤ x.val ∧ x.val < a + 2
  · rw [dite_eq_left hx]
    have hxval : x.val = a ∨ x.val = a + 1 := by omega
    have hxlt : x.val - a < 2 := by omega
    rcases hxval with hxval | hxval
    · have hxeq : x = blockIdx (m := m) a h (0 : Fin 2) := by
        apply Fin.ext
        simp only [blockIdx_val]
        omega
      have hx0 : (⟨x.val - a, hxlt⟩ : Fin 2) = 0 := by
        apply Fin.ext
        show x.val - a = 0
        omega
      rw [hx0, bss_rotSU_mulVec_one, hxeq, Pi.single_eq_same]
      simp
    · have hx1 : (⟨x.val - a, hxlt⟩ : Fin 2) = 1 := by
        apply Fin.ext
        show x.val - a = 1
        omega
      have hxne : x ≠ blockIdx (m := m) a h (0 : Fin 2) := by
        intro h'
        rw [h'] at hxval
        simp only [blockIdx_val] at hxval
        omega
      rw [hx1, bss_rotSU_mulVec_one, Pi.single_eq_of_ne hxne]
      simp
  · rw [dite_eq_right hx]
    have hxne : x ≠ blockIdx (m := m) a h (0 : Fin 2) := by
      intro h'
      apply hx
      rw [h']
      simp only [blockIdx_val]
      omega
    simp [Pi.single_eq_of_ne hxne]

theorem swapAt_smul_single_of_ne {m a : ℕ} (h : a + 2 ≤ m) {l : Fin m} (hl : (l : ℕ) ≠ a)
    (hl' : (l : ℕ) ≠ a + 1) :
    swapAt K m a h • (Pi.single l 1 : Fin m → K) = Pi.single l 1 := by
  change blockEmb K 2 1 m 2 a h (rotSU (unitaryInvolution K 2 1)) •
      (Pi.single l 1 : Fin m → K) = Pi.single l 1
  exact blockEmb_smul_single_of_not_mem h (rotSU (unitaryInvolution K 2 1)) (by omega)

theorem mem_range_blockProd_of_smul_pair {c : ℕ} (x : Su K 2 1 (c + 3))
    (hx : (x • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) = Pi.single (Fin.last (c + 2)) 1 ∧
        x • (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1) ∨
      (x • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 ∧
        x • (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (Fin.last (c + 2)) 1)) :
    x ∈ (blockProd K (c + 1) 2 (c + 3) (by omega)).range := by
  rcases hx with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · have hmem : x ∈ (blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega)).range :=
      bss_mem_range_blockEmb_of_fixes_last_two h1 h2
    obtain ⟨A, hA⟩ := hmem
    refine ⟨(A, 1), ?_⟩
    rw [blockProd_apply, hA, map_one, mul_one]
  · let s := swapAt K (c + 3) (c + 1) (by omega)
    have hs1 : s • (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
        Pi.single (Fin.last (c + 2)) 1 := by
      simpa only [s, Fin.last] using
        swapAt_smul_single_left (m := c + 3) (a := c + 1) (by omega)
    have hs2 : s • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
        Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 := by
      simpa only [s, Fin.last] using
        swapAt_smul_single_right (m := c + 3) (a := c + 1) (by omega)
    have hy1 : (x * s) • (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
        Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 := by
      rw [mul_smul, hs1, h2]
    have hy2 : (x * s) • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
        Pi.single (Fin.last (c + 2)) 1 := by
      rw [mul_smul, hs2, h1]
    have hmem : x * s ∈ (blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega)).range :=
      bss_mem_range_blockEmb_of_fixes_last_two hy1 hy2
    obtain ⟨A, hA⟩ := hmem
    refine ⟨(A, (rotSU (unitaryInvolution K 2 1))⁻¹), ?_⟩
    rw [blockProd_apply, hA, map_inv]
    change (x * s) * s⁻¹ = x
    dsimp only [s]
    group

theorem mem_range_blockEmb_of_blockProd_smul_last {c : ℕ} {A : Su K 2 1 c} {B : Su K 2 1 3}
    (h : blockProd K c 3 (c + 3) rfl (A, B) • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1) :
    B ∈ (blockEmb K 2 1 3 2 0 (by norm_num)).range := by
  have h0c : 0 + c ≤ c + 3 := by omega
  have hc3 : c + 3 ≤ c + 3 := by omega
  have hcomm : blockEmb K 2 1 (c + 3) c 0 h0c A *
      blockEmb K 2 1 (c + 3) 3 c hc3 B =
      blockEmb K 2 1 (c + 3) 3 c hc3 B *
        blockEmb K 2 1 (c + 3) c 0 h0c A :=
    blockEmb_comm _ _ (Or.inl (by omega)) A B
  have hA : blockEmb K 2 1 (c + 3) c 0 h0c A •
      (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1 :=
    blockEmb_smul_single_of_not_mem h0c A (by
      simp only [Fin.val_last, Nat.zero_add]
      omega)
  have hB : blockEmb K 2 1 (c + 3) 3 c hc3 B •
      (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
      Pi.single (Fin.last (c + 2)) 1 := by
    have := h
    rw [blockProd_apply, hcomm, mul_smul, hA] at this
    exact this
  have hB2 : B • (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1 := by
    apply bss_blockEmb3_smul_single_of_block_single (c := c) (j := 2) (k := 2)
    simpa [blockIdx, Fin.last] using hB
  rw [mem_range_blockEmb_iff]
  intro l hl
  have hlval : l.val = 2 := by
    simp only [Nat.zero_add] at hl
    omega
  have hl' : l = (2 : Fin 3) := Fin.ext hlval
  rw [hl']
  exact hB2

theorem mem_range_blockEmb_of_blockProd_smul_pair {c : ℕ} {A : Su K 2 1 c} {B : Su K 2 1 3}
    (h : (blockProd K c 3 (c + 3) rfl (A, B) • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
          Pi.single (Fin.last (c + 2)) 1 ∧
        blockProd K c 3 (c + 3) rfl (A, B) •
            (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1) ∨
      (blockProd K c 3 (c + 3) rfl (A, B) • (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 ∧
        blockProd K c 3 (c + 3) rfl (A, B) •
            (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (Fin.last (c + 2)) 1)) :
    B ∈ (blockEmb K 2 1 3 2 1 (by norm_num)).range := by
  have hBpair := bss_blockEmb3_pair_action_of_blockProd h
  let e1m : Fin (c + 3) → K := Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1
  let e2m : Fin (c + 3) → K := Pi.single (Fin.last (c + 2)) 1
  rcases hBpair with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · have hb1 : B • (Pi.single (1 : Fin 3) 1 : Fin 3 → K) = Pi.single (1 : Fin 3) 1 := by
      apply bss_blockEmb3_smul_single_of_block_single (c := c) (j := 1) (k := 1)
      simpa [e1m, blockIdx] using h1
    have hb2 : B • (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1 := by
      apply bss_blockEmb3_smul_single_of_block_single (c := c) (j := 2) (k := 2)
      simpa [e2m, blockIdx, Fin.last] using h2
    have hBone : B = 1 := bss_su3_eq_one_of_fixes_one_two hb1 hb2
    rw [hBone]
    exact (blockEmb K 2 1 3 2 1 (by norm_num)).range.one_mem
  · have hb1 : B • (Pi.single (1 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1 := by
      apply bss_blockEmb3_smul_single_of_block_single (c := c) (j := 1) (k := 2)
      simpa [e1m, e2m, blockIdx, Fin.last] using h1
    have hb2 : B • (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (1 : Fin 3) 1 := by
      apply bss_blockEmb3_smul_single_of_block_single (c := c) (j := 2) (k := 1)
      simpa [e2m, e1m, blockIdx, Fin.last] using h2
    have hs1 : swapAt K 3 1 (by omega) •
        (Pi.single (1 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1 := by
      simpa using swapAt_smul_single_left (m := 3) (a := 1) (by omega)
    have hs2 : swapAt K 3 1 (by omega) •
        (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (1 : Fin 3) 1 := by
      simpa using swapAt_smul_single_right (m := 3) (a := 1) (by omega)
    have hC1 : (B * swapAt K 3 1 (by omega)) •
        (Pi.single (1 : Fin 3) 1 : Fin 3 → K) = Pi.single (1 : Fin 3) 1 := by
      rw [mul_smul, hs1, hb2]
    have hC2 : (B * swapAt K 3 1 (by omega)) •
        (Pi.single (2 : Fin 3) 1 : Fin 3 → K) = Pi.single (2 : Fin 3) 1 := by
      rw [mul_smul, hs2, hb1]
    have hCone : B * swapAt K 3 1 (by omega) = 1 :=
      bss_su3_eq_one_of_fixes_one_two hC1 hC2
    have hBinv : B = (swapAt K 3 1 (by omega))⁻¹ := eq_inv_of_mul_eq_one_left hCone
    have hs : swapAt K 3 1 (by omega) ∈ (blockEmb K 2 1 3 2 1 (by norm_num)).range :=
      ⟨rotSU (unitaryInvolution K 2 1), rfl⟩
    rw [hBinv]
    exact Subgroup.inv_mem _ hs

end CFSG.StandardType.QTwo

end
