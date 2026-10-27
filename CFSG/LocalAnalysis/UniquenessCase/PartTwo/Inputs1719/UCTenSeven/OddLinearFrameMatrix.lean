module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearGeometry
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Matrix
open CFSG.LocalAnalysis.UniquenessCase.UC22 (linearFrameBlock linearFrameInvolution)
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open CFSG.ClassicalInvolution.Phan (blockSel blockIdx blockMat blockIdx_val blockMat_apply
  blockMat_apply_blockIdx blockSel_apply blockSel_transpose_mul_self)
open scoped MatrixGroups commutatorElement

private theorem eq_zero_of_neg_eq_self {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    {x : F} (h : -x = x) : x = 0 := by
  have h' : x + x = 0 := by linear_combination -h
  have h2x : (2 : F) * x = 0 := by rw [two_mul]; exact h'
  exact (mul_eq_zero.mp h2x).resolve_left h2

private theorem mem_pair_iff {m tail : ℕ} (k : Fin (m + 1))
    (a : Fin (2 * m + 1 + 1 + tail)) :
    (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) ↔ a.val / 2 = k.val := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · intro h
    have h' := (Nat.div_eq_iff (k := 2) (x := a.val) (y := k.val) (by norm_num)).mp h
    omega

private theorem coe_linearFrameInvolution_diagonal {F : Type} [Field F] {m tail : ℕ}
    (k : Fin (m + 1)) :
    (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) =
      Matrix.diagonal (fun a : Fin (2 * m + 1 + 1 + tail) =>
        if 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2 then (-1 : F) else 1) := by
  rw [linearFrameInvolution, CFSG.ClassicalInvolution.Models.coe_blockSL_neg_one (by omega)]
  exact CFSG.ClassicalInvolution.Models.negBlock_eq_diagonal _ _

private theorem eq_zero_of_commute_frameInvolution {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) {m tail : ℕ} (htail : tail ≤ 1)
    {u : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F}
    (hu : ∀ k : Fin (m + 1),
      u * (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) =
      (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) * u)
    {a b : Fin (2 * m + 1 + 1 + tail)} (hab : a.val / 2 ≠ b.val / 2) :
    u a b = 0 := by
  have hhalf : ∀ x : Fin (2 * m + 1 + 1 + tail), x.val / 2 ≤ m + 1 := by
    intro x
    have hx := x.isLt
    exact Nat.div_le_of_le_mul (k := 2) (n := m + 1) (by omega)
  rcases lt_or_gt_of_ne hab with h | h
  ·
    set k : Fin (m + 1) := ⟨a.val / 2, by have := hhalf a; omega⟩ with hk
    have hka : a.val / 2 = k.val := rfl
    have hkb : b.val / 2 ≠ k.val := by
      simp only [hk, Fin.val_mk]
      omega
    have hmem_a : 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2 := (mem_pair_iff k a).mpr hka
    have hmem_b : ¬ (2 * k.val ≤ b.val ∧ b.val < 2 * k.val + 2) :=
      fun hc => hkb ((mem_pair_iff k b).mp hc)
    have hentry := congrFun (congrFun (hu k) a) b
    rw [coe_linearFrameInvolution_diagonal] at hentry
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    rw [ite_eq_right hmem_b, ite_eq_left hmem_a, mul_one, neg_one_mul] at hentry
    exact eq_zero_of_neg_eq_self h2 hentry.symm
  ·
    set k : Fin (m + 1) := ⟨b.val / 2, by have := hhalf b; omega⟩ with hk
    have hkb : b.val / 2 = k.val := rfl
    have hka : a.val / 2 ≠ k.val := by
      simp only [hk, Fin.val_mk]
      omega
    have hmem_b : 2 * k.val ≤ b.val ∧ b.val < 2 * k.val + 2 := (mem_pair_iff k b).mpr hkb
    have hmem_a : ¬ (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) :=
      fun hc => hka ((mem_pair_iff k a).mp hc)
    have hentry := congrFun (congrFun (hu k) a) b
    rw [coe_linearFrameInvolution_diagonal] at hentry
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    rw [ite_eq_left hmem_b, ite_eq_right hmem_a, mul_neg, mul_one, one_mul] at hentry
    exact eq_zero_of_neg_eq_self h2 hentry

private theorem mul_blockSel_apply {F : Type} [Field F] {N i : ℕ} (hi : i + 2 ≤ N)
    (A : Matrix (Fin N) (Fin N) F) (a : Fin N) (w : Fin 2) :
    (A * blockSel F N 2 i) a w = A a (blockIdx i hi w) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (blockIdx i hi w)]
  · simp [blockSel_apply, blockIdx_val]
  · intro z _ hz
    have h : z.val ≠ i + w.val := fun h => hz (Fin.ext (by simpa [blockIdx_val] using h))
    simp [blockSel_apply, h]
  · simp

private theorem blockSel_transpose_mul_apply {F : Type} [Field F] {N n i : ℕ} (hi : i + 2 ≤ N)
    (A : Matrix (Fin N) (Fin n) F) (w : Fin 2) (b : Fin n) :
    ((blockSel F N 2 i)ᵀ * A) w b = A (blockIdx i hi w) b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (blockIdx i hi w)]
  · simp [Matrix.transpose_apply, blockSel_apply, blockIdx_val]
  · intro z _ hz
    have h : z.val ≠ i + w.val := fun h => hz (Fin.ext (by simpa [blockIdx_val] using h))
    simp [Matrix.transpose_apply, blockSel_apply, h]
  · simp

private theorem blockSel_conj_apply {F : Type} [Field F] {N i : ℕ} (hi : i + 2 ≤ N)
    (A : Matrix (Fin N) (Fin N) F) (x y : Fin 2) :
    ((blockSel F N 2 i)ᵀ * A * blockSel F N 2 i) x y =
      A (blockIdx i hi x) (blockIdx i hi y) := by
  have h1 := blockSel_transpose_mul_apply hi (A * blockSel F N 2 i) x y
  have h2 := mul_blockSel_apply hi A (blockIdx i hi x) y
  calc ((blockSel F N 2 i)ᵀ * A * blockSel F N 2 i) x y
      = ((blockSel F N 2 i)ᵀ * (A * blockSel F N 2 i)) x y := by
        rw [Matrix.mul_assoc]
    _ = (A * blockSel F N 2 i) (blockIdx i hi x) y := h1
    _ = A (blockIdx i hi x) (blockIdx i hi y) := h2

private theorem block_commute_of_mul_blockMat {F : Type} [Field F] {N i : ℕ} (hi : i + 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) F} {B : Matrix (Fin 2) (Fin 2) F}
    (h : A * blockMat N i B = blockMat N i B * A) :
    ((blockSel F N 2 i)ᵀ * A * blockSel F N 2 i) * B =
      B * ((blockSel F N 2 i)ᵀ * A * blockSel F N 2 i) := by
  set L : Matrix (Fin N) (Fin 2) F := blockSel F N 2 i with hL
  have hLL : Lᵀ * L = 1 := blockSel_transpose_mul_self hi
  have hBL : blockMat N i B = 1 + L * (B - 1) * Lᵀ := rfl
  have key : (Lᵀ * A * L) * B = B * (Lᵀ * A * L) := by
    have hc := congrArg (fun M => Lᵀ * M * L) h
    rw [hBL] at hc
    have hcancel : ∀ X : Matrix (Fin 2) (Fin 2) F, X * Lᵀ * L = X := by
      intro X
      rw [Matrix.mul_assoc, hLL, Matrix.mul_one]
    have h1 : Lᵀ * (A * (1 + L * (B - 1) * Lᵀ)) * L =
        Lᵀ * A * L + (Lᵀ * A * L) * (B - 1) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc]
      rw [hcancel]
    have h2 : Lᵀ * ((1 + L * (B - 1) * Lᵀ) * A) * L =
        Lᵀ * A * L + (B - 1) * (Lᵀ * A * L) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, ← Matrix.mul_assoc, hLL]
    rw [h1, h2] at hc
    have hc' : (Lᵀ * A * L) * (B - 1) = (B - 1) * (Lᵀ * A * L) := add_left_cancel hc
    calc (Lᵀ * A * L) * B = (Lᵀ * A * L) * ((B - 1) + 1) := by rw [sub_add_cancel]
      _ = (Lᵀ * A * L) * (B - 1) + (Lᵀ * A * L) := by rw [Matrix.mul_add, Matrix.mul_one]
      _ = (B - 1) * (Lᵀ * A * L) + (Lᵀ * A * L) := by rw [hc']
      _ = ((B - 1) + 1) * (Lᵀ * A * L) := by rw [Matrix.add_mul, Matrix.one_mul]
      _ = B * (Lᵀ * A * L) := by rw [sub_add_cancel]
  rwa [hL]



private theorem neg_one_mem_sylow {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (Q : Sylow 2 SL(2, F)) : (-1 : SL(2, F)) ∈ (Q : Subgroup SL(2, F)) := by
  obtain ⟨x, hx, y, hy, hxx, -, -⟩ :=
    (CFSG.ComponentClassification.HarrisLit.T1.sylow_sl2_facts hF Q).1 1
      (Q : Subgroup SL(2, F)).one_mem
  have hmem : x * x ∈ (Q : Subgroup SL(2, F)) := (Q : Subgroup SL(2, F)).mul_mem hx hx
  rwa [hxx] at hmem

private theorem exists_blockIdx_of_ne_of_div_two_eq {m tail : ℕ} (htail : tail ≤ 1)
    {a b : Fin (2 * m + 1 + 1 + tail)} (hab : a ≠ b) (hclass : a.val / 2 = b.val / 2) :
    ∃ (k : Fin (m + 1)) (h : 2 * k.val + 2 ≤ 2 * m + 1 + 1 + tail) (x y : Fin 2),
      x ≠ y ∧ blockIdx (2 * k.val) h x = a ∧ blockIdx (2 * k.val) h y = b := by
  have hhalf : ∀ x : Fin (2 * m + 1 + 1 + tail), x.val / 2 ≤ m + 1 := by
    intro x
    have hx := x.isLt
    exact Nat.div_le_of_le_mul (k := 2) (n := m + 1) (by omega)
  have hle : a.val / 2 ≤ m := by
    rcases Nat.lt_or_eq_of_le (hhalf a) with h | h
    · omega
    · exfalso
      have ha' := (Nat.div_eq_iff (k := 2) (x := a.val) (y := m + 1) (by norm_num)).mp h
      have hb' := (Nat.div_eq_iff (k := 2) (x := b.val) (y := m + 1) (by norm_num)).mp
        (hclass.symm.trans h)
      have haN := a.isLt
      have hbN := b.isLt
      exact hab (Fin.ext (by omega))
  refine ⟨⟨a.val / 2, by omega⟩, by omega,
    ⟨a.val - 2 * (a.val / 2), by omega⟩, ⟨b.val - 2 * (a.val / 2), by omega⟩,
    ?_, ?_, ?_⟩
  · intro hxy
    apply hab
    have hval := congrArg Fin.val hxy
    simp only at hval
    have ha := (mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) a).mpr rfl
    have hb := (mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) b).mpr
      (hclass.symm.trans rfl)
    exact Fin.ext (by omega)
  · ext
    simp only [blockIdx_val]
    omega
  · ext
    simp only [blockIdx_val]
    have hb := (mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) b).mpr
      (hclass.symm.trans rfl)
    omega

private theorem commutator_mul_central {G : Type} [Group G] {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) (a b : G) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hzc : Commute z b := (Subgroup.mem_center_iff.mp hz b).symm
  have hzw : Commute z w := (Subgroup.mem_center_iff.mp hz w).symm
  have haw : Commute a w := Subgroup.mem_center_iff.mp hw a
  have hz1 : ⁅z, b * w⁆ = 1 := (hzc.mul_right hzw).commutator_eq
  have hw1 : ⁅a, w⁆ = 1 := haw.commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, hz1,
    commutatorElement_mul_right_eq_mul_conj, hw1]
  group

private theorem conj_commutator_mem_of_conj_mem_mul_center
    {G : Type} [Group G] {H Z : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    {u : G} (hkey : ∀ x ∈ H, ∃ j ∈ H, ∃ z ∈ Z, u * x * u⁻¹ = j * z)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    u * ⁅x, y⁆ * u⁻¹ ∈ H := by
  obtain ⟨j1, hj1, z1, hz1, hx1⟩ := hkey x hx
  obtain ⟨j2, hj2, z2, hz2, hy2⟩ := hkey y hy
  rw [conjugate_commutatorElement, hx1, hy2]
  rw [commutator_mul_central (hZ hz1) (hZ hz2)]
  exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator hj1 hj2)

private theorem exists_neg_one_eq_commutator_sl2 {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) :
    ∃ I Jm : SL(2, F), ⁅I, Jm⁆ = (-1 : SL(2, F)) := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hF
  have hK : ringChar F ≠ 2 := by
    intro h
    have : CharP F 2 := ringChar.eq_iff.mp h
    exact h2 (CharP.cast_eq_zero F 2)
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hK (-1)
  obtain ⟨I, hI⟩ : ∃ I : SL(2, F), (I : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨Jm, hJm⟩ : ∃ Jm : SL(2, F), (Jm : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] :=
    ⟨⟨_, by rw [Matrix.det_fin_two]; simp; linear_combination -hab⟩, rfl⟩
  have hIi : ((I⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hI, Matrix.adjugate_fin_two]
    simp
  have hJi : ((Jm⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-a, -b; -b, a] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hJm, Matrix.adjugate_fin_two]
    simp
  refine ⟨I, Jm, ?_⟩
  apply Subtype.ext
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul, hI, hJm, hIi, hJi,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | linear_combination hab | ring

theorem exists_blockScalar_of_commute_frame_sylow {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {m tail : ℕ} (htail : tail ≤ 1) (Q : Fin (m + 1) → Sylow 2 SL(2, F))
    {A : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F}
    (hA : ∀ k : Fin (m + 1), ∀ B ∈ (Q k : Subgroup SL(2, F)),
      A * ((blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) B :
        SL(2 * m + 1 + 1 + tail, F)) : Matrix (Fin (2 * m + 1 + 1 + tail))
          (Fin (2 * m + 1 + 1 + tail)) F) =
      ((blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) B :
        SL(2 * m + 1 + 1 + tail, F)) : Matrix (Fin (2 * m + 1 + 1 + tail))
          (Fin (2 * m + 1 + 1 + tail)) F) * A) :
    ∃ c : Fin (2 * m + 1 + 1 + tail) → F, A = Matrix.diagonal c ∧
      ∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 = b.val / 2 → c a = c b := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hF
  have hcomm : ∀ k : Fin (m + 1),
      A * (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) =
      (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) * A := by
    intro k
    have h := hA k (-1) (neg_one_mem_sylow hF (Q k))
    simpa only [linearFrameInvolution] using h
  have hoff : ∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 ≠ b.val / 2 → A a b = 0 :=
    fun a b hab => eq_zero_of_commute_frameInvolution h2 htail hcomm hab
  have hblock : ∀ k : Fin (m + 1), ∃ ck : F,
      ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
        blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) = ck • 1 := by
    intro k
    have hM : ∀ g ∈ (Q k : Subgroup SL(2, F)),
        ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) *
            (g : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) *
          ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
            blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) := by
      intro g hg
      have h := hA k g hg
      rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL] at h
      exact block_commute_of_mul_blockMat (by omega) h
    exact CFSG.ComponentClassification.HarrisLit.T1.eq_smul_one_of_commute_sylow_sl2
      hF (Q k) hM
  choose ck hck using hblock
  refine ⟨fun a => A a a, ?_, ?_⟩
  · ext a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · have hzero : A a b = 0 := by
        by_cases hclass : a.val / 2 = b.val / 2
        · obtain ⟨k, hk2, x, y, hxy, hbx, hby⟩ :=
            exists_blockIdx_of_ne_of_div_two_eq htail hab hclass
          have hMxy : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
              blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) x y = 0 := by
            rw [hck k]
            simp [hxy]
          rw [blockSel_conj_apply (i := 2 * k.val) hk2, hbx, hby] at hMxy
          exact hMxy
        · exact hoff a b hclass
      rw [if_neg hab, hzero]
  · intro a b hclass
    change A a a = A b b
    by_cases hab : a = b
    · subst hab
      rfl
    · obtain ⟨k, hk2, x, y, hxy, hbx, hby⟩ :=
        exists_blockIdx_of_ne_of_div_two_eq htail hab hclass
      have hMxx : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) x x = ck k := by
        rw [hck k]
        simp
      have hMyy : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) y y = ck k := by
        rw [hck k]
        simp
      rw [blockSel_conj_apply (i := 2 * k.val) hk2, hbx] at hMxx
      rw [blockSel_conj_apply (i := 2 * k.val) hk2, hby] at hMyy
      rw [hMxx, hMyy]

theorem commute_diagonal_of_commute_frameInvolution {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    {m tail : ℕ} (htail : tail ≤ 1)
    {u : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F}
    (hu : ∀ k : Fin (m + 1),
      u * (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) =
      (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail))
        (Fin (2 * m + 1 + 1 + tail)) F) * u)
    {c : Fin (2 * m + 1 + 1 + tail) → F} (hc : ∀ a b, a.val / 2 = b.val / 2 → c a = c b) :
    u * Matrix.diagonal c = Matrix.diagonal c * u := by

  ext a b
  by_cases hab : a.val / 2 = b.val / 2
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ← hc a b hab]
    ring
  · have h0 := eq_zero_of_commute_frameInvolution h2 htail hu hab
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h0, zero_mul, mul_zero]

theorem commute_frameInvolution_of_map_eq {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {m tail : ℕ} (k : Fin (m + 1)) (u : SL(2 * m + 1 + 1 + tail, F))
    (hu : ((linearFrameBlock F m k tail).map
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F)).map
          (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
            (2 * m + 1 + 1 + tail) F u)).toMonoidHom =
      (linearFrameBlock F m k tail).map
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F)) :
    u * linearFrameInvolution F m k tail = linearFrameInvolution F m k tail * u := by

  set pi := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F with hpi
  set Z := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (2 * m + 1 + 1 + tail) F
    with hZdef
  set J := linearFrameBlock F m k tail with hJ
  set t := linearFrameInvolution F m k tail with ht
  have hZc : Z ≤ Subgroup.center (SL(2 * m + 1 + 1 + tail, F)) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center _ _
  have hu' : (J.map pi).map (MulAut.conj (pi u)).toMonoidHom = J.map pi := by
    rw [hJ, hpi]
    exact hu
  have hkey : ∀ x ∈ J, ∃ j ∈ J, ∃ z ∈ Z, u * x * u⁻¹ = j * z := by
    intro x hx
    have hmem : MulAut.conj (pi u) (pi x) ∈ J.map pi := by
      have h1 : MulAut.conj (pi u) (pi x) ∈ (J.map pi).map (MulAut.conj (pi u)).toMonoidHom :=
        ⟨pi x, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hu'] at h1
    rw [Subgroup.mem_map] at hmem
    obtain ⟨j, hj, hjx⟩ := hmem
    have hjx' : pi j = pi (u * x * u⁻¹) := by
      rw [hjx, MulAut.conj_apply]
      simp only [map_mul, map_inv]
    refine ⟨j, hj, j⁻¹ * (u * x * u⁻¹),
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff.mp hjx', by group⟩
  obtain ⟨I, Jm, hIJ⟩ := exists_neg_one_eq_commutator_sl2 hF
  set x0 : SL(2 * m + 1 + 1 + tail, F) := blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
    (by omega) I with hx0
  set y0 : SL(2 * m + 1 + 1 + tail, F) := blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
    (by omega) Jm with hy0
  have hx0mem : x0 ∈ J := by
    rw [hJ, linearFrameBlock, hx0]
    exact ⟨I, rfl⟩
  have hy0mem : y0 ∈ J := by
    rw [hJ, linearFrameBlock, hy0]
    exact ⟨Jm, rfl⟩
  have ht_eq : t = ⁅x0, y0⁆ := by
    rw [ht, hx0, hy0, linearFrameInvolution, ← hIJ]
    exact map_commutatorElement (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega)) I Jm
  have hJfin : J = (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega)).range := by
    rw [hJ, linearFrameBlock]
  have ht2 : t * t = 1 := by
    rw [ht, linearFrameInvolution, ← map_mul]
    simp
  have hconj_sq : (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
    calc (u * t * u⁻¹) * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have ht_ne_one : t ≠ 1 := by
    intro h
    rw [ht, linearFrameInvolution] at h
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hF
      (CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := F)
        (m := 2 * m + 1 + 1 + tail) (k := 2) (i := 2 * k.val) (by omega)
        (by simpa using h))
  have hne : u * t * u⁻¹ ≠ 1 := by
    intro h1
    apply ht_ne_one
    calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group
  have ht_mem : u * t * u⁻¹ ∈ J := by
    rw [ht_eq]
    exact conj_commutator_mem_of_conj_mem_mul_center hZc hkey hx0mem hy0mem
  rw [hJfin] at ht_mem
  obtain ⟨j, hjeq⟩ := ht_mem
  have hjsq : j * j = 1 := by
    apply CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := F)
      (m := 2 * m + 1 + 1 + tail) (k := 2) (i := 2 * k.val) (by omega)
    rw [map_mul, hjeq, hconj_sq, map_one]
  have hjne : j ≠ 1 := by
    intro h
    apply hne
    rw [← hjeq, h, map_one]
  have hord : orderOf j = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hjsq) hjne
  have hjneg : j = -1 := (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hF j).mp hord
  have hfinal : u * t * u⁻¹ = t := by
    rw [← hjeq, hjneg, ht, linearFrameInvolution]
  calc u * t = (u * t * u⁻¹) * u := by group
    _ = t * u := by rw [hfinal]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
