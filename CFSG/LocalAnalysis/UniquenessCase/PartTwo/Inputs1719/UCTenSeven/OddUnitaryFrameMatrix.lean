module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Matrix
open CFSG.LocalAnalysis.UniquenessCase.UC22 (unitaryFrameBlock unitaryFrameInvolution
  linearFrameInvolution)
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockMat blockSel blockIdx blockIdx_val
  blockSel_apply blockSel_transpose_mul_self blockEmb_injective)
open CFSG.ClassicalInvolution.Models (suMat negBlock negOneSU suMat_negOneSU suMat_blockEmb
  negBlock_eq_diagonal negOneSU_mul_self negOneSU_ne_one orderOf_negOneSU det_suMat suMat_mul
  suMat_injective two_ne_zero_of_charP_ne_two nonempty_sl2_mulEquiv_su_two
  odd_natCard_fixedSubfield)
open CFSG.LieType.Steinberg (fixedSubfield)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

private theorem uct_eq_zero_of_neg_eq_self {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {x : K} (h : -x = x) : x = 0 := by
  have h' : x + x = 0 := by linear_combination -h
  have h2x : (2 : K) * x = 0 := by rw [two_mul]; exact h'
  exact (mul_eq_zero.mp h2x).resolve_left h2

private theorem uct_mem_pair_iff {m tail : ℕ} (k : Fin (m + 1))
    (a : Fin (2 * m + 1 + 1 + tail)) :
    (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) ↔ a.val / 2 = k.val := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · intro h
    have h' := (Nat.div_eq_iff (k := 2) (x := a.val) (y := k.val) (by norm_num)).mp h
    omega

private theorem uct_eq_zero_of_commute_negBlock {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {m tail : ℕ} (htail : tail ≤ 1)
    {u : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) K}
    (hu : ∀ k : Fin (m + 1),
      u * negBlock K (2 * m + 1 + 1 + tail) (2 * k.val) =
      negBlock K (2 * m + 1 + 1 + tail) (2 * k.val) * u)
    {a b : Fin (2 * m + 1 + 1 + tail)} (hab : a.val / 2 ≠ b.val / 2) :
    u a b = 0 := by
  have hhalf : ∀ x : Fin (2 * m + 1 + 1 + tail), x.val / 2 ≤ m + 1 := by
    intro x
    have hx := x.isLt
    exact Nat.div_le_of_le_mul (k := 2) (n := m + 1) (by omega)
  rcases lt_or_gt_of_ne hab with h | h
  · set k : Fin (m + 1) := ⟨a.val / 2, by have := hhalf a; omega⟩ with hk
    have hka : a.val / 2 = k.val := rfl
    have hkb : b.val / 2 ≠ k.val := by
      simp only [hk, Fin.val_mk]
      omega
    have hmem_a : 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2 := (uct_mem_pair_iff k a).mpr hka
    have hmem_b : ¬ (2 * k.val ≤ b.val ∧ b.val < 2 * k.val + 2) :=
      fun hc => hkb ((uct_mem_pair_iff k b).mp hc)
    have hentry := congrFun (congrFun (hu k) a) b
    rw [negBlock_eq_diagonal] at hentry
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    rw [ite_eq_right hmem_b, ite_eq_left hmem_a, mul_one, neg_one_mul] at hentry
    exact uct_eq_zero_of_neg_eq_self h2 hentry.symm
  · set k : Fin (m + 1) := ⟨b.val / 2, by have := hhalf b; omega⟩ with hk
    have hkb : b.val / 2 = k.val := rfl
    have hka : a.val / 2 ≠ k.val := by
      simp only [hk, Fin.val_mk]
      omega
    have hmem_b : 2 * k.val ≤ b.val ∧ b.val < 2 * k.val + 2 := (uct_mem_pair_iff k b).mpr hkb
    have hmem_a : ¬ (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) :=
      fun hc => hka ((uct_mem_pair_iff k a).mp hc)
    have hentry := congrFun (congrFun (hu k) a) b
    rw [negBlock_eq_diagonal] at hentry
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    rw [ite_eq_left hmem_b, ite_eq_right hmem_a, mul_neg, mul_one, one_mul] at hentry
    exact uct_eq_zero_of_neg_eq_self h2 hentry

private theorem uct_mul_blockSel_apply {K : Type} [Field K] {N i : ℕ} (hi : i + 2 ≤ N)
    (A : Matrix (Fin N) (Fin N) K) (a : Fin N) (w : Fin 2) :
    (A * blockSel K N 2 i) a w = A a (blockIdx i hi w) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (blockIdx i hi w)]
  · simp [blockSel_apply, blockIdx_val]
  · intro z _ hz
    have h : z.val ≠ i + w.val := fun h => hz (Fin.ext (by simpa [blockIdx_val] using h))
    simp [blockSel_apply, h]
  · simp

private theorem uct_blockSel_transpose_mul_apply {K : Type} [Field K] {N n i : ℕ}
    (hi : i + 2 ≤ N) (A : Matrix (Fin N) (Fin n) K) (w : Fin 2) (b : Fin n) :
    ((blockSel K N 2 i)ᵀ * A) w b = A (blockIdx i hi w) b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (blockIdx i hi w)]
  · simp [Matrix.transpose_apply, blockSel_apply, blockIdx_val]
  · intro z _ hz
    have h : z.val ≠ i + w.val := fun h => hz (Fin.ext (by simpa [blockIdx_val] using h))
    simp [Matrix.transpose_apply, blockSel_apply, h]
  · simp

private theorem uct_blockSel_conj_apply {K : Type} [Field K] {N i : ℕ} (hi : i + 2 ≤ N)
    (A : Matrix (Fin N) (Fin N) K) (x y : Fin 2) :
    ((blockSel K N 2 i)ᵀ * A * blockSel K N 2 i) x y =
      A (blockIdx i hi x) (blockIdx i hi y) := by
  have h1 := uct_blockSel_transpose_mul_apply hi (A * blockSel K N 2 i) x y
  have h2 := uct_mul_blockSel_apply hi A (blockIdx i hi x) y
  calc ((blockSel K N 2 i)ᵀ * A * blockSel K N 2 i) x y
      = ((blockSel K N 2 i)ᵀ * (A * blockSel K N 2 i)) x y := by
        rw [Matrix.mul_assoc]
    _ = (A * blockSel K N 2 i) (blockIdx i hi x) y := h1
    _ = A (blockIdx i hi x) (blockIdx i hi y) := h2

private theorem uct_block_commute_of_mul_blockMat {K : Type} [Field K] {N i : ℕ}
    (hi : i + 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) K} {B : Matrix (Fin 2) (Fin 2) K}
    (h : A * blockMat N i B = blockMat N i B * A) :
    ((blockSel K N 2 i)ᵀ * A * blockSel K N 2 i) * B =
      B * ((blockSel K N 2 i)ᵀ * A * blockSel K N 2 i) := by
  set L : Matrix (Fin N) (Fin 2) K := blockSel K N 2 i with hL
  have hLL : Lᵀ * L = 1 := blockSel_transpose_mul_self hi
  have hBL : blockMat N i B = 1 + L * (B - 1) * Lᵀ := rfl
  have key : (Lᵀ * A * L) * B = B * (Lᵀ * A * L) := by
    have hc := congrArg (fun M => Lᵀ * M * L) h
    rw [hBL] at hc
    have hcancel : ∀ X : Matrix (Fin 2) (Fin 2) K, X * Lᵀ * L = X := by
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

private theorem uct_exists_blockIdx_of_ne_of_div_two_eq {m tail : ℕ} (htail : tail ≤ 1)
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
    have ha := (uct_mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) a).mpr rfl
    have hb := (uct_mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) b).mpr
      (hclass.symm.trans rfl)
    exact Fin.ext (by omega)
  · ext
    simp only [blockIdx_val]
    omega
  · ext
    simp only [blockIdx_val]
    have hb := (uct_mem_pair_iff (⟨a.val / 2, by omega⟩ : Fin (m + 1)) b).mpr
      (hclass.symm.trans rfl)
    omega

private theorem uct_suMat_ne_smul_one {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) {x : Su K p f 2}
    (hx : x * x = negOneSU K p f) :
    ∀ c : K, suMat x ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro c hc
  have hdet : c ^ 2 = 1 := by
    have h := det_suMat x
    rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
    exact h
  have hsquare : suMat x * suMat x = -1 := by
    rw [← suMat_mul, hx, suMat_negOneSU]
  have hmat : c ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) = -1 := by
    calc c ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) = (c • 1) * (c • 1) := by
          rw [smul_mul_smul_comm, Matrix.one_mul, ← pow_two]
      _ = suMat x * suMat x := by rw [hc]
      _ = -1 := hsquare
  have hentry : c ^ 2 = (-1 : K) := by
    have := congrFun (congrFun hmat 0) 0
    simpa using this
  rw [hdet] at hentry
  have htwo : (2 : K) = 0 := by
    have h : (1 : K) + 1 = 0 := by linear_combination hentry
    calc (2 : K) = 1 + 1 := by norm_num
      _ = 0 := h
  exact h2 htwo

private theorem uct_commutator_mul_central {G : Type} [Group G] {z w : G}
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

private theorem uct_conj_commutator_mem_of_conj_mem_mul_center
    {G : Type} [Group G] {H Z : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    {u : G} (hkey : ∀ x ∈ H, ∃ j ∈ H, ∃ z ∈ Z, u * x * u⁻¹ = j * z)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    u * ⁅x, y⁆ * u⁻¹ ∈ H := by
  obtain ⟨j1, hj1, z1, hz1, hx1⟩ := hkey x hx
  obtain ⟨j2, hj2, z2, hz2, hy2⟩ := hkey y hy
  rw [conjugate_commutatorElement, hx1, hy2]
  rw [uct_commutator_mul_central (hZ hz1) (hZ hz2)]
  exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator hj1 hj2)

private theorem uct_exists_neg_one_eq_commutator_sl2 {K : Type} [Field K] [Finite K]
    (hF : Odd (Nat.card K)) :
    ∃ I Jm : SL(2, K), ⁅I, Jm⁆ = (-1 : SL(2, K)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hF
  have hK : ringChar K ≠ 2 := by
    intro h
    have : CharP K 2 := ringChar.eq_iff.mp h
    exact h2 (CharP.cast_eq_zero K 2)
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hK (-1)
  obtain ⟨I, hI⟩ : ∃ I : SL(2, K), (I : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨Jm, hJm⟩ : ∃ Jm : SL(2, K), (Jm : Matrix (Fin 2) (Fin 2) K) = !![a, b; b, -a] :=
    ⟨⟨_, by rw [Matrix.det_fin_two]; simp; linear_combination -hab⟩, rfl⟩
  have hIi : ((I⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hI, Matrix.adjugate_fin_two]
    simp
  have hJi : ((Jm⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![-a, -b; -b, a] := by
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


theorem coe_linearFrameInvolution_eq_suMat {m tail : ℕ} (k : Fin (m + 1)) :
    ((linearFrameInvolution F m k tail : SL(2 * m + 1 + 1 + tail, F)) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
      suMat (unitaryFrameInvolution F p f m k tail) := by
  rw [linearFrameInvolution, unitaryFrameInvolution]
  rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
    CFSG.ClassicalInvolution.Models.suMat_blockEmb]
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    CFSG.ClassicalInvolution.Models.suMat_negOneSU]

theorem exists_blockScalar_of_commute_unitaryFrame_sylow (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) {m tail : ℕ} (htail : tail ≤ 1) (Q : Fin (m + 1) → Sylow 2 (Su F p f 2))
    {A : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F}
    (hA : ∀ k : Fin (m + 1), ∀ B ∈ (Q k : Subgroup (Su F p f 2)),
      A * suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B) =
        suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B) * A) :
    ∃ c : Fin (2 * m + 1 + 1 + tail) → F, A = Matrix.diagonal c ∧
      ∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 = b.val / 2 → c a = c b := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hodd : Odd (Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p f)) :=
    odd_natCard_fixedSubfield hF hp2
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := p) (f := f) hF
  have hneg : e (-1) = negOneSU F p f := by
    have h := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm
      (negOneSU F p f)).mp (orderOf_negOneSU h2)
    simpa using h.symm
  have hsq_mem : ∀ k : Fin (m + 1), ∃ x ∈ (Q k : Subgroup (Su F p f 2)),
      x * x = negOneSU F p f ∧
        ∃ y ∈ (Q k : Subgroup (Su F p f 2)), x * y ≠ y * x := by
    intro k
    let Q' : Sylow 2 (SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f)) :=
      Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective (Q k)
    have hQ' : (Q' : Subgroup (SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f))) =
        (Q k : Subgroup (Su F p f 2)).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective (Q k)
    obtain ⟨x₀, hx₀, y₀, hy₀, hx₀sq, -, hx₀y₀⟩ :=
      (CFSG.ComponentClassification.HarrisLit.T1.sylow_sl2_facts hodd Q').2
    have mem_of_mem : ∀ z : SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f),
        z ∈ (Q' : Subgroup (SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f))) →
        e z ∈ (Q k : Subgroup (Su F p f 2)) := by
      intro z hz
      have hz' : z ∈ (Q k : Subgroup (Su F p f 2)).map e.symm.toMonoidHom := by
        rw [← hQ']; exact hz
      rw [Subgroup.mem_map] at hz'
      obtain ⟨w, hw, hwz⟩ := hz'
      have hzw : e z = w := by
        rw [← hwz]
        simp
      rwa [hzw]
    refine ⟨e x₀, mem_of_mem x₀ hx₀, ?_, e y₀, mem_of_mem y₀ hy₀, ?_⟩
    · rw [← map_mul, hx₀sq, hneg]
    · intro h
      exact hx₀y₀ (e.injective (by rw [map_mul, map_mul]; exact h))
  have hcomm : ∀ k : Fin (m + 1),
      A * negBlock F (2 * m + 1 + 1 + tail) (2 * k.val) =
      negBlock F (2 * m + 1 + 1 + tail) (2 * k.val) * A := by
    intro k
    obtain ⟨x, hxQ, hxsq, -⟩ := hsq_mem k
    have h := hA k (x * x) ((Q k : Subgroup (Su F p f 2)).mul_mem hxQ hxQ)
    rw [hxsq] at h
    change A * suMat (unitaryFrameInvolution F p f m k tail) =
      suMat (unitaryFrameInvolution F p f m k tail) * A at h
    rwa [CFSG.LocalAnalysis.UniquenessCase.UC22.suMat_unitaryFrameInvolution] at h
  have hoff : ∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 ≠ b.val / 2 → A a b = 0 :=
    fun a b hab => uct_eq_zero_of_commute_negBlock h2 htail hcomm hab
  have hblock : ∀ k : Fin (m + 1), ∃ ck : F,
      ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
        blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) = ck • 1 := by
    intro k
    obtain ⟨x, hxQ, hxsq, y, hyQ, hxy⟩ := hsq_mem k
    have hMx : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) * suMat x =
        suMat x * ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) := by
      have h := hA k x hxQ
      rw [suMat_blockEmb] at h
      exact uct_block_commute_of_mul_blockMat (by omega) h
    have hMy : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) * suMat y =
        suMat y * ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) := by
      have h := hA k y hyQ
      rw [suMat_blockEmb] at h
      exact uct_block_commute_of_mul_blockMat (by omega) h
    obtain ⟨α, β, hαβ⟩ :=
      CFSG.ComponentClassification.HarrisLit.T1.exists_eq_smul_one_add_smul_of_commute
        (uct_suMat_ne_smul_one h2 hxsq) hMx
    have hβ : β = 0 := by
      by_contra hβ
      apply hxy
      apply suMat_injective
      rw [suMat_mul, suMat_mul]
      have h := hMy
      rw [hαβ, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        mul_smul_comm, Matrix.one_mul, Matrix.mul_one] at h
      have h' : β • (suMat x * suMat y) = β • (suMat y * suMat x) := add_left_cancel h
      exact smul_right_injective _ hβ h'
    exact ⟨α, by rw [hαβ, hβ, zero_smul, add_zero]⟩
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
            uct_exists_blockIdx_of_ne_of_div_two_eq htail hab hclass
          have hMxy : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
              blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) x y = 0 := by
            rw [hck k]
            simp [hxy]
          rw [uct_blockSel_conj_apply (i := 2 * k.val) hk2, hbx, hby] at hMxy
          exact hMxy
        · exact hoff a b hclass
      rw [if_neg hab, hzero]
  · intro a b hclass
    change A a a = A b b
    by_cases hab : a = b
    · subst hab
      rfl
    · obtain ⟨k, hk2, x, y, hxy, hbx, hby⟩ :=
        uct_exists_blockIdx_of_ne_of_div_two_eq htail hab hclass
      have hMxx : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) x x = ck k := by
        rw [hck k]
        simp
      have hMyy : ((blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val))ᵀ * A *
          blockSel F (2 * m + 1 + 1 + tail) 2 (2 * k.val)) y y = ck k := by
        rw [hck k]
        simp
      rw [uct_blockSel_conj_apply (i := 2 * k.val) hk2, hbx] at hMxx
      rw [uct_blockSel_conj_apply (i := 2 * k.val) hk2, hby] at hMyy
      rw [hMxx, hMyy]

theorem commute_unitaryFrameInvolution_of_map_eq (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {m tail : ℕ} {X : Type} [Group X] (ψ : Su F p f (2 * m + 1 + 1 + tail) →* X)
    (hker : ψ.ker ≤ center (Su F p f (2 * m + 1 + 1 + tail))) (k : Fin (m + 1))
    (u : Su F p f (2 * m + 1 + 1 + tail))
    (hu : ((unitaryFrameBlock F p f m k tail).map ψ).map (MulAut.conj (ψ u)).toMonoidHom =
      (unitaryFrameBlock F p f m k tail).map ψ) :
    u * unitaryFrameInvolution F p f m k tail = unitaryFrameInvolution F p f m k tail * u := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hodd : Odd (Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p f)) :=
    odd_natCard_fixedSubfield hF hp2
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := p) (f := f) hF
  have hneg : e (-1) = negOneSU F p f := by
    have h := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm
      (negOneSU F p f)).mp (orderOf_negOneSU h2)
    simpa using h.symm
  set J := unitaryFrameBlock F p f m k tail with hJ
  set t := unitaryFrameInvolution F p f m k tail with ht
  set Z := ψ.ker with hZdef
  have hZc : Z ≤ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)) := by
    rw [hZdef]
    exact hker
  have hkey : ∀ x ∈ J, ∃ j ∈ J, ∃ z ∈ Z, u * x * u⁻¹ = j * z := by
    intro x hx
    have hmem : MulAut.conj (ψ u) (ψ x) ∈ J.map ψ := by
      have h1 : MulAut.conj (ψ u) (ψ x) ∈
          (J.map ψ).map (MulAut.conj (ψ u)).toMonoidHom :=
        ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hu] at h1
    rw [Subgroup.mem_map] at hmem
    obtain ⟨j, hj, hjx⟩ := hmem
    have hjx' : ψ j = ψ (u * x * u⁻¹) := by
      rw [hjx, MulAut.conj_apply]
      simp only [map_mul, map_inv]
    refine ⟨j, hj, j⁻¹ * (u * x * u⁻¹), ?_, by group⟩
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hjx']; group)
  obtain ⟨I, Jm, hIJ⟩ := uct_exists_neg_one_eq_commutator_sl2 hodd
  set x0 : Su F p f (2 * m + 1 + 1 + tail) :=
    blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
      (by have := k.isLt; omega) (e I) with hx0
  set y0 : Su F p f (2 * m + 1 + 1 + tail) :=
    blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
      (by have := k.isLt; omega) (e Jm) with hy0
  have hx0mem : x0 ∈ J := by
    rw [hJ, hx0]
    simp only [unitaryFrameBlock]
    exact ⟨e I, rfl⟩
  have hy0mem : y0 ∈ J := by
    rw [hJ, hy0]
    simp only [unitaryFrameBlock]
    exact ⟨e Jm, rfl⟩
  have ht_eq : t = ⁅x0, y0⁆ := by
    rw [ht, unitaryFrameInvolution, hx0, hy0, ← hneg, ← hIJ, map_commutatorElement e I Jm]
    exact map_commutatorElement (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
      (by have := k.isLt; omega)) (e I) (e Jm)
  have ht2 : t * t = 1 := by
    rw [ht, unitaryFrameInvolution, ← map_mul, negOneSU_mul_self, map_one]
  have ht_ne_one : t ≠ 1 := by
    intro h
    rw [ht, unitaryFrameInvolution] at h
    exact negOneSU_ne_one h2 (blockEmb_injective (K := F) (p := p) (f := f)
      (m := 2 * m + 1 + 1 + tail) (k := 2) (i := 2 * k.val)
      (by have := k.isLt; omega) (by simpa using h))
  have hconj_sq : (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
    calc (u * t * u⁻¹) * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hne : u * t * u⁻¹ ≠ 1 := by
    intro h1
    apply ht_ne_one
    calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group
  have ht_mem : u * t * u⁻¹ ∈ J := by
    rw [ht_eq]
    exact uct_conj_commutator_mem_of_conj_mem_mul_center hZc hkey hx0mem hy0mem
  have hJfin : J = (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
      (by have := k.isLt; omega)).range := by
    rw [hJ, unitaryFrameBlock]
  rw [hJfin] at ht_mem
  obtain ⟨j, hjeq⟩ := ht_mem
  have hjsq : j * j = 1 := by
    apply blockEmb_injective (K := F) (p := p) (f := f) (m := 2 * m + 1 + 1 + tail)
      (k := 2) (i := 2 * k.val) (by have := k.isLt; omega)
    rw [map_mul, hjeq, hconj_sq, map_one]
  have hjne : j ≠ 1 := by
    intro h
    apply hne
    rw [← hjeq, h, map_one]
  have hord : orderOf j = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hjsq) hjne
  have hjneg : j = negOneSU F p f := by
    have h := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm j).mp hord
    simpa [hneg] using h
  have hfinal : u * t * u⁻¹ = t := by
    rw [← hjeq, hjneg, ht, unitaryFrameInvolution]
  calc u * t = (u * t * u⁻¹) * u := by group
    _ = t * u := by rw [hfinal]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
