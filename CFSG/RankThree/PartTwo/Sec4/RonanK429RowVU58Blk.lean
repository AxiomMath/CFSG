module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Lin
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesU58
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesU58
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.Open (StatedSU)
open scoped commutatorElement

section Blocks

variable {F : Type*} [Field F] {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {t : ι → α}

abbrev fibBlk (t : ι → α) (κ : α) (M : Matrix ι ι F) :
    Matrix {i // t i = κ} {i // t i = κ} F :=
  M.submatrix Subtype.val Subtype.val

theorem fibBlk_one (κ : α) : fibBlk t κ (1 : Matrix ι ι F) = 1 :=
  submatrix_one _ Subtype.val_injective

theorem fibBlk_mul (κ : α) {M N : Matrix ι ι F} (hM : IsBlockDiag t M) :
    fibBlk t κ (M * N) = fibBlk t κ M * fibBlk t κ N := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  have h0 : ∑ k : {k // ¬ t k = κ}, M a k * N k b = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hM a k (fun h => k.2 (h.symm.trans ha)), zero_mul]
  rw [fibBlk, fibBlk, fibBlk, submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun k => t k = κ) (fun k => M a k * N k b), h0,
    add_zero]
  rfl

theorem fibBlk_pow (κ : α) {M : Matrix ι ι F} (hM : IsBlockDiag t M) (n : ℕ) :
    fibBlk t κ (M ^ n) = fibBlk t κ M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fibBlk_one]
  | succ n ih => rw [pow_succ', fibBlk_mul κ hM, ih, ← pow_succ']

theorem fibBlk_unitary (κ : α) (f : F →+* F) {M : Matrix ι ι F} (hM : IsBlockDiag t M)
    (hMu : (M.map f)ᵀ * M = 1) : ((fibBlk t κ M).map f)ᵀ * fibBlk t κ M = 1 := by
  have hMT : IsBlockDiag t (M.map f)ᵀ := fun i j hij => by
    rw [transpose_apply, map_apply, hM j i (Ne.symm hij), map_zero]
  have h := fibBlk_mul κ (N := M) hMT
  rw [hMu, fibBlk_one] at h
  rw [h]
  rfl

theorem entry_of_fibBlk_eq_one (κ : α) {M : Matrix ι ι F} (h : fibBlk t κ M = 1) {a b : ι}
    (ha : t a = κ) (hb : t b = κ) : M a b = (1 : Matrix ι ι F) a b := by
  have h1 := congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩
  rw [fibBlk, submatrix_apply] at h1
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  simp [Subtype.ext_iff]

theorem eq_one_of_blocks {M : Matrix ι ι F} (hM : IsBlockDiag t M)
    (h : ∀ a b, t a = t b → M a b = (1 : Matrix ι ι F) a b) : M = 1 := by
  ext a b
  by_cases hab : t a = t b
  · exact h a b hab
  · rw [hM a b hab, Matrix.one_apply_ne (fun e => hab (congrArg t e))]

theorem mul_apply_singleton {M N : Matrix ι ι F} (hM : IsBlockDiag t M) {j : ι}
    (hj : ∀ k, t k = t j → k = j) : (M * N) j j = M j j * N j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hk
    rw [hM j k (fun h => hk (hj k h.symm)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Blocks

theorem card_K_eq : Nat.card K = 64 := by
  rw [card_K]
  norm_num

theorem mU_mem (g : SUI) :
    (mU g).det = 1 ∧ ((mU g).map (iterateFrobenius K 2 3))ᵀ * mU g = 1 :=
  (mem_SUI_iff _).mp g.2

theorem mU_pow (g : SUI) (n : ℕ) : mU (g ^ n) = mU g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mU_mul, ih, pow_succ]

theorem block_eq_one_of_pow {u : Fin 4 → ZMod 9} {g : SUI}
    (hg : g ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) {p : ℕ}
    (κ : ZMod 9)
    (hp : (p = 5 ∧ Fintype.card {i // ext9 u i = κ} < 4) ∨
      (p = 19 ∧ Fintype.card {i // ext9 u i = κ} < 3))
    (hgp : g ^ p = 1) {a b : Fin 5} (ha : ext9 u a = κ) (hb : ext9 u b = κ) :
    mU g a b = (1 : Matrix (Fin 5) (Fin 5) K) a b := by
  have hbd := isBlockDiag_of_mem_centralizer hg
  have hu := fibBlk_unitary κ (iterateFrobenius K 2 3) hbd (mU_mem g).2
  have hpow : fibBlk (ext9 u) κ (mU g) ^ p = 1 := by
    rw [← fibBlk_pow κ hbd, ← mU_pow, hgp, mU_one, fibBlk_one]
  have hB : fibBlk (ext9 u) κ (mU g) = 1 := by
    rcases hp with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · exact eq_one_of_pow_five_of_card_lt card_K_eq hu hpow hc
    · exact eq_one_of_pow_nineteen_of_card_lt card_K_eq hu hpow hc
  exact entry_of_fibBlk_eq_one κ hB ha hb

theorem eq_one_of_mem_centralizer_of_pow {u : Fin 4 → ZMod 9} {g : SUI}
    (hg : g ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) {p : ℕ}
    (hp : (p = 5 ∧ ∀ κ, Fintype.card {i // ext9 u i = κ} < 4) ∨
      (p = 19 ∧ ∀ κ, Fintype.card {i // ext9 u i = κ} < 3))
    (hgp : g ^ p = 1) : g = 1 := by
  apply mU_injective
  rw [mU_one]
  refine eq_one_of_blocks (t := ext9 u) (isBlockDiag_of_mem_centralizer hg) fun a b hab => ?_
  refine block_eq_one_of_pow hg (ext9 u a) ?_ hgp rfl hab.symm
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2 _⟩
  · exact Or.inr ⟨h1, h2 _⟩

theorem mem_idOutsideSU_of_pow_nineteen {u : Fin 4 → ZMod 9} {g : SUI}
    (hg : g ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) (κ₀ : ZMod 9)
    (hsmall : ∀ κ, κ ≠ κ₀ → Fintype.card {i // ext9 u i = κ} < 3) (hgp : g ^ 19 = 1) :
    g ∈ idOutsideSU {i | ext9 u i = κ₀} := by
  show IsIdOutside _ (mU g)
  intro a b hab
  by_cases h : ext9 u a = ext9 u b
  · have hκ : ext9 u a ≠ κ₀ := by
      rcases hab with ha | hb
      · exact ha
      · rw [h]
        exact hb
    exact block_eq_one_of_pow hg (ext9 u a) (Or.inr ⟨rfl, hsmall _ hκ⟩) hgp rfl h.symm
  · rw [isBlockDiag_of_mem_centralizer hg a b h,
      Matrix.one_apply_ne (fun e => h (congrArg (ext9 u) e))]

theorem commutator_mem_idOutsideSU {u : Fin 4 → ZMod 9} {j : Fin 5} {κ₀ : ZMod 9}
    (hj : ∀ k, ext9 u k = ext9 u j → k = j) (hκ : ∀ k, k ≠ j → ext9 u k = κ₀) {a b : SUI}
    (ha : a ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI))
    (hb : b ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) :
    ⁅a, b⁆ ∈ idOutsideSU {i | ext9 u i = κ₀} := by
  set C := Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) with hC
  have hjj : ∀ x ∈ C, ∀ y : SUI, mU (x * y) j j = mU x j j * mU y j j := fun x hx y => by
    rw [mU_mul]
    exact mul_apply_singleton (isBlockDiag_of_mem_centralizer hx) hj
  have hinv : ∀ x ∈ C, mU x j j * mU x⁻¹ j j = 1 := fun x hx => by
    rw [← hjj x hx x⁻¹, mul_inv_cancel, mU_one, Matrix.one_apply_eq]
  have hab : a * b ∈ C := C.mul_mem ha hb
  have haba : a * b * a⁻¹ ∈ C := C.mul_mem hab (C.inv_mem ha)
  have hc : ⁅a, b⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem haba (C.inv_mem hb)
  have hcjj : mU ⁅a, b⁆ j j = 1 := by
    rw [commutatorElement_def, hjj _ haba, hjj _ hab, hjj _ ha]
    have h1 := hinv a ha
    have h2 := hinv b hb
    linear_combination (mU b j j * mU b⁻¹ j j) * h1 + h2
  show IsIdOutside _ (mU ⁅a, b⁆)
  intro x y hxy
  have hbd := isBlockDiag_of_mem_centralizer hc
  by_cases hxy' : x = y
  · subst hxy'
    have hxj : x = j := by
      by_contra hne
      have hx := hκ x hne
      rcases hxy with h | h <;> exact h hx
    subst hxj
    rw [hcjj, Matrix.one_apply_eq]
  · by_cases h : ext9 u x = ext9 u y
    · exfalso
      have hxj : x ≠ j := fun e => hxy' (by rw [e]; exact (hj y (by rw [← h, e])).symm)
      have hyj : y ≠ j := fun e => hxy' (by rw [e]; exact hj x (by rw [h, e]))
      rcases hxy with h' | h'
      · exact h' (hκ x hxj)
      · exact h' (hκ y hyj)
    · rw [hbd x y h, Matrix.one_apply_ne hxy']

theorem idOutsideSU_eq_range {u : Fin 4 → ZMod 9} {κ : ZMod 9} {k : ℕ} (f : Fin k → Fin 5)
    (hf : Function.Injective f) (hfib : Set.range f = {i | ext9 u i = κ}) (hk : 1 ≤ k) :
    idOutsideSU {i | ext9 u i = κ} = (embedSU hf card_K hk (by norm_num : 1 ≤ 5)).range := by
  ext x
  rw [mem_range_embedSU_iff, hfib]
  exact Iff.rfl

theorem isQuasisimple_idOutsideSU {u : Fin 4 → ZMod 9} {κ : ZMod 9} {k : ℕ} (f : Fin k → Fin 5)
    (hf : Function.Injective f) (hfib : Set.range f = {i | ext9 u i = κ}) (hk : 2 ≤ k) :
    CFSG.IsQuasisimple (idOutsideSU {i | ext9 u i = κ}) := by
  rw [idOutsideSU_eq_range f hf hfib (by omega)]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (embedSU_injective hf card_K _ _)) (isQuasisimple_SU hk)

theorem card_idOutsideSU {u : Fin 4 → ZMod 9} {κ : ZMod 9} {k : ℕ} (f : Fin k → Fin 5)
    (hf : Function.Injective f) (hfib : Set.range f = {i | ext9 u i = κ}) (hk : 1 ≤ k) :
    Nat.card (idOutsideSU {i | ext9 u i = κ}) = Nat.card (StatedSU k (2 ^ 3) K) := by
  rw [idOutsideSU_eq_range f hf hfib hk]
  exact (Nat.card_congr (MonoidHom.ofInjective (embedSU_injective hf card_K hk
    (by norm_num : 1 ≤ 5))).toEquiv).symm

section Order

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem card_statedSU_eq_int {F : Type} [Field F] {p f : ℕ} (h : UnitaryFieldData p f F) {n : ℕ}
    (hn : 1 ≤ n) :
    (Nat.card ↥(StatedSU n (p ^ f) F) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) F)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  rw [show StatedSU n (p ^ f) F = unitarySU p f F n from rfl, unitarySU_eq_gramSU h, card_gramSU,
    hU]

theorem card_SU4_eight : Nat.card (StatedSU 4 (2 ^ 3) K) = 8 ^ 6 * (63 * (513 * 4095)) := by
  have h := card_statedSU_eq_int hK (n := 4) (by norm_num)
  have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e] at h
  simp at h
  norm_num at h
  exact_mod_cast h

end Order

theorem thirteen_dvd_card_SU4 : 13 ∣ Nat.card (StatedSU 4 (2 ^ 3) K) := by
  rw [card_SU4_eight]
  norm_num

theorem exists_conj_mem_A0 {s : SUI} (hs3 : s ^ 3 = 1) : ∃ x : SUI, x * s * x⁻¹ ∈ A0 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_SUI
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  obtain ⟨z, hz⟩ := hfuse _ (CFSG.Open.isElemAbelian_zpowers hs3)
  have hT81 : Nat.card T ≤ 3 ^ 4 := maxEA_SUI.1 T hTe
  have hyT : A0.map (MulAut.conj y).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hy (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, card_A0]
      exact hT81)
  have h1 : z * s * z⁻¹ ∈ T := hz ⟨s, Subgroup.mem_zpowers s, rfl⟩
  rw [← hyT] at h1
  obtain ⟨a, ha, hya⟩ := h1
  have hya' : y * a * y⁻¹ = z * s * z⁻¹ := hya
  refine ⟨y⁻¹ * z, ?_⟩
  have e : y⁻¹ * z * s * (y⁻¹ * z)⁻¹ = a := by
    calc y⁻¹ * z * s * (y⁻¹ * z)⁻¹ = y⁻¹ * (z * s * z⁻¹) * y := by group
      _ = y⁻¹ * (y * a * y⁻¹) * y := by rw [hya']
      _ = a := by group
  rw [e]
  exact ha

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
