module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CSmallAux_cc_ne_zero {p : ℕ} [Fact p.Prime] {x : ZMod p}
    (h : x = 1 ∨ x = -1) : x ≠ 0 := by
  rcases h with h | h
  · rw [h]; exact one_ne_zero
  · rw [h]; exact neg_ne_zero.mpr one_ne_zero

private lemma hdRo7CSmallAux_cc_sq {p : ℕ} [Fact p.Prime] {x : ZMod p}
    (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with h | h <;> rw [h] <;> ring

lemma hdRo7CSmallAux_zmod3_ne_zero {x : ZMod 3} (h : x ≠ 0) : x = 1 ∨ x = -1 := by
  have h3 : ∀ y : ZMod 3, y = 1 ∨ y = -1 ∨ y = 0 := by decide
  rcases h3 x with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · exact absurd h' h

lemma hdRo7CSmallAux_zmod3_sq {x : ZMod 3} (h : x ≠ 0) : x * x = 1 :=
  hdRo7CSmallAux_cc_sq (p := 3) (hdRo7CSmallAux_zmod3_ne_zero h)

lemma hdRo7CSmallAux_zmod3_negtwo_ne : (-2 : ZMod 3) ≠ 0 := by decide

lemma hdRo7CSmallAux_zmod3_sum : (-1 : ZMod 3) - 1 + 0 + 0 = 1 := by decide

lemma hdRo7CSmallAux_zmod3_m13 : (2 : ZMod 3) - (-1) * 3 = -1 := by decide

private lemma hdRo7CSmallAux_sign_sq {x : ZMod 3} (h : x ≠ 0) : x * (-1 * x) = -1 := by
  rcases hdRo7CSmallAux_zmod3_ne_zero h with h | h <;> rw [h] <;> ring

private lemma hdRo7CSmallAux_zmod3_sum' : (-1 : ZMod 3) + -1 + 0 + 0 = 1 := by decide

noncomputable def hdRo7CSmallAux_signedPerm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (σ : Equiv.Perm (Fin (n + 1))) (cc : Fin (n + 1) → ZMod p)
    (hcc : ∀ i, cc i = 1 ∨ cc i = -1) : V ≃ₗ[ZMod p] V :=
  b.equiv (b.unitsSMul (fun i => Units.mk0 (cc (σ.symm i))
    (hdRo7CSmallAux_cc_ne_zero (hcc (σ.symm i))))) σ

lemma hdRo7CSmallAux_signedPerm_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (σ : Equiv.Perm (Fin (n + 1))) (cc : Fin (n + 1) → ZMod p)
    (hcc : ∀ i, cc i = 1 ∨ cc i = -1) (i : Fin (n + 1)) :
    hdRo7CSmallAux_signedPerm b σ cc hcc (b i) = cc i • b (σ i) := by
  simp only [hdRo7CSmallAux_signedPerm, Module.Basis.equiv_apply,
    Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply, Units.smul_def, Units.val_mk0]

lemma hdRo7CSmallAux_signedPerm_inv
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (σ : Equiv.Perm (Fin (n + 1))) (cc : Fin (n + 1) → ZMod p)
    (hcc : ∀ i, cc i = 1 ∨ cc i = -1) :
    (hdRo7CSmallAux_signedPerm b σ cc hcc)⁻¹ =
      hdRo7CSmallAux_signedPerm b σ.symm (cc ∘ σ.symm) (fun i => hcc (σ.symm i)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply (LinearEquiv.toLinearMap_inj).mp
  apply Module.Basis.ext
  intro i
  change ((hdRo7CSmallAux_signedPerm b σ cc hcc) *
      (hdRo7CSmallAux_signedPerm b σ.symm (cc ∘ σ.symm) (fun i => hcc (σ.symm i)))) (b i) =
    (1 : V ≃ₗ[ZMod p] V) (b i)
  rw [LinearEquiv.mul_apply, hdRo7CSmallAux_signedPerm_apply, map_smul,
    hdRo7CSmallAux_signedPerm_apply, Equiv.apply_symm_apply]
  simp only [Function.comp_apply]
  rw [smul_smul, hdRo7CSmallAux_cc_sq (hcc (σ.symm i)), one_smul]
  rfl

lemma hdRo7CSmallAux_signedPerm_c2sp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (σ : Equiv.Perm (Fin (n + 1))) (cc : Fin (n + 1) → ZMod p)
    (hcc : ∀ i, cc i = 1 ∨ cc i = -1) (hσ0 : σ 0 = 0) (hc0 : cc 0 = 1) :
    C2SP p b (hdRo7CSmallAux_signedPerm b σ cc hcc) :=
  ⟨σ, cc, hσ0, hc0, hcc, fun i => hdRo7CSmallAux_signedPerm_apply b σ cc hcc i⟩

lemma hdRo7CSmallAux_coord_smul_basis
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (k j : Fin (n + 1)) (x : ZMod p) :
    b.coord k (x • b j) = if j = k then x else 0 := by
  rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  by_cases h : j = k
  · simp [h]
  · simp [h]

lemma hdRo7CSmallAux_sum_repr_insert
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (u : V) (S : Finset (Fin (n + 1)))
    (hS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0) :
    u = ∑ i ∈ insert 0 S, b.coord i u • b i := by
  conv_lhs => rw [← Module.Basis.sum_repr b u]
  refine (Finset.sum_subset (s₁ := insert 0 S) (s₂ := Finset.univ)
    (f := fun i => b.coord i u • b i) (Finset.subset_univ (insert 0 S)) ?_).symm
  intro x _ hx
  rw [Finset.mem_insert, not_or] at hx
  obtain ⟨hx0, hxS⟩ := hx
  have : b.coord x u = 0 := by
    by_contra hc
    exact hxS ((hS x).mpr ⟨hx0, hc⟩)
  rw [this, zero_smul]

private lemma hdRo7CSmallAux_compl_card {n : ℕ} (S : Finset (Fin (n + 1)))
    (h0 : (0 : Fin (n + 1)) ∉ S) :
    (Finset.univ \ insert 0 S).card = n - S.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
    Finset.card_insert_of_notMem h0, Finset.card_univ, Fintype.card_fin]
  omega

lemma hdRo7CSmallAux_exists_two_free {n : ℕ} (S : Finset (Fin (n + 1)))
    (h0 : (0 : Fin (n + 1)) ∉ S) (hk : S.card ≤ 3) (hn : 5 ≤ n) :
    ∃ j1 j2 : Fin (n + 1), j1 ≠ j2 ∧ j1 ∉ insert 0 S ∧ j2 ∉ insert 0 S := by
  have hc : 1 < (Finset.univ \ insert 0 S).card := by
    rw [hdRo7CSmallAux_compl_card S h0]; omega
  obtain ⟨j1, hj1, j2, hj2, hj12⟩ := Finset.one_lt_card.mp hc
  exact ⟨j1, j2, hj12, (Finset.mem_sdiff.mp hj1).2, (Finset.mem_sdiff.mp hj2).2⟩

lemma hdRo7CSmallAux_exists_one_free {n : ℕ} (S : Finset (Fin (n + 1)))
    (h0 : (0 : Fin (n + 1)) ∉ S) (hk : S.card ≤ 4) (hn : 5 ≤ n) :
    ∃ j1 : Fin (n + 1), j1 ∉ insert 0 S := by
  have hc : 0 < (Finset.univ \ insert 0 S).card := by
    rw [hdRo7CSmallAux_compl_card S h0]; omega
  obtain ⟨j1, hj1⟩ := Finset.card_pos.mp hc
  exact ⟨j1, (Finset.mem_sdiff.mp hj1).2⟩

lemma hdRo7CSmallAux_case_m13
    {n : ℕ} (hn : 5 ≤ n) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = -1 * b.coord i u)
    (S : Finset (Fin (n + 1))) (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (h0S : (0 : Fin (n + 1)) ∉ S) (hScard : S.card = 3) (hu0 : b.coord 0 u = -1) :
    False := by
  obtain ⟨i1, i2, i3, hd12, hd13, hd23, hSeq⟩ := Finset.card_eq_three.mp hScard
  have hi1 : i1 ∈ S := by rw [hSeq]; simp
  have hi2 : i2 ∈ S := by rw [hSeq]; simp
  have hi3 : i3 ∈ S := by rw [hSeq]; simp
  have hi1ne : i1 ≠ 0 := ((hS_mem i1).mp hi1).1
  have hi2ne : i2 ≠ 0 := ((hS_mem i2).mp hi2).1
  have hi3ne : i3 ≠ 0 := ((hS_mem i3).mp hi3).1
  have ha1ne : b.coord i1 u ≠ 0 := ((hS_mem i1).mp hi1).2
  have ha2ne : b.coord i2 u ≠ 0 := ((hS_mem i2).mp hi2).2
  have ha3ne : b.coord i3 u ≠ 0 := ((hS_mem i3).mp hi3).2
  obtain ⟨j1, j2, hj12, hfj1, hfj2⟩ :=
    hdRo7CSmallAux_exists_two_free S h0S (by omega) hn
  have hj1S : j1 ∉ S := fun h => hfj1 (Finset.mem_insert_of_mem h)
  have hj2S : j2 ∉ S := fun h => hfj2 (Finset.mem_insert_of_mem h)
  have hj1ne : j1 ≠ 0 := fun h => hfj1 (h ▸ Finset.mem_insert_self 0 S)
  have hj2ne : j2 ≠ 0 := fun h => hfj2 (h ▸ Finset.mem_insert_self 0 S)
  have hcj1 : b.coord j1 u = 0 := by
    by_contra hc; exact hj1S ((hS_mem j1).mpr ⟨hj1ne, hc⟩)
  have hcj2 : b.coord j2 u = 0 := by
    by_contra hc; exact hj2S ((hS_mem j2).mpr ⟨hj2ne, hc⟩)
  have hi1j1 : i1 ≠ j1 := fun h => hj1S (h ▸ hi1)
  have hi1j2 : i1 ≠ j2 := fun h => hj2S (h ▸ hi1)
  have hi2j1 : i2 ≠ j1 := fun h => hj1S (h ▸ hi2)
  have hi2j2 : i2 ≠ j2 := fun h => hj2S (h ▸ hi2)
  have hi3j1 : i3 ≠ j1 := fun h => hj1S (h ▸ hi3)
  have hi3j2 : i3 ≠ j2 := fun h => hj2S (h ▸ hi3)
  have h0i1 : (0 : Fin (n + 1)) ≠ i1 := fun h => hi1ne h.symm
  have h0i2 : (0 : Fin (n + 1)) ≠ i2 := fun h => hi2ne h.symm
  have h0i3 : (0 : Fin (n + 1)) ≠ i3 := fun h => hi3ne h.symm
  have h0j1 : (0 : Fin (n + 1)) ≠ j1 := fun h => hj1ne h.symm
  have h0j2 : (0 : Fin (n + 1)) ≠ j2 := fun h => hj2ne h.symm
  have hj1i1 : j1 ≠ i1 := fun h => hi1j1 h.symm
  have hj1i2 : j1 ≠ i2 := fun h => hi2j1 h.symm
  have hj1i3 : j1 ≠ i3 := fun h => hi3j1 h.symm
  have hj2i1 : j2 ≠ i1 := fun h => hi1j2 h.symm
  have hj2i2 : j2 ≠ i2 := fun h => hi2j2 h.symm
  have hj2i3 : j2 ≠ i3 := fun h => hi3j2 h.symm
  have hi2i1 : i2 ≠ i1 := fun h => hd12 h.symm
  have hi3i1 : i3 ≠ i1 := fun h => hd13 h.symm
  have hi3i2 : i3 ≠ i2 := fun h => hd23 h.symm
  have hj2j1 : j2 ≠ j1 := fun h => hj12 h.symm
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i2 j1 * Equiv.swap i3 j2
  let cc : Fin (n + 1) → ZMod 3 := fun _ => 1
  have hcc : ∀ j, cc j = 1 ∨ cc j = -1 := fun _ => Or.inl rfl
  have hσ0 : σ 0 = 0 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [h0i2, h0j1, h0i3, h0j2]
  have hc0 : cc 0 = 1 := rfl
  have hσi1 : σ i1 = i1 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hd12, hi1j1, hd13, hi1j2]
  have hσi2 : σ i2 = j1 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hi2j2, hd12, hd23, hi2j1]
  have hσi3 : σ i3 = j2 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hd23, hi3j2, hd13, hi3j1, hj2i2, hj2j1]
  have hcc1 : cc i1 = 1 := rfl
  have hcc2 : cc i2 = 1 := rfl
  have hcc3 : cc i3 = 1 := rfl
  let h : V ≃ₗ[ZMod 3] V := hdRo7CSmallAux_signedPerm b σ cc hcc
  have hh : h = hdRo7CSmallAux_signedPerm b σ cc hcc := rfl
  have hsp : C2SP 3 b h := by
    rw [hh]; exact hdRo7CSmallAux_signedPerm_c2sp b σ cc hcc hσ0 hc0
  have hb0 : h (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσ0, hc0, one_smul]
  have hbi1 : h (b i1) = b i1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi1, hcc1, one_smul]
  have hbi2 : h (b i2) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi2, hcc2, one_smul]
  have hbi3 : h (b i3) = b j2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi3, hcc3, one_smul]
  have hu3 : u = b.coord 0 u • b 0 + b.coord i1 u • b i1
      + b.coord i2 u • b i2 + b.coord i3 u • b i3 := by
    conv_lhs => rw [hdRo7CSmallAux_sum_repr_insert b u S hS_mem]
    rw [hSeq]
    simp [Finset.sum_insert, h0i1, h0i2, h0i3, hd12, hd13, hd23]
    abel
  have hhu : h u = b.coord 0 u • b 0 + b.coord i1 u • b i1
      + b.coord i2 u • b j1 + b.coord i3 u • b j2 := by
    conv_lhs => rw [hu3]
    simp only [map_add, map_smul]
    rw [hb0, hbi1, hbi2, hbi3]
  have hphi : φ (h u) = 1 := by
    rw [hhu]
    simp only [map_add, map_smul, smul_eq_mul, hnf.hφ0, hcoef i1 hi1ne, hcoef j1 hj1ne,
      hcoef j2 hj2ne, hcj1, hcj2, mul_zero, add_zero]
    rw [hu0, hdRo7CSmallAux_sign_sq ha1ne]
    exact hdRo7CSmallAux_zmod3_sum'
  have hinv0 : h⁻¹ (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0i2, h0i3, h0j1, h0j2]
  have hinv1 : h⁻¹ (b i1) = b i1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0i2, h0i3, h0j1, h0j2, hd12, hi2i1, hd13, hi3i1, hd23, hi3i2, hi1j1, hj1i1, hi2j1, hj1i2, hi3j1, hj1i3, hi1j2, hj2i1, hi2j2, hj2i2, hi3j2, hj2i3, hj12, hj2j1]
  have hinv2 : h⁻¹ (b i2) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0i2, h0i3, h0j1, h0j2, hd12, hi2i1, hd13, hi3i1, hd23, hi3i2, hi1j1, hj1i1, hi2j1, hj1i2, hi3j1, hj1i3, hi1j2, hj2i1, hi2j2, hj2i2, hi3j2, hj2i3, hj12, hj2j1]
  have hinv3 : h⁻¹ (b i3) = b j2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0i2, h0i3, h0j1, h0j2, hd12, hi2i1, hd13, hi3i1, hd23, hi3i2, hi1j1, hj1i1, hi2j1, hj1i2, hi3j1, hj1i3, hi1j2, hj2i1, hi2j2, hj2i2, hi3j2, hj2i3, hj12, hj2j1]
  have hhu_inv : h⁻¹ u = b.coord 0 u • b 0 + b.coord i1 u • b i1
      + b.coord i2 u • b j1 + b.coord i3 u • b j2 := by
    conv_lhs => rw [hu3]
    simp only [map_add, map_smul, hinv0, hinv1, hinv2, hinv3]
  have hphi_inv : φ (h⁻¹ u) = 1 := by rw [hhu_inv, ← hhu]; exact hphi
  have hcard : 3 ≤ (Finset.univ.filter fun i => b.coord i (h u - u) ≠ 0).card := by
    have hd : h u - u = (b.coord i2 u) • b j1 + (b.coord i3 u) • b j2
        - (b.coord i2 u) • b i2 - (b.coord i3 u) • b i3 := by
      conv_lhs => rw [hhu]
      conv_lhs => arg 2; rw [hu3]
      module
    have hc2 : b.coord i2 (h u - u) = -(b.coord i2 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj1i2, hj2i2, hi3i2]
    have hc2' : b.coord i2 (h u - u) ≠ 0 := by
      rw [hc2]; exact neg_ne_zero.mpr ha2ne
    have hc3 : b.coord j1 (h u - u) = b.coord i2 u := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj2j1, hi2j1, hi3j1]
    have hc3' : b.coord j1 (h u - u) ≠ 0 := by
      rw [hc3]; exact ha2ne
    have hc4 : b.coord i3 (h u - u) = -(b.coord i3 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj1i3, hj2i3, hd23]
    have hc4' : b.coord i3 (h u - u) ≠ 0 := by
      rw [hc4]; exact neg_ne_zero.mpr ha3ne
    have hsub : ({i2, j1, i3} : Finset (Fin (n + 1))) ⊆
        Finset.univ.filter (fun i => b.coord i (h u - u) ≠ 0) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | rfl | rfl
      · exact ⟨Finset.mem_univ _, hc2'⟩
      · exact ⟨Finset.mem_univ _, hc3'⟩
      · exact ⟨Finset.mem_univ _, hc4'⟩
    have h3 : ({i2, j1, i3} : Finset (Fin (n + 1))).card = 3 :=
      Finset.card_eq_three.mpr ⟨i2, j1, i3, hi2j1, hd23, hj1i3, rfl⟩
    calc (3 : ℕ) = ({i2, j1, i3} : Finset (Fin (n + 1))).card := h3.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle := hT hSp 3 rfl n hn V b A hPA hStab
    r u φ hnf h hsp hphi hphi_inv
  omega

end CFSG.StandardType.HdRo7C
