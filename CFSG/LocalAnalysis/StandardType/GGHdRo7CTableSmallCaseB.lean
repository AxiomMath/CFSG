module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallAux

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CSmallAux_case_c1_k3
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = 1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 3) (hu0val : b.coord 0 u = -1) :
    False := by
  have h0S : (0 : Fin (n + 1)) ∉ S := by rw [hS_mem]; simp
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
  have hi2i1 : i2 ≠ i1 := fun h => hd12 h.symm
  have hi3i1 : i3 ≠ i1 := fun h => hd13 h.symm
  have hj1i1 : j1 ≠ i1 := fun h => hi1j1 h.symm
  have hj2i1 : j2 ≠ i1 := fun h => hi1j2 h.symm
  have hi3i2 : i3 ≠ i2 := fun h => hd23 h.symm
  have hj1i2 : j1 ≠ i2 := fun h => hi2j1 h.symm
  have hj2i2 : j2 ≠ i2 := fun h => hi2j2 h.symm
  have hj1i3 : j1 ≠ i3 := fun h => hi3j1 h.symm
  have hj2j1 : j2 ≠ j1 := fun h => hj12 h.symm
  have hj2i3 : j2 ≠ i3 := fun h => hi3j2 h.symm
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i2 j1 * Equiv.swap i3 j2
  let cc : Fin (n + 1) → ZMod 3 := fun j => if j = i1 then -1 else 1
  have hcc : ∀ j, cc j = 1 ∨ cc j = -1 := by
    intro j; by_cases h : j = i1 <;> simp [cc, h]
  have hσ0 : σ 0 = 0 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [h0i2, h0j1, h0i3, h0j2]
  have hc0 : cc 0 = 1 := by simp [cc, h0i1]
  have hσi1 : σ i1 = i1 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hd12, hi1j1, hd13, hi1j2]
  have hσi2 : σ i2 = j1 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hi2j2, hd12, hd23, hi2j1]
  have hσi3 : σ i3 = j2 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hd23, hi3j2, hd13, hi3j1, hj2i2, hj2j1]
  have hcc1 : cc i1 = -1 := by simp [cc]
  have hcc2 : cc i2 = 1 := by simp [cc, hi2i1]
  have hcc3 : cc i3 = 1 := by simp [cc, hi3i1]
  let h : V ≃ₗ[ZMod 3] V := hdRo7CSmallAux_signedPerm b σ cc hcc
  have hh : h = hdRo7CSmallAux_signedPerm b σ cc hcc := rfl
  have hsp : C2SP 3 b h := by
    rw [hh]; exact hdRo7CSmallAux_signedPerm_c2sp b σ cc hcc hσ0 hc0
  have hb0 : h (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσ0, hc0, one_smul]
  have hbi1 : h (b i1) = -b i1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi1, hcc1]; simp
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
  have hhu : h u = b.coord 0 u • b 0 - b.coord i1 u • b i1
      + b.coord i2 u • b j1 + b.coord i3 u • b j2 := by
    conv_lhs => rw [hu3]
    simp only [map_add, map_smul, hb0, hbi1, hbi2, hbi3, smul_neg]
    abel
  have hphi : φ (h u) = 1 := by
    rw [hhu]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hnf.hφ0, hcoef i1 hi1ne,
      hcoef j1 hj1ne, hcoef j2 hj2ne, hcj1, hcj2, mul_one, one_mul, mul_zero]
    rw [hdRo7CSmallAux_zmod3_sq ha1ne, hu0val]
    exact hdRo7CSmallAux_zmod3_sum
  have hinv0 : h⁻¹ (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0i2, h0i3, h0j1, h0j2, hd12, hi2i1, hd13, hi3i1, hd23, hi3i2, hi1j1, hj1i1, hi2j1, hj1i2, hi3j1, hj1i3, hi1j2, hj2i1, hi2j2, hj2i2, hi3j2, hj2i3, hj12, hj2j1]
  have hinv1 : h⁻¹ (b i1) = -b i1 := by
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
  have hhu_inv : h⁻¹ u = b.coord 0 u • b 0 - b.coord i1 u • b i1
      + b.coord i2 u • b j1 + b.coord i3 u • b j2 := by
    conv_lhs => rw [hu3]
    simp only [map_add, map_smul, hinv0, hinv1, hinv2, hinv3, smul_neg]
    abel
  have hphi_inv : φ (h⁻¹ u) = 1 := by rw [hhu_inv, ← hhu]; exact hphi
  have hcard : 3 ≤ (Finset.univ.filter fun i => b.coord i (h u - u) ≠ 0).card := by
    have hd : h u - u = (-2 * (b.coord i1 u)) • b i1 + (b.coord i2 u) • b j1
        - (b.coord i2 u) • b i2 + (b.coord i3 u) • b j2 - (b.coord i3 u) • b i3 := by
      conv_lhs => rw [hhu]
      conv_lhs => arg 2; rw [hu3]
      module
    have hc1 : b.coord i1 (h u - u) = -2 * (b.coord i1 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj1i1, hi2i1, hj2i1, hi3i1]
    have hc1' : b.coord i1 (h u - u) ≠ 0 := by
      rw [hc1]; exact mul_ne_zero hdRo7CSmallAux_zmod3_negtwo_ne ha1ne
    have hc2 : b.coord i2 (h u - u) = -(b.coord i2 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hd12, hj1i2, hj2i2, hi3i2]
    have hc2' : b.coord i2 (h u - u) ≠ 0 := by
      rw [hc2]; exact neg_ne_zero.mpr ha2ne
    have hc3 : b.coord j1 (h u - u) = b.coord i2 u := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hi1j1, hi2j1, hi3j1, hj2j1]
    have hc3' : b.coord j1 (h u - u) ≠ 0 := by
      rw [hc3]; exact ha2ne
    have hsub : ({i1, i2, j1} : Finset (Fin (n + 1))) ⊆
        Finset.univ.filter (fun i => b.coord i (h u - u) ≠ 0) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | rfl | rfl
      · exact ⟨Finset.mem_univ _, hc1'⟩
      · exact ⟨Finset.mem_univ _, hc2'⟩
      · exact ⟨Finset.mem_univ _, hc3'⟩
    have h3 : ({i1, i2, j1} : Finset (Fin (n + 1))).card = 3 :=
      Finset.card_eq_three.mpr ⟨i1, i2, j1, hd12, hi1j1, hi2j1, rfl⟩
    calc (3 : ℕ) = ({i1, i2, j1} : Finset (Fin (n + 1))).card := h3.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle := hT hSp 3 rfl n hn V b A hPA hStab
    r u φ hnf h hsp hphi hphi_inv
  omega

theorem hdRo7CSmallAux_case_c1_k4
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = 1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 4) (hu0val : b.coord 0 u = 1) :
    False := by
  have h0S : (0 : Fin (n + 1)) ∉ S := by rw [hS_mem]; simp
  exfalso
  obtain ⟨i1, i2, i3, i4, hd12, hd13, hd14, hd23, hd24, hd34, hSeq⟩ :=
    Finset.card_eq_four.mp hScard
  have hi1 : i1 ∈ S := by rw [hSeq]; simp
  have hi2 : i2 ∈ S := by rw [hSeq]; simp
  have hi3 : i3 ∈ S := by rw [hSeq]; simp
  have hi4 : i4 ∈ S := by rw [hSeq]; simp
  have hi1ne : i1 ≠ 0 := ((hS_mem i1).mp hi1).1
  have hi2ne : i2 ≠ 0 := ((hS_mem i2).mp hi2).1
  have hi3ne : i3 ≠ 0 := ((hS_mem i3).mp hi3).1
  have hi4ne : i4 ≠ 0 := ((hS_mem i4).mp hi4).1
  have ha1ne : b.coord i1 u ≠ 0 := ((hS_mem i1).mp hi1).2
  have ha2ne : b.coord i2 u ≠ 0 := ((hS_mem i2).mp hi2).2
  have ha3ne : b.coord i3 u ≠ 0 := ((hS_mem i3).mp hi3).2
  obtain ⟨j1, hfj1⟩ := hdRo7CSmallAux_exists_one_free S h0S (by omega) hn
  have hj1S : j1 ∉ S := fun h => hfj1 (Finset.mem_insert_of_mem h)
  have hj1ne : j1 ≠ 0 := fun h => hfj1 (h ▸ Finset.mem_insert_self 0 S)
  have hcj1 : b.coord j1 u = 0 := by
    by_contra hc; exact hj1S ((hS_mem j1).mpr ⟨hj1ne, hc⟩)
  have hi1j1 : i1 ≠ j1 := fun h => hj1S (h ▸ hi1)
  have hi2j1 : i2 ≠ j1 := fun h => hj1S (h ▸ hi2)
  have hi3j1 : i3 ≠ j1 := fun h => hj1S (h ▸ hi3)
  have hi4j1 : i4 ≠ j1 := fun h => hj1S (h ▸ hi4)
  have h0i1 : (0 : Fin (n + 1)) ≠ i1 := fun h => hi1ne h.symm
  have h0i2 : (0 : Fin (n + 1)) ≠ i2 := fun h => hi2ne h.symm
  have h0i3 : (0 : Fin (n + 1)) ≠ i3 := fun h => hi3ne h.symm
  have h0i4 : (0 : Fin (n + 1)) ≠ i4 := fun h => hi4ne h.symm
  have h0j1 : (0 : Fin (n + 1)) ≠ j1 := fun h => hj1ne h.symm
  have hj1i1 : j1 ≠ i1 := fun h => hi1j1 h.symm
  have hj1i2 : j1 ≠ i2 := fun h => hi2j1 h.symm
  have hj1i3 : j1 ≠ i3 := fun h => hi3j1 h.symm
  have hj1i4 : j1 ≠ i4 := fun h => hi4j1 h.symm
  have hi2i1 : i2 ≠ i1 := fun h => hd12 h.symm
  have hi3i1 : i3 ≠ i1 := fun h => hd13 h.symm
  have hi3i2 : i3 ≠ i2 := fun h => hd23 h.symm
  have hi4i1 : i4 ≠ i1 := fun h => hd14 h.symm
  have hi4i2 : i4 ≠ i2 := fun h => hd24 h.symm
  have hi4i3 : i4 ≠ i3 := fun h => hd34 h.symm
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i4 j1
  let cc : Fin (n + 1) → ZMod 3 :=
    fun j => if j ∈ ({i1, i2, i3} : Finset (Fin (n + 1))) then -1 else 1
  have hcc : ∀ j, cc j = 1 ∨ cc j = -1 := by
    intro j
    by_cases h : j ∈ ({i1, i2, i3} : Finset (Fin (n + 1)))
    · right
      change (if j ∈ ({i1, i2, i3} : Finset (Fin (n + 1))) then (-1 : ZMod 3) else 1) = -1
      rw [if_pos h]
    · left
      change (if j ∈ ({i1, i2, i3} : Finset (Fin (n + 1))) then (-1 : ZMod 3) else 1) = 1
      rw [if_neg h]
  have hσ0 : σ 0 = 0 := by
    simp only [σ, Equiv.swap_apply_def]; simp [h0i4, h0j1]
  have hc0 : cc 0 = 1 := by simp [cc, h0i1, h0i2, h0i3]
  have hσi1 : σ i1 = i1 := by
    simp only [σ, Equiv.swap_apply_def]; simp [hi1j1, hd14]
  have hσi2 : σ i2 = i2 := by
    simp only [σ, Equiv.swap_apply_def]; simp [hi2j1, hd24]
  have hσi3 : σ i3 = i3 := by
    simp only [σ, Equiv.swap_apply_def]; simp [hi3j1, hd34]
  have hσi4 : σ i4 = j1 := by simp [σ]
  have hcc1 : cc i1 = -1 := by simp [cc]
  have hcc2 : cc i2 = -1 := by simp [cc]
  have hcc3 : cc i3 = -1 := by simp [cc]
  have hcc4 : cc i4 = 1 := by simp [cc, hi4i1, hi4i2, hi4i3]
  let h : V ≃ₗ[ZMod 3] V := hdRo7CSmallAux_signedPerm b σ cc hcc
  have hh : h = hdRo7CSmallAux_signedPerm b σ cc hcc := rfl
  have hsp : C2SP 3 b h := by
    rw [hh]; exact hdRo7CSmallAux_signedPerm_c2sp b σ cc hcc hσ0 hc0
  have hb0 : h (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσ0, hc0, one_smul]
  have hbi1 : h (b i1) = -b i1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi1, hcc1]; simp
  have hbi2 : h (b i2) = -b i2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi2, hcc2]; simp
  have hbi3 : h (b i3) = -b i3 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi3, hcc3]; simp
  have hbi4 : h (b i4) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi4, hcc4, one_smul]
  have hu4 : u = b.coord 0 u • b 0 + b.coord i1 u • b i1 + b.coord i2 u • b i2
      + b.coord i3 u • b i3 + b.coord i4 u • b i4 := by
    conv_lhs => rw [hdRo7CSmallAux_sum_repr_insert b u S hS_mem]
    rw [hSeq]
    simp [Finset.sum_insert, h0i1, h0i2, h0i3, h0i4, hd12, hd13, hd14, hd23, hd24, hd34]
    abel
  have hhu : h u = b.coord 0 u • b 0 - b.coord i1 u • b i1 - b.coord i2 u • b i2
      - b.coord i3 u • b i3 + b.coord i4 u • b j1 := by
    conv_lhs => rw [hu4]
    simp only [map_add, map_smul, hb0, hbi1, hbi2, hbi3, hbi4, smul_neg]
    abel
  have hphi : φ (h u) = 1 := by
    rw [hhu]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hnf.hφ0, hcoef i1 hi1ne,
      hcoef i2 hi2ne, hcoef i3 hi3ne, hcoef j1 hj1ne, hcj1, mul_one, one_mul, mul_zero]
    rw [hdRo7CSmallAux_zmod3_sq ha1ne, hdRo7CSmallAux_zmod3_sq ha2ne,
      hdRo7CSmallAux_zmod3_sq ha3ne, hu0val]
    exact hdRo7CSmallAux_zmod3_sum
  have hinv0 : h⁻¹ (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i4, h0j1, h0i1, h0i2, h0i3]
  have hinv1 : h⁻¹ (b i1) = -b i1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hi1j1, hd14, h0i1]
  have hinv2 : h⁻¹ (b i2) = -b i2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hi2j1, hd24, h0i2]
  have hinv3 : h⁻¹ (b i3) = -b i3 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hi3j1, hd34, h0i3]
  have hinv4 : h⁻¹ (b i4) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hi4j1, hi4i1, hi4i2, hi4i3,
      hj1i1, hj1i2, hj1i3]
  have hhu_inv : h⁻¹ u = b.coord 0 u • b 0 - b.coord i1 u • b i1 - b.coord i2 u • b i2
      - b.coord i3 u • b i3 + b.coord i4 u • b j1 := by
    conv_lhs => rw [hu4]
    simp only [map_add, map_smul, hinv0, hinv1, hinv2, hinv3, hinv4, smul_neg]
    abel
  have hphi_inv : φ (h⁻¹ u) = 1 := by rw [hhu_inv, ← hhu]; exact hphi
  have hcard : 3 ≤ (Finset.univ.filter fun i => b.coord i (h u - u) ≠ 0).card := by
    have hd : h u - u = (-2 * (b.coord i1 u)) • b i1 + (-2 * (b.coord i2 u)) • b i2
        + (-2 * (b.coord i3 u)) • b i3 + (b.coord i4 u) • b j1
        - (b.coord i4 u) • b i4 := by
      conv_lhs => rw [hhu]
      conv_lhs => arg 2; rw [hu4]
      module
    have hc1 : b.coord i1 (h u - u) = -2 * (b.coord i1 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hi2i1, hi3i1, hi4i1, hj1i1]
    have hc1' : b.coord i1 (h u - u) ≠ 0 := by
      rw [hc1]; exact mul_ne_zero hdRo7CSmallAux_zmod3_negtwo_ne ha1ne
    have hc2 : b.coord i2 (h u - u) = -2 * (b.coord i2 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hd12, hi3i2, hi4i2, hj1i2]
    have hc2' : b.coord i2 (h u - u) ≠ 0 := by
      rw [hc2]; exact mul_ne_zero hdRo7CSmallAux_zmod3_negtwo_ne ha2ne
    have hc3 : b.coord i3 (h u - u) = -2 * (b.coord i3 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hd13, hd23, hi4i3, hj1i3]
    have hc3' : b.coord i3 (h u - u) ≠ 0 := by
      rw [hc3]; exact mul_ne_zero hdRo7CSmallAux_zmod3_negtwo_ne ha3ne
    have hsub : ({i1, i2, i3} : Finset (Fin (n + 1))) ⊆
        Finset.univ.filter (fun i => b.coord i (h u - u) ≠ 0) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | rfl | rfl
      · exact ⟨Finset.mem_univ _, hc1'⟩
      · exact ⟨Finset.mem_univ _, hc2'⟩
      · exact ⟨Finset.mem_univ _, hc3'⟩
    have h3 : ({i1, i2, i3} : Finset (Fin (n + 1))).card = 3 :=
      Finset.card_eq_three.mpr ⟨i1, i2, i3, hd12, hd13, hd23, rfl⟩
    calc (3 : ℕ) = ({i1, i2, i3} : Finset (Fin (n + 1))).card := h3.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle := hT hSp 3 rfl n hn V b A hPA hStab
    r u φ hnf h hsp hphi hphi_inv
  omega

end CFSG.StandardType.HdRo7C
