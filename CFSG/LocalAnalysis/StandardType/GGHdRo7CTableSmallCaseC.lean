module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallAux

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CSmallAux_case_cm1_k2
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = -1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 2) (hu0val : b.coord 0 u = 1) :
    False := by
  have h0S : (0 : Fin (n + 1)) ∉ S := by rw [hS_mem]; simp
  exfalso
  obtain ⟨i1, i2, hd12, hSeq⟩ := Finset.card_eq_two.mp hScard
  have hi1 : i1 ∈ S := by rw [hSeq]; simp
  have hi2 : i2 ∈ S := by rw [hSeq]; simp
  have hi1ne : i1 ≠ 0 := ((hS_mem i1).mp hi1).1
  have hi2ne : i2 ≠ 0 := ((hS_mem i2).mp hi2).1
  have ha1ne : b.coord i1 u ≠ 0 := ((hS_mem i1).mp hi1).2
  have ha2ne : b.coord i2 u ≠ 0 := ((hS_mem i2).mp hi2).2
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
  have hi2j1 : i2 ≠ j1 := fun h => hj1S (h ▸ hi2)
  have hi1j2 : i1 ≠ j2 := fun h => hj2S (h ▸ hi1)
  have hi2j2 : i2 ≠ j2 := fun h => hj2S (h ▸ hi2)
  have h0i1 : (0 : Fin (n + 1)) ≠ i1 := fun h => hi1ne h.symm
  have h0i2 : (0 : Fin (n + 1)) ≠ i2 := fun h => hi2ne h.symm
  have h0j1 : (0 : Fin (n + 1)) ≠ j1 := fun h => hj1ne h.symm
  have h0j2 : (0 : Fin (n + 1)) ≠ j2 := fun h => hj2ne h.symm
  have hj1i1 : j1 ≠ i1 := fun h => hi1j1 h.symm
  have hj1i2 : j1 ≠ i2 := fun h => hi2j1 h.symm
  have hj2i1 : j2 ≠ i1 := fun h => hi1j2 h.symm
  have hj2i2 : j2 ≠ i2 := fun h => hi2j2 h.symm
  have hi2i1 : i2 ≠ i1 := fun h => hd12 h.symm
  have hj2j1 : j2 ≠ j1 := fun h => hj12 h.symm
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i1 j1 * Equiv.swap i2 j2
  let cc : Fin (n + 1) → ZMod 3 := fun _ => 1
  have hcc : ∀ j, cc j = 1 ∨ cc j = -1 := fun _ => Or.inl rfl
  have hσ0 : σ 0 = 0 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [h0i1, h0j1, h0i2, h0j2]
  have hc0 : cc 0 = 1 := rfl
  have hσi1 : σ i1 = j1 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hi1j2, hi1j1, hd12]
  have hσi2 : σ i2 = j2 := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [hi2j1, hi2j2, hd12, hj2i1, hj2j1]
  have hcc1 : cc i1 = 1 := rfl
  have hcc2 : cc i2 = 1 := rfl
  let h : V ≃ₗ[ZMod 3] V := hdRo7CSmallAux_signedPerm b σ cc hcc
  have hh : h = hdRo7CSmallAux_signedPerm b σ cc hcc := rfl
  have hsp : C2SP 3 b h := by
    rw [hh]; exact hdRo7CSmallAux_signedPerm_c2sp b σ cc hcc hσ0 hc0
  have hb0 : h (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσ0, hc0, one_smul]
  have hbi1 : h (b i1) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi1, hcc1, one_smul]
  have hbi2 : h (b i2) = b j2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_apply, hσi2, hcc2, one_smul]
  have hu2 : u = b.coord 0 u • b 0 + b.coord i1 u • b i1 + b.coord i2 u • b i2 := by
    conv_lhs => rw [hdRo7CSmallAux_sum_repr_insert b u S hS_mem]
    rw [hSeq]
    simp [Finset.sum_insert, h0i1, h0i2, hd12]
    abel
  have hhu : h u = b.coord 0 u • b 0 + b.coord i1 u • b j1 + b.coord i2 u • b j2 := by
    conv_lhs => rw [hu2]
    simp only [map_add, map_smul, hb0, hbi1, hbi2]
  have hphi : φ (h u) = 1 := by
    rw [hhu]
    simp only [map_add, map_smul, smul_eq_mul, hnf.hφ0, hcoef i1 hi1ne, hcoef i2 hi2ne,
      hcoef j1 hj1ne, hcoef j2 hj2ne, hcj1, hcj2, mul_one, one_mul, mul_zero, add_zero]
    rw [hu0val]
  have hinv0 : h⁻¹ (b 0) = b 0 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0j1, h0i2, h0j2, hd12, hi2i1, hi1j1, hj1i1, hi2j1, hj1i2, hi1j2, hj2i1, hi2j2, hj2i2, hj12, hj2j1]
  have hinv1 : h⁻¹ (b i1) = b j1 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0j1, h0i2, h0j2, hd12, hi2i1, hi1j1, hj1i1, hi2j1, hj1i2, hi1j2, hj2i1, hi2j2, hj2i2, hj12, hj2j1]
  have hinv2 : h⁻¹ (b i2) = b j2 := by
    rw [hh, hdRo7CSmallAux_signedPerm_inv, hdRo7CSmallAux_signedPerm_apply,
      show σ.symm = σ⁻¹ from rfl]
    simp only [Function.comp_apply]
    simp [σ, cc, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0i1, h0j1, h0i2, h0j2, hd12, hi2i1, hi1j1, hj1i1, hi2j1, hj1i2, hi1j2, hj2i1, hi2j2, hj2i2, hj12, hj2j1]
  have hhu_inv : h⁻¹ u = b.coord 0 u • b 0 + b.coord i1 u • b j1 + b.coord i2 u • b j2 := by
    conv_lhs => rw [hu2]
    simp only [map_add, map_smul, hinv0, hinv1, hinv2]
  have hphi_inv : φ (h⁻¹ u) = 1 := by rw [hhu_inv, ← hhu]; exact hphi
  have hcard : 3 ≤ (Finset.univ.filter fun i => b.coord i (h u - u) ≠ 0).card := by
    have hd : h u - u = (b.coord i1 u) • b j1 + (b.coord i2 u) • b j2
        - (b.coord i1 u) • b i1 - (b.coord i2 u) • b i2 := by
      conv_lhs => rw [hhu]
      conv_lhs => arg 2; rw [hu2]
      module
    have hc1 : b.coord i1 (h u - u) = -(b.coord i1 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj1i1, hj2i1, hi2i1]
    have hc1' : b.coord i1 (h u - u) ≠ 0 := by
      rw [hc1]; exact neg_ne_zero.mpr ha1ne
    have hc3 : b.coord j1 (h u - u) = b.coord i1 u := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj2j1, hi1j1, hi2j1]
    have hc3' : b.coord j1 (h u - u) ≠ 0 := by
      rw [hc3]; exact ha1ne
    have hc2 : b.coord i2 (h u - u) = -(b.coord i2 u) := by
      rw [hd]
      simp only [map_add, map_sub, hdRo7CSmallAux_coord_smul_basis]
      simp [hj1i2, hj2i2, hd12]
    have hc2' : b.coord i2 (h u - u) ≠ 0 := by
      rw [hc2]; exact neg_ne_zero.mpr ha2ne
    have hsub : ({i1, j1, i2} : Finset (Fin (n + 1))) ⊆
        Finset.univ.filter (fun i => b.coord i (h u - u) ≠ 0) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | rfl | rfl
      · exact ⟨Finset.mem_univ _, hc1'⟩
      · exact ⟨Finset.mem_univ _, hc3'⟩
      · exact ⟨Finset.mem_univ _, hc2'⟩
    have h3 : ({i1, j1, i2} : Finset (Fin (n + 1))).card = 3 :=
      Finset.card_eq_three.mpr ⟨i1, j1, i2, hi1j1, hd12, hj1i2, rfl⟩
    calc (3 : ℕ) = ({i1, j1, i2} : Finset (Fin (n + 1))).card := h3.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle := hT hSp 3 rfl n hn V b A hPA hStab
    r u φ hnf h hsp hphi hphi_inv
  omega

end CFSG.StandardType.HdRo7C
