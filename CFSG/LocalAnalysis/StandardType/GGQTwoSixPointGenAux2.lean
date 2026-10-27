module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

section Gen


@[expose] def qTwoSixGen_J0123 : Finset (Fin 6) := {0, 1, 2, 3}

theorem qTwoSixGen_block0123_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    coordBlockSU K 2 1 qTwoSixGen_J0123 ≤
      Subgroup.closure (Set.range (nativeSu hK)) := by
  have hA : qTwoSixGen_J012.card = 3 := by decide
  have hB : qTwoSixGen_J123.card = 3 := by decide
  have hAB : (qTwoSixGen_J012 ∪ qTwoSixGen_J123).card = 4 := by decide
  have hunion : qTwoSixGen_J012 ∪ qTwoSixGen_J123 = qTwoSixGen_J0123 := by decide
  have hsup := coordBlockSU_sup_three hK (A := qTwoSixGen_J012) (B := qTwoSixGen_J123) hA hB hAB
  rw [hunion] at hsup
  rw [← hsup]
  exact sup_le (qTwoSixGen_block012_le hK) (qTwoSixGen_block123_le hK)

private theorem qTwoSixGen_permMatrix_map {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6)) :
    (σ.permMatrix F4c).map (f4cEmb hK) = σ.permMatrix K := by
  ext a b
  rw [Matrix.map_apply]
  by_cases h : σ a = b
  · simp [PEquiv.toMatrix_apply, h, map_one]
  · simp [PEquiv.toMatrix_apply, h, map_zero]

@[expose] def qTwoSixGen_swapIdx (i : Fin 5) : Fin 18 := ⟨2 * i.val, by omega⟩

theorem qTwoSixGen_nativeSu_swap_matrix {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (i : Fin 5) :
    (((nativeSu hK (qTwoSixGen_swapIdx i) : Su K 2 1 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) =
      (Equiv.swap i.castSucc i.succ).permMatrix K := by
  rw [show (((nativeSu hK (qTwoSixGen_swapIdx i) : Su K 2 1 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = (nativeGen (qTwoSixGen_swapIdx i)).map (f4cEmb hK) from by
    have h := coe_evalG_nativeSu hK ([(qTwoSixGen_swapIdx i, true)] : List (Fin 18 × Bool))
    simpa [evalG, evalNative] using h]
  have hF : nativeGen (qTwoSixGen_swapIdx i) =
      (Equiv.swap i.castSucc i.succ).permMatrix F4c := by
    fin_cases i <;> decide
  rw [hF, qTwoSixGen_permMatrix_map]

@[expose] def qTwoSixGen_J5 : Finset (Fin 6) := {0, 1, 2, 3, 4}

theorem qTwoSixGen_J5_card : qTwoSixGen_J5.card = 5 := by decide

private theorem qTwoSixGen_fin5_notMem (a : Fin 6) (ha : a ∉ qTwoSixGen_J0123) (h5 : a.val < 5) :
    (⟨a.val, h5⟩ : Fin 5) ∉ ({0, 1, 2, 3} : Finset (Fin 5)) := by
  have hcases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
    fin_cases a <;> simp
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by decide) ha
  · exact absurd (by decide) ha
  · exact absurd (by decide) ha
  · exact absurd (by decide) ha
  · have h4 : (⟨(4 : Fin 6).val, h5⟩ : Fin 5) = 4 := Fin.ext rfl
    rw [h4]; decide
  · exfalso; omega

theorem qTwoSixGen_blockEmb_J0123_le {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    (coordBlockSU K 2 1 ({0, 1, 2, 3} : Finset (Fin 5))).map
        (blockEmb K 2 1 6 5 0 (by norm_num)) ≤
      coordBlockSU K 2 1 qTwoSixGen_J0123 := by
  rintro y ⟨x, hx, rfl⟩
  change x ∈ coordBlockSU K 2 1 ({0, 1, 2, 3} : Finset (Fin 5)) at hx
  rw [mem_coordBlockSU_iff] at hx
  refine (mem_coordBlockSU_iff (J := qTwoSixGen_J0123)).2 ?_
  intro a b hab
  rw [coe_coe_blockEmb, blockMat_apply]
  by_cases hc : (0 ≤ a.val ∧ a.val < 0 + 5) ∧ (0 ≤ b.val ∧ b.val < 0 + 5)
  · rw [dif_pos hc]
    obtain ⟨⟨ha0, ha5⟩, hb0, hb5⟩ := hc
    have hxij : ¬ ((⟨a.val, ha5⟩ : Fin 5) ∈ ({0, 1, 2, 3} : Finset (Fin 5))) ∨
        ¬ ((⟨b.val, hb5⟩ : Fin 5) ∈ ({0, 1, 2, 3} : Finset (Fin 5))) := by
      rcases hab with h | h
      · exact Or.inl (qTwoSixGen_fin5_notMem a h ha5)
      · exact Or.inr (qTwoSixGen_fin5_notMem b h hb5)
    let M : Matrix (Fin 5) (Fin 5) K :=
      (((x : Su K 2 1 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    change M ⟨a.val - 0, ha5⟩ ⟨b.val - 0, hb5⟩ = (if a = b then 1 else 0)
    have hL : M ⟨a.val - 0, ha5⟩ ⟨b.val - 0, hb5⟩ = M ⟨a.val, ha5⟩ ⟨b.val, hb5⟩ := by
      rw [show (⟨a.val - 0, ha5⟩ : Fin 5) = ⟨a.val, ha5⟩ from Fin.ext (by simp),
        show (⟨b.val - 0, hb5⟩ : Fin 5) = ⟨b.val, hb5⟩ from Fin.ext (by simp)]
    have hxval' : M ⟨a.val, ha5⟩ ⟨b.val, hb5⟩ =
        (if (⟨a.val, ha5⟩ : Fin 5) = ⟨b.val, hb5⟩ then 1 else 0) :=
      hx ⟨a.val, ha5⟩ ⟨b.val, hb5⟩ hxij
    rw [hL, hxval']
    by_cases h : (⟨a.val, ha5⟩ : Fin 5) = ⟨b.val, hb5⟩
    · have h2 : a = b := Fin.ext (by simpa using congrArg Fin.val h)
      simp [h, h2]
    · have h2 : a ≠ b := fun h2 => h (Fin.ext (by simpa using congrArg Fin.val h2))
      simp [h, h2]
  · rw [dif_neg hc]
    exact Matrix.one_apply

theorem qTwoSixGen_blockEmb_injective {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    Function.Injective (blockEmb K 2 1 6 5 0 (by norm_num)) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  have h' : blockMat 6 0 ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blockMat 6 0 ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    have := congrArg (fun z : Su K 2 1 6 => (((z : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K)) h
    simpa [coe_coe_blockEmb] using this
  exact blockMat_injective (by norm_num) h'

private theorem qTwoSixGen_permMatrix_apply {K : Type} [Field K] {n : Type*} [DecidableEq n] [Fintype n]
    (σ : Equiv.Perm n) (a b : n) : (σ.permMatrix K) a b = if σ a = b then 1 else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply,
    Matrix.one_apply, id_eq]

private theorem qTwoSixGen_blockMat_perm {K : Type} [Field K] [Finite K] [CharP K 2] (i j : Fin 5) (hij : i.val + 1 = j.val) :
    blockMat 6 0 ((Equiv.swap i j).permMatrix K) =
      (Equiv.swap i.castSucc i.succ).permMatrix K := by
  ext a b
  rw [blockMat_apply]
  by_cases hwin : (0 ≤ a.val ∧ a.val < 0 + 5) ∧ (0 ≤ b.val ∧ b.val < 0 + 5)
  · rw [dif_pos hwin]
    rw [qTwoSixGen_permMatrix_apply (K := K) (n := Fin 5) (σ := Equiv.swap i j)]
    rw [qTwoSixGen_permMatrix_apply (K := K) (n := Fin 6) (σ := Equiv.swap i.castSucc i.succ)]
    congr 1
    rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Nat.sub_zero] <;> omega
  · rw [dif_neg hwin, Matrix.one_apply]
    rw [qTwoSixGen_permMatrix_apply (K := K) (n := Fin 6) (σ := Equiv.swap i.castSucc i.succ)]
    congr 1
    rw [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Nat.sub_zero] <;> omega

theorem qTwoSixGen_blockEmb_perm {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (i j : Fin 5) (hij : i.val + 1 = j.val)
    {g : Su K 2 1 5}
    (hg : (((g : Su K 2 1 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (Equiv.swap i j).permMatrix K) :
    blockEmb K 2 1 6 5 0 (by norm_num) g = nativeSu hK (qTwoSixGen_swapIdx i) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_coe_blockEmb, hg, qTwoSixGen_nativeSu_swap_matrix hK i, qTwoSixGen_blockMat_perm i j hij]

theorem qTwoSixGen_chart5_lower {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    13685760 ≤ Nat.card (Subgroup.closure (nativeSu hK '' {i | i ∈ subsetOf 18 chart5})) := by
  set H5 : Subgroup (Su K 2 1 6) :=
    Subgroup.closure (nativeSu hK '' {i | i ∈ subsetOf 18 chart5}) with hH5
  have hmem : ∀ i : Fin 18, i ∈ subsetOf 18 chart5 → nativeSu hK i ∈ H5 :=
    fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩
  have h012 : coordBlockSU K 2 1 qTwoSixGen_J012 ≤ H5 :=
    qTwoSixGen_block_le_of_mem hK (by decide) 10 11 qTwoSixGen_nodup012
      (qTwoSixGen_nativeSu_mem hK 10 (qTwoSixGen_support012 10 (Or.inl rfl)))
      (qTwoSixGen_nativeSu_mem hK 11 (qTwoSixGen_support012 11 (Or.inr rfl)))
      (hmem 10 (by decide)) (hmem 11 (by decide))
  have h123 : coordBlockSU K 2 1 qTwoSixGen_J123 ≤ H5 :=
    qTwoSixGen_block_le_of_mem hK (by decide) 12 13 qTwoSixGen_nodup123
      (qTwoSixGen_nativeSu_mem hK 12 (qTwoSixGen_support123 12 (Or.inl rfl)))
      (qTwoSixGen_nativeSu_mem hK 13 (qTwoSixGen_support123 13 (Or.inr rfl)))
      (hmem 12 (by decide)) (hmem 13 (by decide))
  have h234 : coordBlockSU K 2 1 qTwoSixGen_J234 ≤ H5 :=
    qTwoSixGen_block_le_of_mem hK (by decide) 14 15 qTwoSixGen_nodup234
      (qTwoSixGen_nativeSu_mem hK 14 (qTwoSixGen_support234 14 (Or.inl rfl)))
      (qTwoSixGen_nativeSu_mem hK 15 (qTwoSixGen_support234 15 (Or.inr rfl)))
      (hmem 14 (by decide)) (hmem 15 (by decide))
  have h0123 : coordBlockSU K 2 1 qTwoSixGen_J0123 ≤ H5 := by
    have hA : qTwoSixGen_J012.card = 3 := by decide
    have hB : qTwoSixGen_J123.card = 3 := by decide
    have hAB : (qTwoSixGen_J012 ∪ qTwoSixGen_J123).card = 4 := by decide
    have hunion : qTwoSixGen_J012 ∪ qTwoSixGen_J123 = qTwoSixGen_J0123 := by decide
    have hsup := coordBlockSU_sup_three hK (A := qTwoSixGen_J012) (B := qTwoSixGen_J123) hA hB hAB
    rw [hunion] at hsup
    rw [← hsup]
    exact sup_le h012 h123
  set φ : Su K 2 1 5 →* Su K 2 1 6 := blockEmb K 2 1 6 5 0 (by norm_num) with hφ
  have hφinj : Function.Injective φ := qTwoSixGen_blockEmb_injective hK
  set H5' : Subgroup (Su K 2 1 5) := H5.comap φ with hH5'
  have htop : H5' = ⊤ := by
    refine eq_top_of_fourBlock_of_swaps hK (N := 5) (by norm_num) H5' ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap]
      exact h0123 (qTwoSixGen_blockEmb_J0123_le hK ⟨x, hx, rfl⟩)
    · intro i j hij g hg
      rw [Subgroup.mem_comap]
      rw [qTwoSixGen_blockEmb_perm hK i j hij hg]
      refine hmem (qTwoSixGen_swapIdx i) ?_
      have hi3 : i.val ≤ 3 := by have := j.isLt; omega
      fin_cases i <;> simp_all <;> decide
  have hmap_top : (⊤ : Subgroup (Su K 2 1 5)).map φ ≤ H5 := by
    rw [← htop]
    rintro y ⟨x, hx, rfl⟩
    exact hx
  haveI : Finite ↥H5 := Subtype.finite
  have hcard : Nat.card (Su K 2 1 5) = 13685760 := CFSG.StandardType.QTwo.card_Su_five hK
  have hinj : Function.Injective
      (fun x : (⊤ : Subgroup (Su K 2 1 5)).map φ => (⟨x, hmap_top x.2⟩ : H5)) := by
    intro a b h
    exact Subtype.val_injective (by simpa using congrArg Subtype.val h)
  calc 13685760 = Nat.card (Su K 2 1 5) := hcard.symm
    _ = Nat.card ((⊤ : Subgroup (Su K 2 1 5)).map φ) := by
        rw [Subgroup.map_top]
        exact Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ≤ Nat.card H5 := Nat.card_le_card_of_injective _ hinj

end Gen

end CFSG.StandardType.QTwo.SixPoint

end
