module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSStab
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem bsgen_permMatrix_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (σ.permMatrix K) a b = if σ a = b then (1 : K) else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private theorem bsgen_permMatrix_swap_mem_coordBlockSU {N : ℕ} {i j : Fin N}
    {J : Finset (Fin N)} (hi : i ∈ J) (hj : j ∈ J) {g : Su K 2 1 N}
    (hg : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = (Equiv.swap i j).permMatrix K) :
    g ∈ coordBlockSU K 2 1 J := by
  rw [mem_coordBlockSU_iff]
  intro a b hab
  rw [hg, bsgen_permMatrix_apply]
  rcases hab with ha | hb
  · have hai : a ≠ i := fun h => ha (h ▸ hi)
    have haj : a ≠ j := fun h => ha (h ▸ hj)
    rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  · have hbi : b ≠ i := fun h => hb (h ▸ hi)
    have hbj : b ≠ j := fun h => hb (h ▸ hj)
    by_cases hai : a = i
    · subst hai
      rw [Equiv.swap_apply_left]
      rw [if_neg (fun h => hbj h.symm)]
      rw [if_neg (fun h => hbi h.symm)]
    · by_cases haj : a = j
      · subst haj
        rw [Equiv.swap_apply_right]
        rw [if_neg (fun h => hbi h.symm)]
        rw [if_neg (fun h => hbj h.symm)]
      · rw [Equiv.swap_apply_of_ne_of_ne hai haj]

private theorem bsgen_window_eq {k s : ℕ} (hs : s + 3 ≤ k) :
    (Finset.univ.map (SixPoint.qTwoSixWinEmb hs) : Finset (Fin k)) =
      ({⟨s, by omega⟩, ⟨s + 1, by omega⟩, ⟨s + 2, by omega⟩} : Finset (Fin k)) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff]
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (SixPoint.qTwoSixWinEmb hs a).val = a.val + s := SixPoint.qTwoSixWinEmb_val hs a
    have ha'' : a.val + s = ↑x := by rwa [ha'] at ha
    have ha3 : a.val < 3 := a.isLt
    omega
  · rintro (h | h | h)
    · exact ⟨⟨0, by omega⟩, by
        have ha' : (SixPoint.qTwoSixWinEmb hs ⟨0, by omega⟩).val = 0 + s :=
          SixPoint.qTwoSixWinEmb_val hs ⟨0, by omega⟩
        omega⟩
    · exact ⟨⟨1, by omega⟩, by
        have ha' : (SixPoint.qTwoSixWinEmb hs ⟨1, by omega⟩).val = 1 + s :=
          SixPoint.qTwoSixWinEmb_val hs ⟨1, by omega⟩
        omega⟩
    · exact ⟨⟨2, by omega⟩, by
        have ha' : (SixPoint.qTwoSixWinEmb hs ⟨2, by omega⟩).val = 2 + s :=
          SixPoint.qTwoSixWinEmb_val hs ⟨2, by omega⟩
        omega⟩

private theorem bsgen_swapAt_four_matrix :
    (((swapAt K 4 2 (by norm_num) : Su K 2 1 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) =
      (Equiv.swap (⟨2, by norm_num⟩ : Fin 4) ⟨3, by norm_num⟩).permMatrix K := by
  apply Matrix.ext_of_mulVec_single
  intro l
  rw [← CFSG.ClassicalGroups.Unitary.smul_def]
  rw [Matrix.permMatrix_mulVec]
  fin_cases l
  · rw [swapAt_smul_single_of_ne (K := K) (m := 4) (a := 2) (by norm_num)
      (by norm_num) (by norm_num)]
    funext b
    fin_cases b <;> simp [Equiv.swap_apply_def]
  · rw [swapAt_smul_single_of_ne (K := K) (m := 4) (a := 2) (by norm_num)
      (by norm_num) (by norm_num)]
    funext b
    fin_cases b <;> simp [Equiv.swap_apply_def]
  · rw [swapAt_smul_single_left]
    funext b
    fin_cases b <;> simp [Equiv.swap_apply_def]
  · rw [swapAt_smul_single_right]
    funext b
    fin_cases b <;> simp [Equiv.swap_apply_def]

private theorem bsgen_conj_mem_coordBlockSU {I J : Finset (Fin 4)} {σ : Equiv.Perm (Fin 4)}
    (hσ : σ = σ⁻¹) (hJI : ∀ a, a ∉ J → σ a ∉ I) {P g : Su K 2 1 4}
    (hP : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = σ.permMatrix K)
    (hg : g ∈ coordBlockSU K 2 1 I) :
    P * g * P ∈ coordBlockSU K 2 1 J := by
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro a b hab
  set G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hmul : (((P * g * P : Su K 2 1 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      σ.permMatrix K * G * σ.permMatrix K := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hP]
  rw [hmul]
  have hmul_left : σ.permMatrix K * G = G.submatrix σ id := by
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rw [hmul_left]
  have hmul_right : ∀ M : Matrix (Fin 4) (Fin 4) K,
      M * σ.permMatrix K = M.submatrix id σ.symm := by
    intro M
    rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rw [hmul_right]
  have hsymm : σ.symm = σ := hσ.symm
  rw [hsymm]
  simp only [Matrix.submatrix_apply, id_eq]
  have hmem : σ a ∉ I ∨ σ b ∉ I := by
    rcases hab with ha | hb
    · exact Or.inl (hJI a ha)
    · exact Or.inr (hJI b hb)
  rw [hg (σ a) (σ b) hmem]
  simp only [Equiv.apply_eq_iff_eq]

private theorem bsgen_sup_swapAt (hK : Nat.card K = 4) :
    (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔
      Subgroup.zpowers (swapAt K 4 2 (by norm_num)) = ⊤ := by
  set P : Su K 2 1 4 := swapAt K 4 2 (by norm_num) with hPdef
  set I : Finset (Fin 4) := {⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩} with hI
  set J : Finset (Fin 4) := {⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨3, by norm_num⟩} with hJ
  have hP : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (Equiv.swap (⟨2, by norm_num⟩ : Fin 4) ⟨3, by norm_num⟩).permMatrix K :=
    bsgen_swapAt_four_matrix
  have hPP : P * P = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hP, ← Matrix.permMatrix_mul, Equiv.swap_mul_self,
      Matrix.permMatrix_one]
    simp
  have hbot : (blockEmb K 2 1 4 3 0 (by norm_num)).range =
      coordBlockSU K 2 1 I := by
    rw [SixPoint.qTwoSixWin_range (by norm_num), bsgen_window_eq (by norm_num)]
  have hstepJ : ∀ {g : Su K 2 1 4}, g ∈ coordBlockSU K 2 1 J →
      P * g * P ∈ coordBlockSU K 2 1 I := by
    intro g hg
    refine bsgen_conj_mem_coordBlockSU (K := K) (I := J) (J := I)
      (σ := Equiv.swap (⟨2, by norm_num⟩ : Fin 4) ⟨3, by norm_num⟩) ?_ ?_ hP hg
    · rw [Equiv.swap_inv]
    · intro a ha
      fin_cases a <;> simp_all [I, J]
  have hbot_le : coordBlockSU K 2 1 I ≤
      (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔ Subgroup.zpowers P :=
    hbot.symm.le.trans le_sup_left
  have hPmem : P ∈ (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔ Subgroup.zpowers P :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers P)
  have hJ_le : coordBlockSU K 2 1 J ≤
      (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔ Subgroup.zpowers P := by
    intro y hy
    have hconj := hstepJ hy
    have hconj' : P * (P * y * P) * P ∈
        (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔ Subgroup.zpowers P :=
      mul_mem (mul_mem hPmem (hbot_le hconj)) hPmem
    have hy' : P * (P * y * P) * P = y := by
      calc P * (P * y * P) * P = (P * P) * y * (P * P) := by group
        _ = y := by rw [hPP, one_mul, mul_one]
    rwa [hy'] at hconj'
  have htop : coordBlockSU K 2 1 I ⊔ coordBlockSU K 2 1 J = ⊤ := by
    rw [coordBlockSU_sup_three hK (A := I) (B := J) (by decide) (by decide) (by decide)]
    rw [show I ∪ J = (Finset.univ : Finset (Fin 4)) by ext x; fin_cases x <;> simp [I, J]]
    exact SixPoint.qTwoSixWin_coordBlockSU_univ 4
  rw [eq_top_iff, ← htop]
  exact sup_le hbot_le hJ_le

private theorem bsgen_iSup_three :
    ⨆ (i : ℕ) (h : i + 3 ≤ 3), (blockEmb K 2 1 3 3 i h).range = ⊤ := by
  have htop : (blockEmb K 2 1 3 3 0 (by norm_num)).range = ⊤ := by
    rw [SixPoint.qTwoSixWin_range (by norm_num), bsgen_window_eq (by norm_num)]
    rw [show ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩} : Finset (Fin 3)) =
      Finset.univ by decide]
    exact SixPoint.qTwoSixWin_coordBlockSU_univ 3
  rw [eq_top_iff]
  intro g _
  exact Subgroup.mem_iSup_of_mem 0
    (Subgroup.mem_iSup_of_mem (by norm_num) (by rw [htop]; exact Subgroup.mem_top g))

private theorem bsgen_fourBlock_le (hK : Nat.card K = 4) {k : ℕ} (h4 : 4 ≤ k) :
    coordBlockSU K 2 1
        ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin k)) ≤
      ⨆ (i : ℕ) (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range := by
  have h0 : (blockEmb K 2 1 k 3 0 (by omega)).range =
      coordBlockSU K 2 1
        ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin k)) := by
    rw [SixPoint.qTwoSixWin_range (by omega), bsgen_window_eq (by omega)]
  have h1 : (blockEmb K 2 1 k 3 1 (by omega)).range =
      coordBlockSU K 2 1
        ({⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin k)) := by
    rw [SixPoint.qTwoSixWin_range (by omega), bsgen_window_eq (by omega)]
  have hk0 : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hk3 : 3 < k := by omega
  have hsup : coordBlockSU K 2 1
        ({⟨0, hk0⟩, ⟨1, hk1⟩, ⟨2, hk2⟩} : Finset (Fin k)) ⊔
      coordBlockSU K 2 1
        ({⟨1, hk1⟩, ⟨2, hk2⟩, ⟨3, hk3⟩} : Finset (Fin k)) =
      coordBlockSU K 2 1
        ({⟨0, hk0⟩, ⟨1, hk1⟩, ⟨2, hk2⟩, ⟨3, hk3⟩} : Finset (Fin k)) := by
    have h := coordBlockSU_sup_three (K := K) hK
      (A := ({⟨0, hk0⟩, ⟨1, hk1⟩, ⟨2, hk2⟩} : Finset (Fin k)))
      (B := ({⟨1, hk1⟩, ⟨2, hk2⟩, ⟨3, hk3⟩} : Finset (Fin k)))
      (by simp [Finset.card_insert_of_notMem]) (by simp [Finset.card_insert_of_notMem])
      (by simp [Finset.card_insert_of_notMem])
    rwa [show ({⟨0, hk0⟩, ⟨1, hk1⟩, ⟨2, hk2⟩} : Finset (Fin k)) ∪
        {⟨1, hk1⟩, ⟨2, hk2⟩, ⟨3, hk3⟩} =
        ({⟨0, hk0⟩, ⟨1, hk1⟩, ⟨2, hk2⟩, ⟨3, hk3⟩} : Finset (Fin k)) by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Fin.ext_iff]; omega] at h
  have hAle : coordBlockSU K 2 1
        ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin k)) ≤
      ⨆ (i : ℕ) (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range := by
    intro x hx
    exact Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_iSup_of_mem (by omega)
      (by rw [h0]; exact hx))
  have hBle : coordBlockSU K 2 1
        ({⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin k)) ≤
      ⨆ (i : ℕ) (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range := by
    intro x hx
    exact Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (by omega)
      (by rw [h1]; exact hx))
  rw [← hsup]
  exact sup_le hAle hBle

private theorem bsgen_swap_mem {k : ℕ} (hk : 3 ≤ k) (i j : Fin k) (hij : i.val + 1 = j.val)
    (g : Su K 2 1 k)
    (hg : (((g : Su K 2 1 k) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      (Equiv.swap i j).permMatrix K) :
    g ∈ ⨆ (i : ℕ) (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range := by
  set s : ℕ := min i.val (k - 3) with hs
  have hs3 : s + 3 ≤ k := by omega
  have hwin : (Finset.univ.map (SixPoint.qTwoSixWinEmb hs3) : Finset (Fin k)) =
      ({⟨s, by omega⟩, ⟨s + 1, by omega⟩, ⟨s + 2, by omega⟩} :
        Finset (Fin k)) :=
    bsgen_window_eq hs3
  have hi_mem : i ∈ (Finset.univ.map (SixPoint.qTwoSixWinEmb hs3) :
      Finset (Fin k)) := by
    rw [hwin]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  have hj_mem : j ∈ (Finset.univ.map (SixPoint.qTwoSixWinEmb hs3) :
      Finset (Fin k)) := by
    rw [hwin]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  have hmem : g ∈ coordBlockSU K 2 1 ({i, j} : Finset (Fin k)) :=
    bsgen_permMatrix_swap_mem_coordBlockSU (by simp) (by simp) hg
  have hsub : ({i, j} : Finset (Fin k)) ⊆
      (Finset.univ.map (SixPoint.qTwoSixWinEmb hs3) : Finset (Fin k)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi_mem
    · exact hj_mem
  have hmem' : g ∈ coordBlockSU K 2 1
      (Finset.univ.map (SixPoint.qTwoSixWinEmb hs3) : Finset (Fin k)) :=
    qTwoS34_coordBlockSU_mono hsub hmem
  rw [← SixPoint.qTwoSixWin_range hs3] at hmem'
  exact Subgroup.mem_iSup_of_mem s (Subgroup.mem_iSup_of_mem hs3 hmem')

theorem iSup_range_blockEmb_three (hK : Nat.card K = 4) {k : ℕ} (hk : 3 ≤ k) :
    ⨆ (i : ℕ) (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range = ⊤ := by
  rcases eq_or_lt_of_le hk with rfl | hk4
  · exact bsgen_iSup_three
  · exact eq_top_of_fourBlock_of_swaps hK hk4 _ (bsgen_fourBlock_le hK hk4)
      (fun i j hij g hg => bsgen_swap_mem hk i j hij g hg)

theorem range_blockEmb_three_sup_zpowers_swapAt (hK : Nat.card K = 4) :
    (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔
      Subgroup.zpowers (swapAt K 4 2 (by norm_num)) = ⊤ :=
  bsgen_sup_swapAt hK

end CFSG.StandardType.QTwo

end
