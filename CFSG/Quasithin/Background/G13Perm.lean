module

public import CFSG.Quasithin.Background.G13Core

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F] {n : ℕ} {i j : Fin n}

section Swap

variable [CharP F 2]

@[expose] noncomputable def wS (F : Type*) [Field F] [CharP F 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) : Matrix.SpecialLinearGroup (Fin n) F :=
  embSL hij (wmat F)

theorem wS_smul (hij : i ≠ j) (v : Fin n → F) (k : Fin n) :
    (wS F hij • v) k = v (Equiv.swap i j k) := by
  rw [smul_eq_mulVec']
  change ((embSL hij (wmat F) : Matrix (Fin n) (Fin n) F) *ᵥ v) k = _
  rw [embSL_coe, emb_mulVec, blockMap_apply]
  by_cases hki : k = i
  · subst hki
    simp
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem wS_mul_self (hij : i ≠ j) :
    wS F hij * wS F hij = (1 : Matrix.SpecialLinearGroup (Fin n) F) := by
  unfold wS
  rw [← map_mul, wmat_mul_self, map_one]

theorem wS_smul_smul {U : Type*} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U] (hij : i ≠ j) (u : U) :
    wS F hij • wS F hij • u = u := by
  rw [← mul_smul, wS_mul_self, one_smul]

theorem wS_symm (hij : i ≠ j) : wS F hij = wS F hij.symm := by
  refine SL_ext_vec fun v => funext fun k => ?_
  rw [wS_smul, wS_smul, Equiv.swap_comm]

theorem wS_mem_Lij (hij : i ≠ j) : wS F hij ∈ Lij F i j := embSL_mem_Lij hij _

theorem wS_conj_transvection {a b k l : Fin n} (hab : a ≠ b) (hkl : k ≠ l) (c : F)
    (hkl' : Equiv.swap a b k ≠ Equiv.swap a b l) :
    wS F hab * Matrix.SpecialLinearGroup.transvection hkl c * wS F hab =
      Matrix.SpecialLinearGroup.transvection hkl' c := by
  refine SL_ext_vec fun v => funext fun m => ?_
  simp only [mul_smul]
  rw [wS_smul, T_smul_apply, T_smul_apply, wS_smul, wS_smul, Equiv.swap_apply_self]
  have : (Equiv.swap a b m = k) ↔ (m = Equiv.swap a b k) := by
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [this]

theorem wS_cocycle {o : Fin n} (hij : i ≠ j) (hoi : o ≠ i) (hoj : o ≠ j) :
    wS F hij * wS F hoi = wS F hoj * wS F hij := by
  refine SL_ext_vec fun v => funext fun k => ?_
  simp only [mul_smul]
  rw [wS_smul, wS_smul, wS_smul, wS_smul]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

@[expose] def idx0 (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

@[expose] def idx1 (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

theorem idx0_ne_idx1 (hn : 2 ≤ n) : idx0 hn ≠ idx1 hn := by
  simp [idx0, idx1, Fin.ext_iff]

theorem eq_top_of_swaps (hn : 2 ≤ n) (S : Subgroup (Matrix.SpecialLinearGroup (Fin n) F))
    (hx : ∀ c : F, Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c ∈ S)
    (hw : ∀ (i j : Fin n) (hij : i ≠ j), wS F hij ∈ S) : S = ⊤ := by
  have hconj : ∀ {a b k l k' l' : Fin n} (hab : a ≠ b) (hkl : k ≠ l)
      (hk : Equiv.swap a b k = k') (hl : Equiv.swap a b l = l') (hk'l' : k' ≠ l') (c : F),
      Matrix.SpecialLinearGroup.transvection hkl c ∈ S →
        Matrix.SpecialLinearGroup.transvection hk'l' c ∈ S := by
    intro a b k l k' l' hab hkl hk hl hk'l' c h
    subst hk hl
    rw [← wS_conj_transvection hab hkl c hk'l']
    exact S.mul_mem (S.mul_mem (hw a b hab) h) (hw a b hab)
  have ha : ∀ (j : Fin n) (hj : idx0 hn ≠ j) (c : F),
      Matrix.SpecialLinearGroup.transvection hj c ∈ S := by
    intro j hj c
    by_cases hj1 : j = idx1 hn
    · subst hj1
      exact hx c
    · have h1j : idx1 hn ≠ j := fun h => hj1 h.symm
      refine hconj h1j (idx0_ne_idx1 hn)
        (Equiv.swap_apply_of_ne_of_ne (idx0_ne_idx1 hn) hj) (Equiv.swap_apply_left _ _) hj c (hx c)
  have hall : ∀ (i j : Fin n) (hij : i ≠ j) (c : F),
      Matrix.SpecialLinearGroup.transvection hij c ∈ S := by
    intro i j hij c
    by_cases hi : i = idx0 hn
    · subst hi
      exact ha j hij c
    · have hi0 : idx0 hn ≠ i := fun h => hi h.symm
      by_cases hj : j = idx0 hn
      · subst hj
        exact hconj hi0 hi0 (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _) hij c
          (ha i hi0 c)
      · have hj0 : idx0 hn ≠ j := fun h => hj h.symm
        exact hconj hi0 hj0 (Equiv.swap_apply_left _ _)
          (Equiv.swap_apply_of_ne_of_ne hj hij.symm) hij c (ha j hj0 c)
  have hLadj : Ladj F n ≤ S := by
    refine iSup₂_le fun k hk => sup_le (fun t ht => ?_) (fun t ht => ?_)
    · have hne : (⟨k, by omega⟩ : Fin n) ≠ ⟨k + 1, hk⟩ := by simp [Fin.ext_iff]
      obtain ⟨b, rfl⟩ := (mem_Rij_iff hne).1 ht
      exact hall _ _ hne b
    · have hne : (⟨k + 1, hk⟩ : Fin n) ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]
      obtain ⟨b, rfl⟩ := (mem_Rij_iff hne).1 ht
      exact hall _ _ hne b
  rw [eq_top_iff]
  have := Ladj_eq_top (F := F) hn
  rw [← this]
  exact hLadj

end Swap

end CFSG.Quasithin.G1
