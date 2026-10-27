module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2s08pi_A_eq_three_iff {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    CoxeterMatrix.A n a b = 3 ↔ (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b := by
  have h : CoxeterMatrix.A n a b =
      (if (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b then 3 else 2) := by
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    rw [if_neg hab]
  rw [h]
  by_cases hc : (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]; simp [hc]

private theorem ggQ2s08pi_A_eq_two_iff {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    CoxeterMatrix.A n a b = 2 ↔ ¬ ((b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b) := by
  have h : CoxeterMatrix.A n a b =
      (if (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b then 3 else 2) := by
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    rw [if_neg hab]
  rw [h]
  by_cases hc : (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]; simp [hc]

private theorem ggQ2s08pi_A_ne_four {n : ℕ} (a b : Fin n) : CoxeterMatrix.A n a b ≠ 4 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2s08pi_A_ne_six {n : ℕ} (a b : Fin n) : CoxeterMatrix.A n a b ≠ 6 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2s08pi_find3 {n : ℕ} (hn : 4 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (hadj : (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b) :
    (∃ k : Fin n, k ≠ a ∧ k ≠ b ∧
      CoxeterMatrix.A n k a = 3 ∧ CoxeterMatrix.A n k b = 2) ∨
    (∃ k : Fin n, k ≠ a ∧ k ≠ b ∧
      CoxeterMatrix.A n k a = 2 ∧ CoxeterMatrix.A n k b = 3) := by
  rcases hadj with hba | hab'
  ·
    by_cases hb0 : (b : ℕ) = 0
    ·
      let k : Fin n := ⟨2, by omega⟩
      have hka : k ≠ a := by
        intro h
        have hv : (2 : ℕ) = (a : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hkb : k ≠ b := by
        intro h
        have hv : (2 : ℕ) = (b : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hAa : CoxeterMatrix.A n k a = 3 := by
        rw [ggQ2s08pi_A_eq_three_iff k a hka]
        left
        simp only [k, Fin.val_mk]
        omega
      have hAb : CoxeterMatrix.A n k b = 2 := by
        rw [ggQ2s08pi_A_eq_two_iff k b hkb]
        intro h
        rcases h with h | h <;> (simp only [k, Fin.val_mk] at h; omega)
      exact Or.inl ⟨k, hka, hkb, hAa, hAb⟩
    ·
      let k : Fin n := ⟨(b : ℕ) - 1, by omega⟩
      have hka : k ≠ a := by
        intro h
        have hv : ((b : ℕ) - 1) = (a : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hkb : k ≠ b := by
        intro h
        have hv : ((b : ℕ) - 1) = (b : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hAa : CoxeterMatrix.A n k a = 2 := by
        rw [ggQ2s08pi_A_eq_two_iff k a hka]
        intro h
        rcases h with h | h <;> (simp only [k, Fin.val_mk] at h; omega)
      have hAb : CoxeterMatrix.A n k b = 3 := by
        rw [ggQ2s08pi_A_eq_three_iff k b hkb]
        right
        simp only [k, Fin.val_mk]
        omega
      exact Or.inr ⟨k, hka, hkb, hAa, hAb⟩
  ·
    by_cases ha0 : (a : ℕ) = 0
    ·
      let k : Fin n := ⟨2, by omega⟩
      have hka : k ≠ a := by
        intro h
        have hv : (2 : ℕ) = (a : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hkb : k ≠ b := by
        intro h
        have hv : (2 : ℕ) = (b : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hAa : CoxeterMatrix.A n k a = 2 := by
        rw [ggQ2s08pi_A_eq_two_iff k a hka]
        intro h
        rcases h with h | h <;> (simp only [k, Fin.val_mk] at h; omega)
      have hAb : CoxeterMatrix.A n k b = 3 := by
        rw [ggQ2s08pi_A_eq_three_iff k b hkb]
        left
        simp only [k, Fin.val_mk]
        omega
      exact Or.inr ⟨k, hka, hkb, hAa, hAb⟩
    ·
      let k : Fin n := ⟨(a : ℕ) - 1, by omega⟩
      have hka : k ≠ a := by
        intro h
        have hv : ((a : ℕ) - 1) = (a : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hkb : k ≠ b := by
        intro h
        have hv : ((a : ℕ) - 1) = (b : ℕ) := by
          simpa only [k, Fin.val_mk] using congrArg Fin.val h
        omega
      have hAa : CoxeterMatrix.A n k a = 3 := by
        rw [ggQ2s08pi_A_eq_three_iff k a hka]
        right
        simp only [k, Fin.val_mk]
        omega
      have hAb : CoxeterMatrix.A n k b = 2 := by
        rw [ggQ2s08pi_A_eq_two_iff k b hkb]
        intro h
        rcases h with h | h <;> (simp only [k, Fin.val_mk] at h; omega)
      exact Or.inl ⟨k, hka, hkb, hAa, hAb⟩

private theorem ggQ2s08pi_cartan_of_coxeter_two {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {i j : M.Λ} (hij : i ≠ j) (h : M.coxeter i j = 2) :
    M.cartan i j = 0 := by
  rcases M.isCartan.2 i j hij with ⟨-, h1, -⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact h1
  · rw [h] at h3; norm_num at h3
  · rw [h] at h4; norm_num at h4
  · rw [h] at h6; norm_num at h6

private theorem ggQ2s08pi_cartan_of_coxeter_three {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {i j : M.Λ} (hij : i ≠ j) (h : M.coxeter i j = 3) :
    M.cartan i j = -1 := by
  rcases M.isCartan.2 i j hij with ⟨h2, -, -⟩ | ⟨-, h1, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · rw [h] at h2; norm_num at h2
  · exact h1
  · rw [h] at h4; norm_num at h4
  · rw [h] at h6; norm_num at h6

theorem ggQ2s08_big_pairIndep {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hMW : GGQ2LabelWeyl lab M.coxeter)
    (htag : lab.tag = .twA) (h4 : 4 ≤ lab.rank) (i j : M.Λ) (hij : i ≠ j) :
    LinearIndependent (ZMod 3) ![M.coroot i, M.coroot j] := by
  obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa [GGQ2LabelWeyl, htag] using hMW
  have hab : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
  have hcox : ∀ u v : M.Λ, M.coxeter u v =
      CoxeterMatrix.A lab.rank (e.symm u) (e.symm v) := by
    intro u v
    rw [he, CoxeterMatrix.reindex_apply]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hpair_ii : M.root i (M.coroot i) = (2 : ZMod 3) := by
    rw [M.pairing i i, M.isCartan.1 i]; norm_num
  have hpair_jj : M.root j (M.coroot j) = (2 : ZMod 3) := by
    rw [M.pairing j j, M.isCartan.1 j]; norm_num
  have h1 : (2 : ZMod 3) * s + (M.cartan i j : ZMod 3) * t = 0 := by
    have h := congrArg (fun v => M.root i v) hst
    simp only [map_add, map_smul, map_zero] at h
    rw [hpair_ii, M.pairing i j] at h
    simp only [smul_eq_mul] at h
    rw [mul_comm s 2, mul_comm t (M.cartan i j : ZMod 3)] at h
    exact h
  have h2 : (M.cartan j i : ZMod 3) * s + (2 : ZMod 3) * t = 0 := by
    have h := congrArg (fun v => M.root j v) hst
    simp only [map_add, map_smul, map_zero] at h
    rw [hpair_jj, M.pairing j i] at h
    simp only [smul_eq_mul] at h
    rw [mul_comm s (M.cartan j i : ZMod 3), mul_comm t 2] at h
    exact h
  rcases M.isCartan.2 i j hij with ⟨hm2, hCij2, hCji2⟩ | ⟨hm3, hCij3, hCji3⟩ |
    ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
  ·
    have hcij : (M.cartan i j : ZMod 3) = 0 := by rw [hCij2]; norm_num
    have hcji : (M.cartan j i : ZMod 3) = 0 := by rw [hCji2]; norm_num
    constructor
    · have h := h1
      rw [hcij, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (by decide)
    · have h := h2
      rw [hcji, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left (by decide)
  ·
    have hcij : (M.cartan i j : ZMod 3) = -1 := by rw [hCij3]; decide
    have hts : t = -s := by
      have h := h1
      rw [hcij] at h
      rw [show (-1 : ZMod 3) = 2 by decide, ← mul_add] at h
      have hst0 : s + t = 0 := (mul_eq_zero.mp h).resolve_left (by decide)
      exact eq_neg_of_add_eq_zero_right hst0
    have hs0 : s = 0 := by
      by_contra hs
      have hcd : M.coroot i = M.coroot j := by
        have hz : s • (M.coroot i - M.coroot j) = 0 := by
          have h := hst
          rw [hts] at h
          rw [smul_sub, sub_eq_add_neg, ← neg_smul]
          exact h
        exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hs)
      have hadj : (e.symm j : ℕ) + 1 = e.symm i ∨ (e.symm i : ℕ) + 1 = e.symm j := by
        have hA : CoxeterMatrix.A lab.rank (e.symm i) (e.symm j) = 3 := by
          rw [← hcox i j, hm3]
        exact (ggQ2s08pi_A_eq_three_iff (e.symm i) (e.symm j) hab).mp hA
      rcases ggQ2s08pi_find3 h4 (e.symm i) (e.symm j) hab hadj with
        ⟨k, hka, hkb, hA1, hA2⟩ | ⟨k, hka, hkb, hA1, hA2⟩
      · have hki : e k ≠ i := fun h =>
          hka (e.injective (h.trans (Equiv.apply_symm_apply e i).symm))
        have hkj : e k ≠ j := fun h =>
          hkb (e.injective (h.trans (Equiv.apply_symm_apply e j).symm))
        have h3 : M.coxeter (e k) i = 3 := by
          rw [hcox (e k) i]; simpa using hA1
        have h2' : M.coxeter (e k) j = 2 := by
          rw [hcox (e k) j]; simpa using hA2
        have hc1 := ggQ2s08pi_cartan_of_coxeter_three M hki h3
        have hc2 := ggQ2s08pi_cartan_of_coxeter_two M hkj h2'
        have hk := congrArg (fun v => M.root (e k) v) hcd
        rw [M.pairing (e k) i, M.pairing (e k) j, hc1, hc2] at hk
        exact absurd hk (by decide)
      · have hki : e k ≠ i := fun h =>
          hka (e.injective (h.trans (Equiv.apply_symm_apply e i).symm))
        have hkj : e k ≠ j := fun h =>
          hkb (e.injective (h.trans (Equiv.apply_symm_apply e j).symm))
        have h2' : M.coxeter (e k) i = 2 := by
          rw [hcox (e k) i]; simpa using hA1
        have h3 : M.coxeter (e k) j = 3 := by
          rw [hcox (e k) j]; simpa using hA2
        have hc1 := ggQ2s08pi_cartan_of_coxeter_two M hki h2'
        have hc2 := ggQ2s08pi_cartan_of_coxeter_three M hkj h3
        have hk := congrArg (fun v => M.root (e k) v) hcd
        rw [M.pairing (e k) i, M.pairing (e k) j, hc1, hc2] at hk
        exact absurd hk (by decide)
    refine ⟨hs0, ?_⟩
    have hcji : (M.cartan j i : ZMod 3) = -1 := by rw [hCji3]; decide
    have ht2 : (2 : ZMod 3) * t = 0 := by
      have h := h2
      rw [hcji, hs0, mul_zero, zero_add] at h
      exact h
    exact (mul_eq_zero.mp ht2).resolve_left (by decide)
  · exfalso
    have h := hcox i j
    rw [hm4] at h
    exact ggQ2s08pi_A_ne_four _ _ h.symm
  · exfalso
    have h := hcox i j
    rw [hm6] at h
    exact ggQ2s08pi_A_ne_six _ _ h.symm

end CFSG.StandardType

end
