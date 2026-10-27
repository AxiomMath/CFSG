module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def ggBCCoroot (n : ℕ) (ε : ZMod 3) (i : Fin n) : GGBCV n := fun j =>
  if (i : ℕ) + 1 < n then (if (j : ℕ) = i then 1 else if (j : ℕ) = i + 1 then -1 else 0)
  else (if (j : ℕ) + 1 = n then ε else 0)

@[expose] def ggBCRootFun (n : ℕ) (ε : ZMod 3) (i : Fin n) : GGBCV n := fun j =>
  if (i : ℕ) + 1 < n then (if (j : ℕ) = i then 1 else if (j : ℕ) = i + 1 then -1 else 0)
  else (if (j : ℕ) + 1 = n then 2 / ε else 0)

private lemma ggQ2x_coroot_eq_single (n : ℕ) (ε : ZMod 3) (i : Fin n) (hi : (i:ℕ)+1 < n) :
    ggBCCoroot n ε i =
      ((Pi.single i (1:ZMod 3) : Fin n → ZMod 3) -
        (Pi.single ⟨(i:ℕ)+1, hi⟩ (1:ZMod 3) : Fin n → ZMod 3)) := by
  funext j
  by_cases h1 : j = i
  · subst h1
    have hne : j ≠ ⟨(j:ℕ)+1, hi⟩ := by
      intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
    simp [ggBCCoroot, hi, Pi.single_apply, hne]
    norm_num
  · by_cases h2 : j = ⟨(i:ℕ)+1, hi⟩
    · subst h2
      have hne' : i ≠ ⟨(i:ℕ)+1, hi⟩ := by
        intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
      simp [ggBCCoroot, hi, Pi.single_apply, h1, hne']
      rfl
    · have hj1 : (j:ℕ) ≠ i := fun h => h1 (Fin.ext h)
      have hj2 : (j:ℕ) ≠ (i:ℕ)+1 := fun h => h2 (Fin.ext h)
      simp [ggBCCoroot, hi, Pi.single_apply, h1, h2, hj1, hj2]

private lemma ggQ2x_rootFun_eq_single (n : ℕ) (ε : ZMod 3) (i : Fin n) (hi : (i:ℕ)+1 < n) :
    ggBCRootFun n ε i =
      ((Pi.single i (1:ZMod 3) : Fin n → ZMod 3) -
        (Pi.single ⟨(i:ℕ)+1, hi⟩ (1:ZMod 3) : Fin n → ZMod 3)) := by
  funext j
  by_cases h1 : j = i
  · subst h1
    have hne : j ≠ ⟨(j:ℕ)+1, hi⟩ := by
      intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
    simp [ggBCRootFun, hi, Pi.single_apply, hne]
    norm_num
  · by_cases h2 : j = ⟨(i:ℕ)+1, hi⟩
    · subst h2
      have hne' : i ≠ ⟨(i:ℕ)+1, hi⟩ := by
        intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
      simp [ggBCRootFun, hi, Pi.single_apply, h1, hne']
      rfl
    · have hj1 : (j:ℕ) ≠ i := fun h => h1 (Fin.ext h)
      have hj2 : (j:ℕ) ≠ (i:ℕ)+1 := fun h => h2 (Fin.ext h)
      simp [ggBCRootFun, hi, Pi.single_apply, h1, h2, hj1, hj2]

private lemma ggQ2x_coroot_last (n : ℕ) (ε : ZMod 3) (hn : 0 < n) :
    ggBCCoroot n ε ⟨n-1, by omega⟩ =
      (Pi.single ⟨n-1, by omega⟩ ε : Fin n → ZMod 3) := by
  funext j
  have hnot : ¬ (n - 1) + 1 < n := by omega
  have hiff : ((j:ℕ)+1 = n) ↔ j = (⟨n-1, by omega⟩ : Fin n) := by
    constructor
    · intro h; apply Fin.ext; simp only [Fin.val_mk]; omega
    · intro h; subst h; simp only [Fin.val_mk]; omega
  simp [ggBCCoroot, hnot, hiff, Pi.single_apply]

private lemma ggQ2x_rootFun_last (n : ℕ) (ε : ZMod 3) (hn : 0 < n) :
    ggBCRootFun n ε ⟨n-1, by omega⟩ =
      (Pi.single ⟨n-1, by omega⟩ (2/ε) : Fin n → ZMod 3) := by
  funext j
  have hnot : ¬ (n - 1) + 1 < n := by omega
  have hiff : ((j:ℕ)+1 = n) ↔ j = (⟨n-1, by omega⟩ : Fin n) := by
    constructor
    · intro h; apply Fin.ext; simp only [Fin.val_mk]; omega
    · intro h; subst h; simp only [Fin.val_mk]; omega
  simp [ggBCRootFun, hnot, hiff, Pi.single_apply]

private lemma ggQ2x_dot_chain_chain (n : ℕ) (i j : Fin n) (hi : (i:ℕ)+1 < n)
    (hj : (j:ℕ)+1 < n) :
    (((Pi.single i (1:ZMod 3) : Fin n → ZMod 3) -
      (Pi.single ⟨(i:ℕ)+1, hi⟩ (1:ZMod 3) : Fin n → ZMod 3)) ⬝ᵥ
      ((Pi.single j (1:ZMod 3) : Fin n → ZMod 3) -
        (Pi.single ⟨(j:ℕ)+1, hj⟩ (1:ZMod 3) : Fin n → ZMod 3))) =
      (if i = j then 2 else if j = (⟨(i:ℕ)+1, hi⟩ : Fin n) then -1
        else if i = (⟨(j:ℕ)+1, hj⟩ : Fin n) then -1 else 0) := by
  by_cases h1 : i = j
  · subst h1
    have hlt : i < (⟨(i:ℕ)+1, hi⟩ : Fin n) := by rw [Fin.lt_def]; simp
    simp [sub_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single,
      hlt.ne, hlt.ne']
    rfl
  · by_cases h2 : j = (⟨(i:ℕ)+1, hi⟩ : Fin n)
    · subst h2
      have hlt : i < (⟨(i:ℕ)+1, hi⟩ : Fin n) := by rw [Fin.lt_def]; simp
      have hlt2 : (⟨(i:ℕ)+1, hi⟩ : Fin n) <
          (⟨(i:ℕ)+1+1, by omega⟩ : Fin n) := by rw [Fin.lt_def]; simp
      have hlt3 : i < (⟨(i:ℕ)+1+1, by omega⟩ : Fin n) := hlt.trans hlt2
      simp [sub_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single,
        hlt.ne, hlt.ne', hlt2.ne, hlt2.ne', hlt3.ne, hlt3.ne']
      rfl
    · by_cases h3 : i = (⟨(j:ℕ)+1, hj⟩ : Fin n)
      · subst h3
        have hlt : j < (⟨(j:ℕ)+1, hj⟩ : Fin n) := by rw [Fin.lt_def]; simp
        have hlt2 : (⟨(j:ℕ)+1, hj⟩ : Fin n) <
            (⟨(j:ℕ)+1+1, by omega⟩ : Fin n) := by rw [Fin.lt_def]; simp
        have hlt3 : j < (⟨(j:ℕ)+1+1, by omega⟩ : Fin n) := hlt.trans hlt2
        simp [sub_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single,
          h1, h2, hlt.ne, hlt.ne', hlt2.ne, hlt2.ne', hlt3.ne, hlt3.ne']
        rfl
      · have hlt : i < (⟨(i:ℕ)+1, hi⟩ : Fin n) := by rw [Fin.lt_def]; simp
        have hlt2 : j < (⟨(j:ℕ)+1, hj⟩ : Fin n) := by rw [Fin.lt_def]; simp
        have hne3 : (⟨(i:ℕ)+1, hi⟩ : Fin n) ≠ ⟨(j:ℕ)+1, hj⟩ := by
          intro hh
          have hv := Fin.ext_iff.mp hh
          have h1v : (i:ℕ) ≠ (j:ℕ) := fun h => h1 (Fin.ext h)
          simp only [Fin.val_mk] at hv
          omega
        simp [sub_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single,
          h1, h2, h3, hlt.ne, hlt.ne', hlt2.ne, hlt2.ne', hne3]

private lemma ggQ2x_dot_chain_last (n : ℕ) (ε : ZMod 3) (i : Fin n) (hi : (i:ℕ)+1 < n)
    (hn : 0 < n) :
    (((Pi.single i (1:ZMod 3) : Fin n → ZMod 3) -
      (Pi.single ⟨(i:ℕ)+1, hi⟩ (1:ZMod 3) : Fin n → ZMod 3)) ⬝ᵥ
      (Pi.single ⟨n-1, by omega⟩ ε : Fin n → ZMod 3)) =
      (if (⟨(i:ℕ)+1, hi⟩ : Fin n) = ⟨n-1, by omega⟩ then -ε else 0) := by
  have hli : (⟨n-1, by omega⟩ : Fin n) ≠ i := by
    intro hl; have hv := Fin.ext_iff.mp hl; simp only [Fin.val_mk] at hv; omega
  by_cases h : (⟨(i:ℕ)+1, hi⟩ : Fin n) = ⟨n-1, by omega⟩
  · simp [sub_dotProduct, dotProduct_single, Pi.single_apply, h, hli]
    rfl
  · simp [sub_dotProduct, dotProduct_single, Pi.single_apply, h, hli]

private lemma ggQ2x_dot_last_chain (n : ℕ) (ε : ZMod 3) (j : Fin n) (hj : (j:ℕ)+1 < n)
    (hn : 0 < n) :
    ((Pi.single ⟨n-1, by omega⟩ (2/ε) : Fin n → ZMod 3) ⬝ᵥ
      ((Pi.single j (1:ZMod 3) : Fin n → ZMod 3) -
        (Pi.single ⟨(j:ℕ)+1, hj⟩ (1:ZMod 3) : Fin n → ZMod 3))) =
      (if (⟨(j:ℕ)+1, hj⟩ : Fin n) = ⟨n-1, by omega⟩ then -(2/ε) else 0) := by
  rw [dotProduct_comm]
  exact ggQ2x_dot_chain_last n (2/ε) j hj hn

private lemma ggQ2x_dot_last_last (n : ℕ) (ε : ZMod 3) (hn : 0 < n) (hε : ε ≠ 0) :
    (Pi.single ⟨n-1, by omega⟩ (2/ε) : Fin n → ZMod 3) ⬝ᵥ
      (Pi.single ⟨n-1, by omega⟩ ε : Fin n → ZMod 3) = 2 := by
  rw [dotProduct_single]
  simp only [Pi.single_eq_same]
  field_simp

private lemma ggQ2x_B_chain_chain (n : ℕ) (hn : 3 ≤ n) (i j : Fin n)
    (hi : (i:ℕ)+1 < n) (hj : (j:ℕ)+1 < n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1 else if (i:ℕ)+1 = (j:ℕ) then 3
        else if (j:ℕ)+1 = (i:ℕ) then 3 else 2) := by
  have h4 : ¬ ((i:ℕ) = n-1 ∧ (j:ℕ) = n-2 ∨ (j:ℕ) = n-1 ∧ (i:ℕ) = n-2) := by
    intro h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  simp only [CoxeterMatrix.B, Matrix.of_apply]
  rw [if_neg h4]
  by_cases h1 : i = j
  · subst h1; simp
  · by_cases h2 : (i:ℕ)+1 = (j:ℕ)
    · have hcond : (j:ℕ)+1 = (i:ℕ) ∨ (i:ℕ)+1 = (j:ℕ) := Or.inr h2
      rw [if_pos hcond]; simp [h1, h2]
    · by_cases h3 : (j:ℕ)+1 = (i:ℕ)
      · have hcond : (j:ℕ)+1 = (i:ℕ) ∨ (i:ℕ)+1 = (j:ℕ) := Or.inl h3
        rw [if_pos hcond]; simp [h1, h2, h3]
      · have hcond : ¬ ((j:ℕ)+1 = (i:ℕ) ∨ (i:ℕ)+1 = (j:ℕ)) := by tauto
        rw [if_neg hcond]; simp [h1, h2, h3]

private lemma ggQ2x_B_chain_last (n : ℕ) (hn : 3 ≤ n) (i : Fin n) (hi : (i:ℕ)+1 < n) :
    (CoxeterMatrix.B n) i (⟨n-1, by omega⟩ : Fin n) =
      (if (⟨(i:ℕ)+1, hi⟩ : Fin n) = ⟨n-1, by omega⟩ then 4 else 2) := by
  by_cases hnext : (⟨(i:ℕ)+1, hi⟩ : Fin n) = (⟨n-1, by omega⟩ : Fin n)
  · have hv := Fin.ext_iff.mp hnext
    simp only [Fin.val_mk] at hv
    have hival : (i:ℕ) = n - 2 := by omega
    have hn2 : n - 2 ≠ n - 1 := by omega
    have hs : n - 2 + 1 = n - 1 := by omega
    simp [CoxeterMatrix.B, Fin.ext_iff, hival, hn2, hs]
  · have hvne : (i:ℕ)+1 ≠ n - 1 := by
      intro hv; apply hnext; apply Fin.ext; simp only [Fin.val_mk]; omega
    have hi_ne_last : (i:ℕ) ≠ n - 1 := by omega
    have hi_ne_p : (i:ℕ) ≠ n - 2 := by omega
    have hn_ne_i : n - 1 + 1 ≠ (i:ℕ) := by omega
    simp [CoxeterMatrix.B, Fin.ext_iff, hnext, hvne, hi_ne_last, hi_ne_p, hn_ne_i]

private lemma ggQ2x_B_last_chain (n : ℕ) (hn : 3 ≤ n) (j : Fin n) (hj : (j:ℕ)+1 < n) :
    (CoxeterMatrix.B n) (⟨n-1, by omega⟩ : Fin n) j =
      (if (⟨(j:ℕ)+1, hj⟩ : Fin n) = ⟨n-1, by omega⟩ then 4 else 2) := by
  by_cases hnext : (⟨(j:ℕ)+1, hj⟩ : Fin n) = (⟨n-1, by omega⟩ : Fin n)
  · have hv := Fin.ext_iff.mp hnext
    simp only [Fin.val_mk] at hv
    have hjval : (j:ℕ) = n - 2 := by omega
    have hn2 : n - 2 ≠ n - 1 := by omega
    have hs : n - 2 + 1 = n - 1 := by omega
    simp [CoxeterMatrix.B, Fin.ext_iff, hjval, hn2, hs]
    omega
  · have hvne : (j:ℕ)+1 ≠ n - 1 := by
      intro hv; apply hnext; apply Fin.ext; simp only [Fin.val_mk]; omega
    have hj_ne_last : (j:ℕ) ≠ n - 1 := by omega
    have hj_ne_p : (j:ℕ) ≠ n - 2 := by omega
    have h1 : (⟨n-1, by omega⟩ : Fin n) ≠ (⟨n-2, by omega⟩ : Fin n) := by
      intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
    have hne1 : ¬ n - 1 = (j:ℕ) := by omega
    have hne2 : ¬ n - 1 + 1 = (j:ℕ) := by omega
    simp [CoxeterMatrix.B, Fin.ext_iff, hnext, hvne, hj_ne_last, hj_ne_p, h1, hne1, hne2]

private lemma ggQ2x_cartan_of_B_eq2 {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : GGIntCartan (CoxeterMatrix.B n) C) {i j : Fin n} (hij : i ≠ j)
    (hB : (CoxeterMatrix.B n) i j = 2) : C i j = 0 := by
  rcases hC.2 i j hij with ⟨hm, h, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · exact h
  · rw [hm] at hB; norm_num at hB
  · rw [hm] at hB; norm_num at hB
  · rw [hm] at hB; norm_num at hB

private lemma ggQ2x_cartan_of_B_eq3 {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : GGIntCartan (CoxeterMatrix.B n) C) {i j : Fin n} (hij : i ≠ j)
    (hB : (CoxeterMatrix.B n) i j = 3) : C i j = -1 := by
  rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [hm] at hB; norm_num at hB
  · exact h
  · rw [hm] at hB; norm_num at hB
  · rw [hm] at hB; norm_num at hB

private lemma ggQ2x_cartan_of_B_eq4 {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : GGIntCartan (CoxeterMatrix.B n) C) {i j : Fin n} (hij : i ≠ j)
    (hB : (CoxeterMatrix.B n) i j = 4) : C i j * C j i = 2 ∧ C i j < 0 ∧ C j i < 0 := by
  rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, -, -, -⟩
  · rw [hm] at hB; norm_num at hB
  · rw [hm] at hB; norm_num at hB
  · exact ⟨h1, h2, h3⟩
  · rw [hm] at hB; norm_num at hB

private lemma ggQ2x_cartan_chain_chain (n : ℕ) (hn : 3 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : GGIntCartan (CoxeterMatrix.B n) C) (i j : Fin n)
    (hi : (i:ℕ)+1 < n) (hj : (j:ℕ)+1 < n) :
    (C i j : ZMod 3) =
      (if i = j then 2 else if j = (⟨(i:ℕ)+1, hi⟩ : Fin n) then -1
        else if i = (⟨(j:ℕ)+1, hj⟩ : Fin n) then -1 else 0) := by
  by_cases h1 : i = j
  · subst h1; rw [if_pos rfl, hC.1]; norm_num
  · rw [if_neg h1]
    have hB := ggQ2x_B_chain_chain n hn i j hi hj
    by_cases h2 : j = (⟨(i:ℕ)+1, hi⟩ : Fin n)
    · rw [if_pos h2]
      have hB3 : (CoxeterMatrix.B n) i j = 3 := by
        rw [hB, if_neg h1]
        have h2' : (i:ℕ)+1 = (j:ℕ) := by have := Fin.ext_iff.mp h2; simpa using this.symm
        rw [if_pos h2']
      have hCij := ggQ2x_cartan_of_B_eq3 hC h1 hB3
      rw [hCij]; rfl
    · rw [if_neg h2]
      by_cases h3 : i = (⟨(j:ℕ)+1, hj⟩ : Fin n)
      · rw [if_pos h3]
        have hB3 : (CoxeterMatrix.B n) i j = 3 := by
          rw [hB, if_neg h1]
          have h2' : ¬ (i:ℕ)+1 = (j:ℕ) := by intro h; apply h2; apply Fin.ext; simpa using h.symm
          have h3' : (j:ℕ)+1 = (i:ℕ) := by have := Fin.ext_iff.mp h3; simpa using this.symm
          rw [if_neg h2', if_pos h3']
        have hCij := ggQ2x_cartan_of_B_eq3 hC h1 hB3
        rw [hCij]; rfl
      · rw [if_neg h3]
        have hB2 : (CoxeterMatrix.B n) i j = 2 := by
          rw [hB, if_neg h1]
          have h2' : ¬ (i:ℕ)+1 = (j:ℕ) := by intro h; apply h2; apply Fin.ext; simpa using h.symm
          have h3' : ¬ (j:ℕ)+1 = (i:ℕ) := by intro h; apply h3; apply Fin.ext; simpa using h.symm
          rw [if_neg h2', if_neg h3']
        have hCij := ggQ2x_cartan_of_B_eq2 hC h1 hB2
        rw [hCij]; rfl

private lemma ggQ2x_dot_eq_cartan (n : ℕ) (hn : 3 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : GGIntCartan (CoxeterMatrix.B n) C) (ε : ZMod 3)
    (hε : ε = 1 ∨ ε = -1)
    (hCpl : (C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) : ZMod 3) = -ε)
    (hClp : (C (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) : ZMod 3) = -(2/ε)) :
    ∀ i j, ggBCRootFun n ε i ⬝ᵥ ggBCCoroot n ε j = (C i j : ZMod 3) := by
  intro i j
  by_cases hi : (i:ℕ)+1 < n
  · by_cases hj : (j:ℕ)+1 < n
    · rw [ggQ2x_rootFun_eq_single n ε i hi, ggQ2x_coroot_eq_single n ε j hj,
        ggQ2x_dot_chain_chain n i j hi hj]
      exact (ggQ2x_cartan_chain_chain n hn C hC i j hi hj).symm
    · have hjlast : j = (⟨n-1, by omega⟩ : Fin n) := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [hjlast]
      rw [ggQ2x_rootFun_eq_single n ε i hi, ggQ2x_coroot_last n ε (by omega),
        ggQ2x_dot_chain_last n ε i hi (by omega)]
      by_cases hnext : (⟨(i:ℕ)+1, hi⟩ : Fin n) = (⟨n-1, by omega⟩ : Fin n)
      · rw [if_pos hnext]
        have hieq : i = (⟨n-2, by omega⟩ : Fin n) := by
          apply Fin.ext; have := Fin.ext_iff.mp hnext; simp only [Fin.val_mk] at this ⊢; omega
        rw [hieq]
        rw [hCpl]
      · rw [if_neg hnext]
        have hB2 : (CoxeterMatrix.B n) i (⟨n-1, by omega⟩ : Fin n) = 2 := by
          rw [ggQ2x_B_chain_last n hn i hi, if_neg hnext]
        have hine : i ≠ (⟨n-1, by omega⟩ : Fin n) := by
          intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
        have hCij := ggQ2x_cartan_of_B_eq2 hC hine hB2
        rw [hCij]; rfl
  · have hilast : i = (⟨n-1, by omega⟩ : Fin n) := by
      apply Fin.ext; simp only [Fin.val_mk]; omega
    rw [hilast]
    by_cases hj : (j:ℕ)+1 < n
    · rw [ggQ2x_rootFun_last n ε (by omega), ggQ2x_coroot_eq_single n ε j hj,
        ggQ2x_dot_last_chain n ε j hj (by omega)]
      by_cases hnext : (⟨(j:ℕ)+1, hj⟩ : Fin n) = (⟨n-1, by omega⟩ : Fin n)
      · rw [if_pos hnext]
        have hjeq : j = (⟨n-2, by omega⟩ : Fin n) := by
          apply Fin.ext; have := Fin.ext_iff.mp hnext; simp only [Fin.val_mk] at this ⊢; omega
        rw [hjeq]
        rw [hClp]
      · rw [if_neg hnext]
        have hB2 : (CoxeterMatrix.B n) (⟨n-1, by omega⟩ : Fin n) j = 2 := by
          rw [ggQ2x_B_last_chain n hn j hj, if_neg hnext]
        have hine : (⟨n-1, by omega⟩ : Fin n) ≠ j := by
          intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
        have hCij := ggQ2x_cartan_of_B_eq2 hC hine hB2
        rw [hCij]; rfl
    · have hjlast : j = (⟨n-1, by omega⟩ : Fin n) := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [hjlast]
      have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> decide
      rw [ggQ2x_rootFun_last n ε (by omega), ggQ2x_coroot_last n ε (by omega),
        ggQ2x_dot_last_last n ε (by omega) hε0]
      rw [hC.1]; rfl

private noncomputable def ggQ2x_prefixSum {n : ℕ} (i : Fin n) : GGBCV n →ₗ[ZMod 3] ZMod 3 :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), LinearMap.proj j

private lemma ggQ2x_prefixSum_single {n : ℕ} (i j : Fin n) (c : ZMod 3) :
    ggQ2x_prefixSum i (Pi.single j c : Fin n → ZMod 3) = if j ≤ i then c else 0 := by
  simp only [ggQ2x_prefixSum, LinearMap.sum_apply, LinearMap.proj_apply]
  by_cases h : j ≤ i
  · rw [if_pos h]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : j ≠ b := fun hbj => hb hbj.symm
      simp [Pi.single_apply, hne]
    · intro hj
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩) hj
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' : b ≤ i := (Finset.mem_filter.mp hb).2
    have hne : j ≠ b := by intro hbj; exact h (hbj ▸ hb')
    simp [Pi.single_apply, hne]

private lemma ggQ2x_prefixSum_coroot (n : ℕ) (ε : ZMod 3) (i j : Fin n) :
    ggQ2x_prefixSum i (ggBCCoroot n ε j) =
      (if i = j then (if (i:ℕ)+1 < n then 1 else ε) else 0) := by
  by_cases hj : (j:ℕ)+1 < n
  · rw [ggQ2x_coroot_eq_single n ε j hj, map_sub, ggQ2x_prefixSum_single,
      ggQ2x_prefixSum_single]
    by_cases hij : i = j
    · subst hij
      have hnot : ¬ ((⟨(i:ℕ)+1, hj⟩ : Fin n) ≤ i) := by
        rw [Fin.le_def]; simp only [Fin.val_mk]; omega
      rw [if_pos (le_refl i), if_neg hnot, if_pos rfl, if_pos hj]
      decide
    · by_cases hji : (⟨(j:ℕ)+1, hj⟩ : Fin n) ≤ i
      · have hle : j ≤ i := by
          rw [Fin.le_def] at hji ⊢
          simp only [Fin.val_mk] at hji
          omega
        rw [if_neg hij, if_pos hle, if_pos hji]
        decide
      · have hlen : ¬ (j ≤ i) := by
          intro h
          have h1 : (j:ℕ) ≤ (i:ℕ) := by rwa [Fin.le_def] at h
          have h2 : (j:ℕ)+1 ≤ (i:ℕ) := by
            by_contra hh
            exact hji (by rw [Fin.le_def]; omega)
          exact absurd h2 (by omega)
        rw [if_neg hij, if_neg hlen, if_neg hji]
        decide
  · have hjlast : j = (⟨n-1, by omega⟩ : Fin n) := by
      apply Fin.ext; simp only [Fin.val_mk]; omega
    rw [hjlast, ggQ2x_coroot_last n ε (by omega), ggQ2x_prefixSum_single]
    by_cases hilast : i = (⟨n-1, by omega⟩ : Fin n)
    · subst hilast
      have hnot : ¬ ((⟨n-1, by omega⟩ : Fin n):ℕ)+1 < n := by
        simp only [Fin.val_mk]; omega
      simp [hnot]
    · have hle : ¬ ((⟨n-1, by omega⟩ : Fin n) ≤ i) := by
        rw [Fin.le_def]; simp only [Fin.val_mk]
        intro h; exact hilast (Fin.ext (by simp only [Fin.val_mk]; omega))
      simp [hle, hilast]

private lemma ggQ2x_prefix_det_ne_zero (n : ℕ) (hn : 3 ≤ n) (ε : ZMod 3) (hε : ε ≠ 0) :
    (Matrix.of fun i j => ggQ2x_prefixSum i (ggBCCoroot n ε j)).det ≠ 0 := by
  have hM : (Matrix.of fun i j => ggQ2x_prefixSum i (ggBCCoroot n ε j)) =
      Matrix.diagonal (fun i : Fin n => if (i:ℕ)+1 < n then (1:ZMod 3) else ε) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_apply, ggQ2x_prefixSum_coroot]
  rw [hM, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (⟨n-1, by omega⟩ : Fin n)]
  · have hnot : ¬ n - 1 + 1 < n := by omega
    simp only [Fin.val_mk]
    rw [if_neg hnot]
    exact hε
  · intro b _ hb
    by_cases hb' : (b:ℕ)+1 < n
    · simp [hb']
    · have hbeq : b = (⟨n-1, by omega⟩ : Fin n) := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      exact absurd hbeq hb
  · intro h
    exact absurd (Finset.mem_univ (⟨n-1, by omega⟩ : Fin n)) h

private lemma ggQ2x_coroot_linearIndependent (n : ℕ) (hn : 3 ≤ n) (ε : ZMod 3)
    (hε : ε ≠ 0) :
    LinearIndependent (ZMod 3) (ggBCCoroot n ε) := by
  apply linearIndependent_of_det_ne_zero (h := ggBCCoroot n ε)
    (α := fun i => ggQ2x_prefixSum i)
  exact ggQ2x_prefix_det_ne_zero n hn ε hε

theorem ggQ2_BC_coordinates (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 3 ≤ n) (e : Fin n ≃ D.ι)
    (he : D.coxeter = (CoxeterMatrix.B n).reindex e) :
    ∃ (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3), (ε = 1 ∨ ε = -1) ∧
      (∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i) ∧
      ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j := by
  classical
  let C : Matrix (Fin n) (Fin n) ℤ := fun i j => D.cartan (e i) (e j)
  have hC : GGIntCartan (CoxeterMatrix.B n) C := by
    constructor
    · intro i; exact D.isCartan.1 (e i)
    · intro i j hij
      have h := D.isCartan.2 (e i) (e j) (fun h => hij (e.injective h))
      simpa [C, he, CoxeterMatrix.reindex_apply] using h
  have hB4 : (CoxeterMatrix.B n) (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = 4 := by
    simp [CoxeterMatrix.B, Fin.ext_iff]
    omega
  have hpne : (⟨n-2, by omega⟩ : Fin n) ≠ (⟨n-1, by omega⟩ : Fin n) := by
    intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
  have hpl := ggQ2x_cartan_of_B_eq4 hC hpne hB4
  have hcases : C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = -1 ∨
      C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = -2 := by
    have hle : C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) ≤ -1 := by omega
    have hge : -2 ≤ C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) := by
      nlinarith [hpl.1, hpl.2.1, hpl.2.2]
    omega
  let ε : ZMod 3 := - (C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) : ZMod 3)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hcases with h | h
    · left; simp only [ε, h]; decide
    · right; simp only [ε, h]; decide
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> decide
  have hε1_of : ∀ h : C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = -1,
      ε = 1 := by
    intro h; simp only [ε, h]; decide
  have hεm1_of : ∀ h : C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = -2,
      ε = -1 := by
    intro h; simp only [ε, h]; decide
  have hCpl : (C (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) : ZMod 3) = -ε := by
    rcases hcases with h | h
    · rw [h, hε1_of h]; decide
    · rw [h, hεm1_of h]; decide
  have hClp : (C (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) : ZMod 3) = -(2/ε) := by
    rcases hcases with h | h
    · have hlp : C (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) = -2 := by
        have h1 := hpl.1; rw [h] at h1; omega
      have hdiv : (2/(1:ZMod 3) : ZMod 3) = 2 := by norm_num
      rw [hlp, hε1_of h, hdiv]; rfl
    · have hlp : C (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) = -1 := by
        have h1 := hpl.1; rw [h] at h1; omega
      have hdiv : (2/(-1:ZMod 3) : ZMod 3) = -2 := by
        have hh : (-1 : ZMod 3)⁻¹ = -1 := ZMod.inv_neg_one 3
        rw [div_eq_mul_inv, hh]; rfl
      rw [hlp, hεm1_of h, hdiv]; rfl
  have hdot := ggQ2x_dot_eq_cartan n hn C hC ε hε hCpl hClp
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty D.ι := ⟨e ⟨0, by omega⟩⟩
  let b0 : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hb0 : ⇑b0 = D.coroot := coe_basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  let b : Basis (Fin n) (ZMod 3) D.V := b0.reindex e.symm
  have hb : ∀ i, b i = D.coroot (e i) := by
    intro i
    change (b0.reindex e.symm) i = D.coroot (e i)
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    exact congrFun hb0 (e i)
  let bu : Basis (Fin n) (ZMod 3) (GGBCV n) :=
    basisOfLinearIndependentOfCardEqFinrank (ggQ2x_coroot_linearIndependent n hn ε hε0) (by
      change Fintype.card (Fin n) = finrank (ZMod 3) (Fin n → ZMod 3)
      rw [Module.finrank_pi])
  have hbu : ⇑bu = ggBCCoroot n ε := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let τ : D.V ≃ₗ[ZMod 3] GGBCV n := b.equiv bu (Equiv.refl _)
  refine ⟨τ, ε, hε, ?_, ?_⟩
  · intro i
    rw [show D.coroot (e i) = b i from (hb i).symm]
    rw [Module.Basis.equiv_apply, hbu]
    rfl
  · intro i v
    have hroot : D.root (e i) =
        (ggBCDot (ggBCRootFun n ε i)).comp (τ : D.V →ₗ[ZMod 3] GGBCV n) := by
      apply b.ext
      intro j
      rw [LinearMap.comp_apply]
      have hbτ : (↑τ : D.V → GGBCV n) (b j) = ggBCCoroot n ε j := by
        rw [Module.Basis.equiv_apply, hbu]
        rfl
      have h1 : D.root (e i) (b j) = (C i j : ZMod 3) := by
        rw [hb j, D.pairing]
      have hdotval : ggBCDot (ggBCRootFun n ε i) (ggBCCoroot n ε j) =
          ggBCRootFun n ε i ⬝ᵥ ggBCCoroot n ε j := by
        simp [ggBCDot, LinearMap.sum_apply, LinearMap.proj_apply, dotProduct]
      have h2 : ggBCDot (ggBCRootFun n ε i) ((↑τ : D.V → GGBCV n) (b j)) =
          (C i j : ZMod 3) := by
        exact (congrArg (ggBCDot (ggBCRootFun n ε i)) hbτ).trans
          (hdotval.trans (hdot i j))
      exact h1.trans h2.symm
    have := congrArg (fun f => f v) hroot
    simpa [LinearMap.comp_apply, ggBCDot, LinearMap.sum_apply, LinearMap.proj_apply] using this

end CFSG.StandardType

end
