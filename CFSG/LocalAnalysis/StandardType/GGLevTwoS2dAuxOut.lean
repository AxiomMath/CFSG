module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxRefl

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2d_neg_mem_Cl (n : ℕ) (hn : 4 ≤ n) {S : Set (Fin n → ℤ)} {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanD n) β) (hβcl : Cl (isFiniteType_cartanD n) S β) :
    Cl (isFiniteType_cartanD n) S (-β) := by
  have h : Cl (isFiniteType_cartanD n) S
      (weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) β) β) :=
    Cl.refl hβcl hβcl
  rwa [levTwoS2d_rRefl_self n hn hβ] at h

theorem levTwoS2d_eq_ofCoord (n : ℕ) (_hn : 4 ≤ n) {x : Fin n → ℤ} {k a : Fin n} {σ τ : ℤ}
    (hk : k ≠ a) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hx : toStdD n x = Pi.single k σ + Pi.single a τ) :
    x = levTwoS2d_ofCoord n k a σ τ hk hσ hτ :=
  toStdD_injective n (by rw [hx, levTwoS2d_ofCoord_toStdD])


theorem levTwoS2d_neg_sign {s : ℤ} (h : s = 1 ∨ s = -1) : -s = 1 ∨ -s = -1 := by
  omega

theorem levTwoS2d_exists_third (n : ℕ) (hn : 4 ≤ n) (k a : Fin n) :
    ∃ c : Fin n, c ≠ k ∧ c ≠ a := by
  have hlt : ({k, a} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 := Finset.card_insert_le k ({a} : Finset (Fin n))
    simp only [Finset.card_singleton] at h2
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_singleton] at hc
  push Not at hc
  exact ⟨c, hc.1, hc.2⟩

theorem levTwoS2d_neg_ofCoord (n : ℕ) (_hn : 4 ≤ n) {k b : Fin n} {σ τ : ℤ}
    (hbk : k ≠ b) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    - levTwoS2d_ofCoord n k b σ τ hbk hσ hτ =
      levTwoS2d_ofCoord n k b (-σ) (-τ) hbk
        (levTwoS2d_neg_sign hσ)
        (levTwoS2d_neg_sign hτ) := by
  apply toStdD_injective n
  rw [show -levTwoS2d_ofCoord n k b σ τ hbk hσ hτ =
      (-1 : ℤ) • levTwoS2d_ofCoord n k b σ τ hbk hσ hτ by simp,
    toStdD_smul, levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD]
  ext c
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply]
  split_ifs <;> ring

theorem levTwoS2d_reach_coord {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {k : Fin n}
    (hzero : ∀ a, a ≠ k → levTwoS2d_d n hn c a = 0)
    {S : Set (Fin n → ℤ)} (hS : Φ ⊆ S)
    {a : Fin n} (hak : a ≠ k) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hxcl : Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ)) :
    ∀ (b : Fin n) (hbk : b ≠ k) (σ' τ' : ℤ) (hσ' : σ' = 1 ∨ σ' = -1) (hτ' : τ' = 1 ∨ τ' = -1),
      Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k b σ' τ' (Ne.symm hbk) hσ' hτ') := by
  have hdiff : ∀ (b : Fin n) (hbk : b ≠ k),
      Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k b σ τ (Ne.symm hbk) hσ hτ) := by
    intro b hbk
    rcases eq_or_ne a b with rfl | hab
    · exact hxcl
    · set δ := levTwoS2d_ofCoord n a b 1 (-1) hab (Or.inl rfl) (Or.inr rfl) with hδdef
      have hδΦ : δ ∈ Φ := by
        rw [levTwoS2d_mem_Phi_iff n hn hp2 c hΦ hab (Or.inl rfl) (Or.inr rfl)
          (levTwoS2d_ofCoord_toStdD n a b 1 (-1) hab (Or.inl rfl) (Or.inr rfl))]
        rw [hzero a hak, hzero b hbk]
        simp only [mul_zero, add_zero]
      have hcl := Cl.refl (Cl.base (hS hδΦ)) hxcl
      rwa [show weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) δ)
          (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ) =
          levTwoS2d_ofCoord n k b σ τ (Ne.symm hbk) hσ hτ from
        toStdD_injective n (by
          rw [levTwoS2d_toStdD_rRefl_diff_apply n hn hak hbk hab hσ hτ,
            levTwoS2d_ofCoord_toStdD])] at hcl
  have hsum : ∀ (b : Fin n) (hbk : b ≠ k),
      Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k b σ (-τ) (Ne.symm hbk) hσ
        (levTwoS2d_neg_sign hτ)) := by
    intro b hbk
    rcases eq_or_ne a b with rfl | hab
    · obtain ⟨cc, hck, hca⟩ := levTwoS2d_exists_third n hn k a
      have h1 : Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k cc σ τ (Ne.symm hck) hσ hτ) :=
        hdiff cc hck
      set δ := levTwoS2d_ofCoord n cc a 1 1 hca (Or.inl rfl) (Or.inl rfl) with hδdef
      have hδΦ : δ ∈ Φ := by
        rw [levTwoS2d_mem_Phi_add n hn hp2 c hΦ hca
          (levTwoS2d_ofCoord_toStdD n cc a 1 1 hca (Or.inl rfl) (Or.inl rfl))]
        rw [hzero cc hck, hzero a hak]
        exact (neg_zero : -(0 : ZMod p) = 0).symm
      have hcl := Cl.refl (Cl.base (hS hδΦ)) h1
      rwa [show weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) δ)
          (levTwoS2d_ofCoord n k cc σ τ (Ne.symm hck) hσ hτ) =
          levTwoS2d_ofCoord n k a σ (-τ) (Ne.symm hak) hσ
            (levTwoS2d_neg_sign hτ) from
        toStdD_injective n (by
          rw [levTwoS2d_toStdD_rRefl_add_apply n hn hck hak hca hσ hτ,
            levTwoS2d_ofCoord_toStdD, sub_eq_add_neg, Pi.single_neg])] at hcl
    · set δ := levTwoS2d_ofCoord n a b 1 1 hab (Or.inl rfl) (Or.inl rfl) with hδdef
      have hδΦ : δ ∈ Φ := by
        rw [levTwoS2d_mem_Phi_add n hn hp2 c hΦ hab
          (levTwoS2d_ofCoord_toStdD n a b 1 1 hab (Or.inl rfl) (Or.inl rfl))]
        rw [hzero a hak, hzero b hbk]
        exact (neg_zero : -(0 : ZMod p) = 0).symm
      have hcl := Cl.refl (Cl.base (hS hδΦ)) hxcl
      rwa [show weylAction (isFiniteType_cartanD n) (rRefl (isFiniteType_cartanD n) δ)
          (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ) =
          levTwoS2d_ofCoord n k b σ (-τ) (Ne.symm hbk) hσ
            (levTwoS2d_neg_sign hτ) from
        toStdD_injective n (by
          rw [levTwoS2d_toStdD_rRefl_add_apply n hn hak hbk hab hσ hτ,
            levTwoS2d_ofCoord_toStdD, sub_eq_add_neg, Pi.single_neg])] at hcl
  intro b hbk σ' τ' hσ' hτ'
  have h1 := hdiff b hbk
  have h2 := hsum b hbk
  have h3 : Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k b (-σ) (-τ) (Ne.symm hbk)
      (levTwoS2d_neg_sign hσ) (levTwoS2d_neg_sign hτ)) := by
    have hβ := levTwoS2d_ofCoord_isRt n k b σ τ (Ne.symm hbk) hσ hτ
    have hneg := levTwoS2d_neg_mem_Cl n hn hβ h1
    have heq : levTwoS2d_ofCoord n k b (-σ) (-τ) (Ne.symm hbk)
        (levTwoS2d_neg_sign hσ) (levTwoS2d_neg_sign hτ) =
        - levTwoS2d_ofCoord n k b σ τ (Ne.symm hbk) hσ hτ :=
      (levTwoS2d_neg_ofCoord n hn (Ne.symm hbk) hσ hτ).symm
    rwa [← heq] at hneg
  have h4 : Cl (isFiniteType_cartanD n) S (levTwoS2d_ofCoord n k b (-σ) τ (Ne.symm hbk)
      (levTwoS2d_neg_sign hσ) hτ) := by
    have hβ := levTwoS2d_ofCoord_isRt n k b σ (-τ) (Ne.symm hbk) hσ (levTwoS2d_neg_sign hτ)
    have hneg := levTwoS2d_neg_mem_Cl n hn hβ h2
    have heq : levTwoS2d_ofCoord n k b (-σ) τ (Ne.symm hbk) (levTwoS2d_neg_sign hσ) hτ =
        - levTwoS2d_ofCoord n k b σ (-τ) (Ne.symm hbk) hσ (levTwoS2d_neg_sign hτ) := by
      apply toStdD_injective n
      rw [show -levTwoS2d_ofCoord n k b σ (-τ) (Ne.symm hbk) hσ (levTwoS2d_neg_sign hτ) =
          (-1 : ℤ) • levTwoS2d_ofCoord n k b σ (-τ) (Ne.symm hbk) hσ (levTwoS2d_neg_sign hτ) by simp,
        toStdD_smul, levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD]
      ext cc
      simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [heq]
    exact hneg
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
    rcases hσ' with rfl | rfl <;> rcases hτ' with rfl | rfl <;>
    first | exact h1 | exact h2 | exact h3 | exact h4


theorem levTwoS2d_coord_of_notMem {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {k : Fin n}
    (hzero : ∀ a, a ≠ k → levTwoS2d_d n hn c a = 0) {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanD n) β) (hβΦ : β ∉ Φ) :
    ∃ (a : Fin n) (σ τ : ℤ), a ≠ k ∧ (σ = 1 ∨ σ = -1) ∧ (τ = 1 ∨ τ = -1) ∧
      toStdD n β = Pi.single k σ + Pi.single a τ := by
  obtain ⟨i, j, si, sj, hij, hsi, hsj, hβc⟩ := (levTwoS2d_isRt_iff n (by omega) β).1 hβ
  have hβk : toStdD n β k ≠ 0 := by
    intro hk0
    apply hβΦ
    rw [levTwoS2d_Phi_eq_lambda n hn p hp2 c hΦ]
    refine ⟨hβ, ?_⟩
    rw [levTwoS2d_lam_coord n hn hp2 c β]
    apply Finset.sum_eq_zero; intro a _
    by_cases hak : a = k
    · rw [hak, hk0]; ring
    · rw [hzero a hak]; ring
  rcases eq_or_ne i k with rfl | hik
  · exact ⟨j, si, sj, Ne.symm hij, hsi, hsj, hβc⟩
  · have hjk : j = k := by
      by_contra hjk
      exact hβk (by rw [hβc]; simp [Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hjk)])
    subst hjk
    exact ⟨i, sj, si, hik, hsj, hsi, by rw [hβc, add_comm]⟩


end CFSG.StandardType.LevTwo
