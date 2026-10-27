module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvMain

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem fs81Nt_exists_ne3 {n : ℕ} (hn : 3 ≤ n) (a b c : Fin (n + 1)) :
    ∃ k : Fin (n + 1), k ≠ a ∧ k ≠ b ∧ k ≠ c := by
  classical
  have h : ({a, b, c} : Finset (Fin (n + 1))).card < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2⟩

theorem fs81Nt_exists_ne4 {n : ℕ} (hn : 4 ≤ n) (a b c d : Fin (n + 1)) :
    ∃ k : Fin (n + 1), k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d := by
  classical
  have h : ({a, b, c, d} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩

theorem dsign_isSign {n : ℕ} (k₀ k₁ : Fin (n + 1)) : IsSign (dsign k₀ k₁) := fun k => by
  unfold dsign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem dsign_of_ne {n : ℕ} {k₀ k₁ k : Fin (n + 1)} (h₀ : k ≠ k₀) (h₁ : k ≠ k₁) :
    dsign k₀ k₁ k = 1 := by
  unfold dsign
  rw [if_neg (by tauto)]

theorem dsign_left {n : ℕ} (k₀ k₁ : Fin (n + 1)) : dsign k₀ k₁ k₀ = -1 := by
  unfold dsign
  rw [if_pos (Or.inl rfl)]

theorem dsign_prod {n : ℕ} {k₀ k₁ : Fin (n + 1)} (h₀ : k₀ ≠ 0) (h₁ : k₁ ≠ 0) (hne : k₀ ≠ k₁) :
    ∏ i : Fin n, dsign k₀ k₁ i.succ = 1 := by
  classical
  obtain ⟨a, rfl⟩ := Fin.exists_succ_eq.mpr h₀
  obtain ⟨b, rfl⟩ := Fin.exists_succ_eq.mpr h₁
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  have : ∀ i : Fin n, dsign a.succ b.succ i.succ =
      if i ∈ ({a, b} : Finset (Fin n)) then -1 else 1 := by
    intro i
    simp only [dsign, Fin.succ_inj, Finset.mem_insert, Finset.mem_singleton]
  simp only [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, Finset.card_pair hab]
  decide

omit [Finite G] in
theorem orth_acts {n : ℕ} {B : Basis3 G (n + 1)} {b₀ : G}
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {σ : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) (hσ : σ 0 = 0)
    (hs0 : s 0 = 1) (hprod : ∏ i : Fin n, s i.succ = 1) :
    ∃ g ∈ Subgroup.centralizer ({b₀} : Set G), B.Acts g (spMat σ s) := by
  have h : spMat σ s ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
    rcases hCm with h | h <;> rw [h]
    · exact ⟨σ, s, hs, ⟨hσ, hs0⟩, rfl⟩
    · exact ⟨σ, s, hs, ⟨hσ, hs0, hprod⟩, rfl⟩
  exact h

theorem orth_signRealized {n : ℕ} {B : Basis3 G (n + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E)
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) (hs0 : s 0 = 1)
    (hprod : ∏ i : Fin n, s i.succ = 1) : SignRealized B E s := by
  obtain ⟨g, -, hg⟩ := orth_acts hCm hs (Equiv.Perm.one_apply 0) hs0 hprod
  exact ⟨hs, hs0, g, hB.1 ▸ B.mem_normalizer_of_acts hg, hg⟩

theorem orthSignData {n : ℕ} (hn : 4 ≤ n) {B : Basis3 G (n + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E)
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n) :
    SignChanges B.b b₀ E ∧ DiagSigns B E ∧ CoordTrans B b₀ E ∧ DiagSigns3 B E ∧
      (∃ k₀ k₁ : Fin (n + 1), k₀ ≠ 0 ∧ k₁ ≠ 0 ∧ k₀ ≠ k₁ ∧ SignRealized B E (dsign k₀ k₁)) := by
  have hsr : ∀ {k₀ k₁ : Fin (n + 1)}, k₀ ≠ 0 → k₁ ≠ 0 → k₀ ≠ k₁ →
      SignRealized B E (dsign k₀ k₁) := fun h₀ h₁ hne =>
    orth_signRealized hB hCm (dsign_isSign _ _) (dsign_of_ne (Ne.symm h₀) (Ne.symm h₁))
      (dsign_prod h₀ h₁ hne)
  have hinv : ∀ i : Fin (n + 1), B.b i ^ ((-1 : ZMod 3).val) = (B.b i)⁻¹ := fun i => by
    have h3 : B.b i ^ 3 = 1 := by rw [← B.ord i]; exact pow_orderOf_eq_one _
    exact eq_inv_of_mul_eq_one_left (by
      rw [show (-1 : ZMod 3).val = 2 from rfl, ← pow_succ]
      exact h3)
  have hm1 : (-1 : ZMod 3) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hi hji
    obtain ⟨k, hk0, hki, hkj⟩ := fs81Nt_exists_ne3 (by omega) 0 i j
    obtain ⟨-, -, d, hdN, hd⟩ := hsr hi hk0 (Ne.symm hki)
    refine ⟨d, hdN, ?_, ?_, ?_⟩
    · have := B.acts_spMat_one hd 0
      rwa [dsign_of_ne (Ne.symm hi) (Ne.symm hk0), ZMod.val_one, pow_one, hB.2.1] at this
    · rw [B.acts_spMat_one hd i, dsign_left, hinv]
    · rw [B.acts_spMat_one hd j, dsign_of_ne hji (Ne.symm hkj), ZMod.val_one, pow_one]
  ·
    intro k l hk hl hlk
    obtain ⟨m, hm0, hmk, hml⟩ := fs81Nt_exists_ne3 (by omega) 0 k l
    obtain ⟨hs, hs0, d, hdN, hd⟩ := hsr hk hm0 (Ne.symm hmk)
    exact ⟨d, hdN, dsign k m, hs, hs0, hd, by
      rw [dsign_of_ne hlk (Ne.symm hml), dsign_left]
      exact Ne.symm hm1⟩
  ·
    have h10 : (1 : Fin (n + 1)) ≠ 0 := fun h => by
      rw [Fin.one_eq_zero_iff] at h
      omega
    refine ⟨1, h10, fun k hk => ?_⟩
    have hσ : Equiv.swap (1 : Fin (n + 1)) k 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h10) (Ne.symm hk)
    obtain ⟨g, hgC, hg⟩ := orth_acts hCm (s := fun _ => 1) (fun _ => Or.inl rfl) hσ rfl
      (by simp)
    refine ⟨g, hB.1 ▸ B.mem_normalizer_of_acts hg, ?_, _, hg 1, ?_⟩
    · rw [← Subgroup.mem_centralizer_iff.mp hgC b₀ (Set.mem_singleton b₀), mul_inv_cancel_right]
    · simp [spMat_apply, Equiv.swap_apply_left]
  ·
    intro i j k hi hj hk hji
    by_cases hki : k = i
    · subst hki
      obtain ⟨m, hm0, hmk, hmj⟩ := fs81Nt_exists_ne3 (by omega) 0 k j
      refine ⟨dsign j m, hsr hj hm0 (Ne.symm hmj), ?_⟩
      rw [dsign_of_ne (Ne.symm hji) (Ne.symm hmk), dsign_left, one_mul]
      exact Ne.symm hm1
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨m, hm0, hmi, hmk⟩ := fs81Nt_exists_ne3 (by omega) 0 i k
      refine ⟨dsign i m, hsr hi hm0 (Ne.symm hmi), ?_⟩
      rw [dsign_of_ne hji (Ne.symm hmk), dsign_left, mul_one]
      exact Ne.symm hm1
    · obtain ⟨m, hm0, hmi, hmj, hmk⟩ := fs81Nt_exists_ne4 hn 0 i j k
      refine ⟨dsign k m, hsr hk hm0 (Ne.symm hmk), ?_⟩
      rw [dsign_left, dsign_of_ne (Ne.symm hki) (Ne.symm hmi),
        dsign_of_ne (Ne.symm hkj) (Ne.symm hmj), one_mul]
      exact hm1
  ·
    refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
    · simp [Fin.ext_iff] at h
    · simp [Fin.ext_iff] at h
    · simp [Fin.ext_iff] at h
    · exact hsr (fun h => by simp [Fin.ext_iff] at h) (fun h => by simp [Fin.ext_iff] at h)
        (fun h => by simp [Fin.ext_iff] at h)

end CFSG.StandardType.FrameRoute.FS81

end
