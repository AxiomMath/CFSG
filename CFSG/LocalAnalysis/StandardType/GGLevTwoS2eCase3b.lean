module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2eCase3

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2e_mul_pm {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem levTwoS2e_eq_of_mul_pm {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : a * b = 1) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

theorem levTwoS2e_eq_neg_of_mul_pm {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : a * b = -1) : a = -b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

theorem levTwoS2e_pair_of_outside {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p} (_hc₀ : c₀ ≠ 0)
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {β : Fin n → ℤ} (hβ : IsRt (isFiniteType_cartanD n) β) (hβΦ : β ∉ Φ) :
    ∃ (a b : Fin n) (_hab : a ≠ b),
      (toStdD n β = Pi.single a (levTwoS2d_sigma n hn c c₀ a) +
                     Pi.single b (levTwoS2d_sigma n hn c c₀ b)) ∨
      (toStdD n β = Pi.single a (-(levTwoS2d_sigma n hn c c₀ a)) +
                     Pi.single b (-(levTwoS2d_sigma n hn c c₀ b))) := by
  obtain ⟨i, j, s, t, hij, hs, ht, hβc⟩ := (levTwoS2d_isRt_iff n (by omega) β).1 hβ
  have hne : (s : ZMod p) * levTwoS2d_d n hn c i + (t : ZMod p) * levTwoS2d_d n hn c j ≠ 0 := by
    intro hzero
    exact hβΦ ((levTwoS2d_mem_Phi_iff n hn hp2 c hΦ hij hs ht hβc).2 hzero)
  have hσi := levTwoS2d_sigma_spec n hn c (hd i)
  have hσj := levTwoS2d_sigma_spec n hn c (hd j)
  have hm_eq :
      ((s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j : ℤ) : ZMod p) * c₀ =
        (s : ZMod p) * levTwoS2d_d n hn c i + (t : ZMod p) * levTwoS2d_d n hn c j := by
    rw [← hσi, ← hσj]
    push_cast
    ring
  have hm0 :
      ((s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j : ℤ) : ZMod p) * c₀ ≠ 0 := by
    rw [hm_eq]
    exact hne
  have hmne :
      ((s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hm0 (by rw [h, zero_mul])
  have hm_int_ne : s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j ≠ 0 := by
    intro h
    exact hmne (by rw [h]; simp)
  have hm_abs :
      s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j = -2 ∨
      s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j = 0 ∨
      s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j = 2 := by
    rcases levTwoS2d_sigma_pm n hn c c₀ i with hi | hi <;>
      rcases levTwoS2d_sigma_pm n hn c c₀ j with hj | hj <;>
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp only [hi, hj] <;> norm_num
  have hm_pm :
      s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j = 2 ∨
      s * levTwoS2d_sigma n hn c c₀ i + t * levTwoS2d_sigma n hn c c₀ j = -2 := by
    rcases hm_abs with h | h | h
    · exact Or.inr h
    · exact absurd h hm_int_ne
    · exact Or.inl h
  have hsi_pm : s * levTwoS2d_sigma n hn c c₀ i = 1 ∨ s * levTwoS2d_sigma n hn c c₀ i = -1 :=
    levTwoS2e_mul_pm hs (levTwoS2d_sigma_pm n hn c c₀ i)
  have htj_pm : t * levTwoS2d_sigma n hn c c₀ j = 1 ∨ t * levTwoS2d_sigma n hn c c₀ j = -1 :=
    levTwoS2e_mul_pm ht (levTwoS2d_sigma_pm n hn c c₀ j)
  have hcase :
      (s = levTwoS2d_sigma n hn c c₀ i ∧ t = levTwoS2d_sigma n hn c c₀ j) ∨
      (s = -(levTwoS2d_sigma n hn c c₀ i) ∧ t = -(levTwoS2d_sigma n hn c c₀ j)) := by
    rcases hm_pm with hm2 | hm2
    · left
      have hA : s * levTwoS2d_sigma n hn c c₀ i = 1 := by
        rcases hsi_pm with h | h <;> rcases htj_pm with h' | h' <;> omega
      have hB : t * levTwoS2d_sigma n hn c c₀ j = 1 := by
        rcases hsi_pm with h | h <;> rcases htj_pm with h' | h' <;> omega
      exact ⟨levTwoS2e_eq_of_mul_pm hs (levTwoS2d_sigma_pm n hn c c₀ i) hA,
             levTwoS2e_eq_of_mul_pm ht (levTwoS2d_sigma_pm n hn c c₀ j) hB⟩
    · right
      have hA : s * levTwoS2d_sigma n hn c c₀ i = -1 := by
        rcases hsi_pm with h | h <;> rcases htj_pm with h' | h' <;> omega
      have hB : t * levTwoS2d_sigma n hn c c₀ j = -1 := by
        rcases hsi_pm with h | h <;> rcases htj_pm with h' | h' <;> omega
      exact ⟨levTwoS2e_eq_neg_of_mul_pm hs (levTwoS2d_sigma_pm n hn c c₀ i) hA,
             levTwoS2e_eq_neg_of_mul_pm ht (levTwoS2d_sigma_pm n hn c c₀ j) hB⟩
  rcases hcase with ⟨hsi, htj⟩ | ⟨hsi, htj⟩
  · exact ⟨i, j, hij, Or.inl (by rw [hβc, hsi, htj])⟩
  · exact ⟨i, j, hij, Or.inr (by rw [hβc, hsi, htj])⟩

theorem levTwoS2e_to_positive_pair {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p} (hc₀ : c₀ ≠ 0)
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {β : Fin n → ℤ} (hβ : IsRt (isFiniteType_cartanD n) β) (hβΦ : β ∉ Φ) :
    ∃ (a b : Fin n) (hab : a ≠ b),
      Cl (isFiniteType_cartanD n) (Φ ∪ {β})
        (levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ b)
          hab (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ b)) := by
  obtain ⟨a, b, hab, hsign⟩ := levTwoS2e_pair_of_outside n hn hp2 c hΦ hc₀ hd hβ hβΦ
  refine ⟨a, b, hab, ?_⟩
  rcases hsign with h | h
  · have hβeq : β = levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a)
        (levTwoS2d_sigma n hn c c₀ b) hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2d_sigma_pm n hn c c₀ b) :=
      levTwoS2d_eq_ofCoord n hn hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2d_sigma_pm n hn c c₀ b) h
    rw [hβeq]
    exact Cl.base (Or.inr rfl)
  · have hβeq : β = levTwoS2d_ofCoord n a b (-(levTwoS2d_sigma n hn c c₀ a))
        (-(levTwoS2d_sigma n hn c c₀ b)) hab (levTwoS2e_neg_sigma_pm n hn c c₀ a)
        (levTwoS2e_neg_sigma_pm n hn c c₀ b) :=
      levTwoS2d_eq_ofCoord n hn hab _ _ h
    have hβneg : β = - levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a)
        (levTwoS2d_sigma n hn c c₀ b) hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2d_sigma_pm n hn c c₀ b) := by
      rw [hβeq]
      exact (levTwoS2d_neg_ofCoord n hn hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2d_sigma_pm n hn c c₀ b)).symm
    have hβmem : β ∈ Φ ∪ {β} := Or.inr rfl
    have hβcl : Cl (isFiniteType_cartanD n) (Φ ∪ {β}) β := Cl.base hβmem
    have hcl := levTwoS2d_neg_mem_Cl n hn hβ hβcl
    rwa [show -β = levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a)
        (levTwoS2d_sigma n hn c c₀ b) hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2d_sigma_pm n hn c c₀ b) from by rw [hβneg, neg_neg]] at hcl

theorem levTwoS2e_cl_outside_case3 {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p} (hc₀ : c₀ ≠ 0)
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {β γ : Fin n → ℤ} (hβ : IsRt (isFiniteType_cartanD n) β) (hγ : IsRt (isFiniteType_cartanD n) γ)
    (hβΦ : β ∉ Φ) (hγΦ : γ ∉ Φ) :
    Cl (isFiniteType_cartanD n) (Φ ∪ {β}) γ := by
  obtain ⟨a, b, hab, hxa⟩ := levTwoS2e_to_positive_pair n hn hp2 c hΦ hc₀ hd hβ hβΦ
  obtain ⟨c', d', hcd, hsign⟩ := levTwoS2e_pair_of_outside n hn hp2 c hΦ hc₀ hd hγ hγΦ
  have hreach : Cl (isFiniteType_cartanD n) (Φ ∪ {β})
      (levTwoS2d_ofCoord n c' d' (levTwoS2d_sigma n hn c c₀ c')
        (levTwoS2d_sigma n hn c c₀ d') hcd
        (levTwoS2d_sigma_pm n hn c c₀ c') (levTwoS2d_sigma_pm n hn c c₀ d')) :=
    levTwoS2e_pair_reach n hn hp2 c hΦ hd (S := Φ ∪ {β})
      (by intro x hx; exact Or.inl hx) hab hxa c' d' hcd
  rcases hsign with h | h
  · have hγeq : γ = levTwoS2d_ofCoord n c' d' (levTwoS2d_sigma n hn c c₀ c')
        (levTwoS2d_sigma n hn c c₀ d') hcd
        (levTwoS2d_sigma_pm n hn c c₀ c') (levTwoS2d_sigma_pm n hn c c₀ d') :=
      levTwoS2d_eq_ofCoord n hn hcd _ _ h
    rw [hγeq]
    exact hreach
  · have hγeq : γ = levTwoS2d_ofCoord n c' d' (-(levTwoS2d_sigma n hn c c₀ c'))
        (-(levTwoS2d_sigma n hn c c₀ d')) hcd
        (levTwoS2e_neg_sigma_pm n hn c c₀ c') (levTwoS2e_neg_sigma_pm n hn c c₀ d') :=
      levTwoS2d_eq_ofCoord n hn hcd _ _ h
    have hγneg : γ = - levTwoS2d_ofCoord n c' d' (levTwoS2d_sigma n hn c c₀ c')
        (levTwoS2d_sigma n hn c c₀ d') hcd
        (levTwoS2d_sigma_pm n hn c c₀ c') (levTwoS2d_sigma_pm n hn c c₀ d') := by
      rw [hγeq]
      exact (levTwoS2d_neg_ofCoord n hn hcd (levTwoS2d_sigma_pm n hn c c₀ c')
        (levTwoS2d_sigma_pm n hn c c₀ d')).symm
    have hcl := levTwoS2d_neg_mem_Cl n hn
      (levTwoS2d_ofCoord_isRt n c' d' (levTwoS2d_sigma n hn c c₀ c')
        (levTwoS2d_sigma n hn c c₀ d') hcd
        (levTwoS2d_sigma_pm n hn c c₀ c') (levTwoS2d_sigma_pm n hn c c₀ d')) hreach
    rw [hγneg]
    exact hcl

end CFSG.StandardType.LevTwo
