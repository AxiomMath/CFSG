module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

@[expose] def FixesA {n : ℕ} (m : ℕ) (g : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ a : Fin n, a.val < m → g.mulVec (Pi.single a 1) = Pi.single a 1

private theorem zmod2_add_self_nsbla : ∀ x : ZMod 2, x + x = 0 := by decide

private theorem zmod2_unit_nsbla : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

private theorem fixesA_entry_nsbla {n m : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : FixesA m g) (i k : Fin n) (hk : k.val < m) :
    g i k = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i k := by
  have h := congrFun (hg k hk) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h

private theorem entry_zero_nsbla {n m : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : FixesA m g) (i c : Fin n) (hc : c.val < m) (hi : m ≤ i.val) : g i c = 0 := by
  have hne : i ≠ c := by
    intro e
    subst e
    omega
  have h := congrFun (hg c hc) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hne] using h

theorem fixesA_one {n : ℕ} (m : ℕ) : FixesA (n := n) m 1 := by
  intro a _
  exact Matrix.one_mulVec _

theorem fixesA_mul {n m : ℕ} {g₁ g₂ : Matrix (Fin n) (Fin n) (ZMod 2)} (h₁ : FixesA m g₁)
    (h₂ : FixesA m g₂) : FixesA m (g₁ * g₂) := by
  intro a ha
  rw [← Matrix.mulVec_mulVec, h₂ a ha, h₁ a ha]

theorem fixesA_inv {n m : ℕ} (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) :
    FixesA m ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  intro a ha
  have hinv : ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := Units.inv_mul g
  calc ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single a 1)
      = ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          ((g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single a 1)) := by
        rw [hg a ha]
    _ = (((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2))).mulVec (Pi.single a 1) := by
        rw [Matrix.mulVec_mulVec]
    _ = Pi.single a 1 := by rw [hinv, Matrix.one_mulVec]

theorem lowerBlock2_one {n m : ℕ} (h : n = m + 2) : lowerBlock2 h (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [lowerBlock2, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have hne : ¬ ((⟨m + a.val, by omega⟩ : Fin n) = ⟨m + b.val, by omega⟩) := by
      intro e
      apply hab
      apply Fin.ext
      have := congrArg Fin.val e
      dsimp only at this
      omega
    rw [if_neg hne, if_neg hab]

theorem lowerBlock2_mul {n m : ℕ} (h : n = m + 2) {g₁ g₂ : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h₁ : FixesA m g₁) (h₂ : FixesA m g₂) :
    lowerBlock2 h (g₁ * g₂) = lowerBlock2 h g₁ * lowerBlock2 h g₂ := by
  subst h
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [lowerBlock2, Matrix.mul_apply]
  rw [Fin.sum_univ_add]
  have hA : ∀ c : Fin m, g₁ ⟨m + a.val, by omega⟩ (Fin.castAdd 2 c) *
      g₂ (Fin.castAdd 2 c) ⟨m + b.val, by omega⟩ = 0 := by
    intro c
    have hz := entry_zero_nsbla h₁ (⟨m + a.val, by omega⟩ : Fin (m + 2)) (Fin.castAdd 2 c)
      (by simpa using c.isLt) (Nat.le_add_right _ _)
    rw [hz, zero_mul]
  rw [Finset.sum_eq_zero (fun c _ => hA c), zero_add]
  exact Finset.sum_congr rfl (fun k _ => rfl)

private theorem diag_one_nsbla {n m : ℕ} (hn : n = m + 1) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) (mm : Fin n) (hmm : mm.val = m) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) mm mm = 1 := by
  have hrow : ∀ k : Fin n, k ≠ mm → (g : Matrix (Fin n) (Fin n) (ZMod 2)) mm k = 0 := by
    intro k hk
    have hk' : k.val < m := by
      have h1 := k.isLt
      have h2 : k.val ≠ m := fun e => hk (Fin.ext (e.trans hmm.symm))
      omega
    rw [fixesA_entry_nsbla hg mm k hk', Matrix.one_apply,
      if_neg (show ¬ (mm = k) from fun e => hk e.symm)]
  have hsum : ∀ y : Fin n → ZMod 2,
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec y) mm =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) mm mm * y mm := by
    intro y
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single mm]
    · intro k _ hk
      rw [hrow k hk, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ mm) h'
  have hdn : (g : Matrix (Fin n) (Fin n) (ZMod 2)) mm mm ≠ 0 := by
    intro hd
    have hinv : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
      Units.mul_inv g
    have hy : (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Pi.single mm 1)) = Pi.single mm 1 := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have h2 := congrFun hy mm
    rw [hsum, hd, zero_mul, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  exact zmod2_unit_nsbla _ hdn

private theorem mul_self_eq_one_nsbla {n m : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : FixesA m M)
    (hblk : ∀ r j : Fin n, m ≤ r.val → m ≤ j.val →
      M r j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r j) :
    M * M = 1 := by
  have hcol : ∀ k : Fin n, k.val < m → ∀ i : Fin n,
      M i k = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i k :=
    fun k hk i => fixesA_entry_nsbla hM i k hk
  have hrowN : ∀ r : Fin n, m ≤ r.val → ∀ j : Fin n, (M - 1) r j = 0 := by
    intro r hr j
    rw [Matrix.sub_apply]
    by_cases hj : j.val < m
    · rw [hcol j hj r, sub_self]
    · rw [hblk r j hr (by omega), sub_self]
  have hNN : (M - 1) * (M - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < m
    · simp only [Matrix.sub_apply, hcol k hk i, sub_self, zero_mul]
    · rw [hrowN k (by omega) j, mul_zero]
  have hNadd : (M - 1) + (M - 1) = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact zmod2_add_self_nsbla _
  calc M * M = ((M - 1) + 1) * ((M - 1) + 1) := by rw [sub_add_cancel]
    _ = (M - 1) * (M - 1) + ((M - 1) + (M - 1)) + 1 := by noncomm_ring
    _ = 1 := by simp only [hNN, hNadd, zero_add]

theorem sq_eq_one_of_succ {n m : ℕ} (hn : n = m + 1) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  refine mul_self_eq_one_nsbla _ hg (fun r j hr hj => ?_)
  have hr' : r = ⟨m, by omega⟩ := Fin.ext (by have := r.isLt; dsimp only; omega)
  have hj' : j = ⟨m, by omega⟩ := Fin.ext (by have := j.isLt; dsimp only; omega)
  rw [hr', hj', Matrix.one_apply_eq]
  exact diag_one_nsbla hn g hg ⟨m, by omega⟩ rfl

private theorem one_block_entry_nsbla {n m : ℕ} (r j : Fin n) (hr : m ≤ r.val)
    (hj : m ≤ j.val) (hr2 : r.val - m < 2) (hj2 : j.val - m < 2) :
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨r.val - m, hr2⟩ ⟨j.val - m, hj2⟩ =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases hrj : r = j
  · subst hrj
    simp
  · have hv : r.val ≠ j.val := fun e => hrj (Fin.ext e)
    have hne : ¬ ((⟨r.val - m, hr2⟩ : Fin 2) = ⟨j.val - m, hj2⟩) := by
      intro e
      have := congrArg Fin.val e
      dsimp only at this
      omega
    rw [if_neg hne, if_neg hrj]

private theorem entry_of_lowerBlock2_one_nsbla {n m : ℕ} (h : n = m + 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hD : lowerBlock2 h M = 1) (r j : Fin n)
    (hr : m ≤ r.val) (hj : m ≤ j.val) :
    M r j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r j := by
  have hr2 : r.val - m < 2 := by have := r.isLt; omega
  have hj2 : j.val - m < 2 := by have := j.isLt; omega
  have er : (⟨m + (r.val - m), by omega⟩ : Fin n) = r := Fin.ext (by dsimp only; omega)
  have ej : (⟨m + (j.val - m), by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
  have e2 := congrFun (congrFun hD ⟨r.val - m, hr2⟩) ⟨j.val - m, hj2⟩
  have e1 : M r j = lowerBlock2 h M ⟨r.val - m, hr2⟩ ⟨j.val - m, hj2⟩ := by
    simp only [lowerBlock2]
    rw [er, ej]
  rw [e1, e2]
  exact one_block_entry_nsbla r j hr hj hr2 hj2

theorem sq_eq_one_of_lower_one {n m : ℕ} (h : n = m + 2) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hD : lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact mul_self_eq_one_nsbla _ hg
    (fun r j hr hj => entry_of_lowerBlock2_one_nsbla h _ hD r j hr hj)

theorem block_two_commute (D τ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hD : ∃ D' : Matrix (Fin 2) (Fin 2) (ZMod 2), D * D' = 1) (hc : D * τ = τ * D) :
    D * D = 1 := by
  obtain ⟨D', hDD'⟩ := hD
  have hdet : D 0 0 * D 1 1 - D 0 1 * D 1 0 = 1 := by
    have h := congrArg Matrix.det hDD'
    rw [Matrix.det_mul, Matrix.det_one] at h
    have h1 : D.det = 1 := (by decide : ∀ x y : ZMod 2, x * y = 1 → x = 1) _ _ h
    rw [Matrix.det_fin_two] at h1
    exact h1
  have hτ00 : τ 0 0 * τ 0 0 + τ 0 1 * τ 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hτ 0) 0
  have hτ01 : τ 0 0 * τ 0 1 + τ 0 1 * τ 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hτ 0) 1
  have hτ10 : τ 1 0 * τ 0 0 + τ 1 1 * τ 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hτ 1) 0
  have hτ11 : τ 1 0 * τ 0 1 + τ 1 1 * τ 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hτ 1) 1
  have hc00 : D 0 0 * τ 0 0 + D 0 1 * τ 1 0 = τ 0 0 * D 0 0 + τ 0 1 * D 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 0
  have hc01 : D 0 0 * τ 0 1 + D 0 1 * τ 1 1 = τ 0 0 * D 0 1 + τ 0 1 * D 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 1
  have hc10 : D 1 0 * τ 0 0 + D 1 1 * τ 1 0 = τ 1 0 * D 0 0 + τ 1 1 * D 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 0
  have hc11 : D 1 0 * τ 0 1 + D 1 1 * τ 1 1 = τ 1 0 * D 0 1 + τ 1 1 * D 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 1
  have hne : ¬ (τ 0 0 = 1 ∧ τ 0 1 = 0 ∧ τ 1 0 = 0 ∧ τ 1 1 = 1) := by
    rintro ⟨e1, e2, e3, e4⟩
    apply hτ1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4]
  have key : ∀ a b c d p q r s : ZMod 2, a * d - b * c = 1 → p * p + q * r = 1 →
      p * q + q * s = 0 → r * p + s * r = 0 → r * q + s * s = 1 →
      ¬ (p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1) →
      a * p + b * r = p * a + q * c → a * q + b * s = p * b + q * d →
      c * p + d * r = r * a + s * c → c * q + d * s = r * b + s * d →
      a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
    set_option synthInstance.maxSize 4096 in
    decide
  obtain ⟨k1, k2, k3, k4⟩ := key (D 0 0) (D 0 1) (D 1 0) (D 1 1) (τ 0 0) (τ 0 1) (τ 1 0) (τ 1 1)
    hdet hτ00 hτ01 hτ10 hτ11 hne hc00 hc01 hc10 hc11
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k1
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k2
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k3
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k4

theorem eq_one_of_sq_eq_one_of_odd {X : Type*} [Group X] (x : X) (h2 : x * x = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hodd
    have h3 := Nat.odd_iff.mp hodd
    exact absurd h3 (by decide)

end CFSG.Quasithin.H13.Ch4.NSB
