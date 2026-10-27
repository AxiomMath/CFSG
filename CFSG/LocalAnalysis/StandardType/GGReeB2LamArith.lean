module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SigmaOrder

public section

namespace CFSG.StandardType.ReeB2Fixed

private theorem two_pow_e_eq_one (e : ℕ) (he : Odd e) :
    (2 : ZMod (2 ^ e - 1)) ^ e = 1 := by
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hcast : ((2 ^ e : ℕ) : ZMod (2 ^ e - 1)) = 1 := by
    have hsplit : 2 ^ e = (2 ^ e - 1) + 1 := by omega
    rw [hsplit, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  rw [show (2 : ZMod (2 ^ e - 1)) = ((2 : ℕ) : ZMod (2 ^ e - 1)) by norm_num,
    ← Nat.cast_pow]
  exact hcast

private theorem r_sq_local (e : ℕ) (he : Odd e) : r e ^ 2 = 2 := by
  obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp he
  have h0 := two_pow_e_eq_one (2 * m + 1) he
  have h2h : (2 * m + 1 + 1) / 2 * 2 = 2 * m + 1 + 1 := by omega
  calc r (2 * m + 1) ^ 2
      = ((2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ ((2 * m + 1 + 1) / 2)) ^ 2 := by rfl
    _ = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ ((2 * m + 1 + 1) / 2 * 2) :=
          (pow_mul _ _ _).symm
    _ = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (2 * m + 1 + 1) := by rw [h2h]
    _ = 2 := by
          simp only [pow_succ, h0]
          ring

private theorem two_pow_succ_sigma (e : ℕ) (he : Odd e) (p : Fin e) :
    (2 : ZMod (2 ^ e - 1)) ^ ((succσ e p : Fin e) : ℕ)
      = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * r e := by
  have h0 := two_pow_e_eq_one e he
  have hval : ((succσ e p : Fin e) : ℕ) = ((p : ℕ) + (e + 1) / 2) % e := by
    simp only [succσ, Fin.val_mk]
  rw [hval]
  rw [show (2 : ZMod (2 ^ e - 1)) ^ (((p : ℕ) + (e + 1) / 2) % e)
        = (2 : ZMod (2 ^ e - 1)) ^ ((p : ℕ) + (e + 1) / 2) from
      (pow_eq_pow_mod ((p : ℕ) + (e + 1) / 2) h0).symm]
  rw [pow_add]
  rfl

private theorem succ_sigma_ne_self (e : ℕ) (he3 : 3 ≤ e) (p : Fin e) : succσ e p ≠ p := by
  intro h
  have hval : ((p : ℕ) + (e + 1) / 2) % e = (p : ℕ) := by
    have := congrArg Fin.val h
    simpa only [succσ, Fin.val_mk] using this
  have hme : (p : ℕ) + (e + 1) / 2 ≡ (p : ℕ) [MOD e] := by
    show ((p : ℕ) + (e + 1) / 2) % e = (p : ℕ) % e
    rw [hval, Nat.mod_eq_of_lt p.isLt]
  have hzero : (e + 1) / 2 ≡ 0 [MOD e] :=
    (Nat.ModEq.refl (p : ℕ)).add_left_cancel (by simpa using hme)
  have hlt : (e + 1) / 2 < e := by omega
  have hmod0 : ((e + 1) / 2) % e = 0 := by
    have h' := hzero
    change ((e + 1) / 2) % e = 0 % e at h'
    simpa using h'
  rw [Nat.mod_eq_of_lt hlt] at hmod0
  omega

private theorem two_mul_two_pow_div (e : ℕ) (he : Odd e) :
    2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) = r e := by
  obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp he
  have h1 : (2 * m + 1 - 1) / 2 = m := by omega
  have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h1]
  rw [show r (2 * m + 1)
      = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ ((2 * m + 1 + 1) / 2) from rfl]
  rw [h2]
  simp only [pow_succ']

private theorem units_add_mul (e : ℕ) (he : Odd e) {u : ZMod (2 ^ e - 1)} (hu : u ∈ units e) :
    ∃ x ∈ units e, ∃ y ∈ units e, u = x + r e * y := by
  have hr : r e ^ 2 = 2 := r_sq_local e he
  have hR : R e = r e - 1 := rfl
  have hRR : R e + r e * R e = 1 := by
    rw [hR]
    have h2 : (r e - 1) + r e * (r e - 1) = r e ^ 2 - 1 := by ring
    rw [h2, hr]; ring
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact ⟨R e, by simp [units], R e, by simp [units], hRR.symm⟩
  · refine ⟨-R e, by simp [units], -R e, by simp [units], ?_⟩
    show (-1 : ZMod (2 ^ e - 1)) = -R e + r e * (-R e)
    have h2 : -R e + r e * (-R e) = -(R e + r e * R e) := by ring
    rw [h2, hRR]
  · refine ⟨-1, by simp [units], 1, by simp [units], ?_⟩
    show R e = -1 + r e * 1
    rw [hR]; ring
  · refine ⟨1, by simp [units], -1, by simp [units], ?_⟩
    show -R e = 1 + r e * (-1)
    rw [hR]; ring

private def dset (e : ℕ) : Finset (ZMod (2 ^ e - 1)) :=
  {0, -1, 2 ^ ((e - 1) / 2) - 1, -2 ^ ((e - 1) / 2)}

private theorem units_eq_one_add_two_dset (e : ℕ) (he : Odd e) {u : ZMod (2 ^ e - 1)}
    (hu : u ∈ units e) : ∃ d ∈ dset e, u = 1 + 2 * d := by
  have hθ : 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) = r e := two_mul_two_pow_div e he
  have hR : R e = r e - 1 := rfl
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [dset], by ring⟩
  · exact ⟨-1, by simp [dset], by ring⟩
  · refine ⟨(2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1, by simp [dset], ?_⟩
    have h2 : (1 : ZMod (2 ^ e - 1))
        + 2 * ((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1)
        = 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1 := by ring
    rw [hR, h2, hθ]
  · refine ⟨-((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2)), by simp [dset], ?_⟩
    have h2 : (1 : ZMod (2 ^ e - 1))
        + 2 * (-((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2)))
        = 1 - 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) := by ring
    rw [hR, h2, hθ]; ring

private theorem one_add_two_mem_units (e : ℕ) (he : Odd e) {d : ZMod (2 ^ e - 1)}
    (hd : d ∈ dset e) : 1 + 2 * d ∈ units e := by
  have hθ : 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) = r e := two_mul_two_pow_div e he
  have hR : R e = r e - 1 := rfl
  simp only [dset, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · have h2 : (1 : ZMod (2 ^ e - 1)) + 2 * 0 = 1 := by ring
    rw [h2]; simp [units]
  · have h2 : (1 : ZMod (2 ^ e - 1)) + 2 * (-1) = -1 := by ring
    rw [h2]; simp [units]
  · have h2 : (1 : ZMod (2 ^ e - 1))
        + 2 * ((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1)
        = 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1 := by ring
    rw [h2, hθ, ← hR]; simp [units]
  · have h2 : (1 : ZMod (2 ^ e - 1))
        + 2 * (-((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2)))
        = 1 - 2 * (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) := by ring
    rw [h2, hθ]
    have h3 : (1 : ZMod (2 ^ e - 1)) - r e = -R e := by rw [hR]; ring
    rw [h3]; simp [units]

private theorem sum_erase_succ_eq (e : ℕ) (he : Odd e) (A : Finset (Fin e)) (p : Fin e)
    (hp : p ∈ A) (hq : succσ e p ∈ A) (hpq : p ≠ succσ e p)
    (c : Fin e → ZMod (2 ^ e - 1)) (x0 y0 : ZMod (2 ^ e - 1))
    (hxy : c p = x0 + r e * y0) :
    (∑ j ∈ A.erase (succσ e p), c j * 2 ^ (j : ℕ)) =
      ∑ j ∈ A,
        (if j = succσ e p then y0 else if j = p then x0 else c j) * 2 ^ (j : ℕ) := by
  have hp' : p ∈ A.erase (succσ e p) := Finset.mem_erase.mpr ⟨hpq, hp⟩
  have htail :
      (∑ j ∈ (A.erase (succσ e p)).erase p,
          (if j = succσ e p then y0 else if j = p then x0 else c j) * 2 ^ (j : ℕ))
        = ∑ j ∈ (A.erase (succσ e p)).erase p, c j * 2 ^ (j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_erase] at hj
    obtain ⟨hjp, hjq, _⟩ := hj
    rw [if_neg hjq, if_neg hjp]
  rw [← Finset.sum_erase_add (A.erase (succσ e p)) (fun j => c j * 2 ^ (j : ℕ)) hp']
  rw [← Finset.sum_erase_add A
        (fun j =>
          (if j = succσ e p then y0 else if j = p then x0 else c j) * 2 ^ (j : ℕ)) hq]
  rw [← Finset.sum_erase_add (A.erase (succσ e p))
        (fun j =>
          (if j = succσ e p then y0 else if j = p then x0 else c j) * 2 ^ (j : ℕ)) hp']
  rw [htail]
  have hgp : (if p = succσ e p then y0 else if p = p then x0 else c p) * 2 ^ (p : ℕ)
      = x0 * 2 ^ (p : ℕ) := by rw [if_neg hpq, if_pos rfl]
  have hgq : (if succσ e p = succσ e p then y0 else if succσ e p = p then x0 else c (succσ e p))
        * 2 ^ ((succσ e p : Fin e) : ℕ)
      = y0 * 2 ^ ((succσ e p : Fin e) : ℕ) := by rw [if_pos rfl]
  rw [hgp, hgq]
  have h2 : (2 : ZMod (2 ^ e - 1)) ^ ((succσ e p : Fin e) : ℕ)
      = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * r e := two_pow_succ_sigma e he p
  rw [h2, hxy]
  ring

theorem lam_erase_succ_subset (e : ℕ) (he : Odd e) (A : Finset (Fin e)) (p : Fin e) (hp : p ∈ A)
    (hq : succσ e p ∈ A) : Lam e (A.erase (succσ e p)) ⊆ Lam e A := by
  rcases e with _ | _ | e
  · obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp he
    omega
  · intro x hx
    haveI : Subsingleton (ZMod (2 ^ 1 - 1)) := by
      rw [show 2 ^ 1 - 1 = 1 by norm_num]
      infer_instance
    refine ⟨fun _ => 1, ?_, Subsingleton.elim _ _⟩
    intro j hj
    simp [units]
  · intro x hx
    simp only [Lam, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨c, hc, hxeq⟩ := hx
    have he3 : 3 ≤ e + 2 := by
      obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp he
      omega
    have hpq : p ≠ succσ (e + 2) p := (succ_sigma_ne_self (e + 2) he3 p).symm
    have hp' : p ∈ A.erase (succσ (e + 2) p) := Finset.mem_erase.mpr ⟨hpq, hp⟩
    obtain ⟨x0, hx0, y0, hy0, hxy⟩ := units_add_mul (e + 2) he (hc p hp')
    refine ⟨fun j => if j = succσ (e + 2) p then y0 else if j = p then x0 else c j, ?_, ?_⟩
    · intro j hj
      change (if j = succσ (e + 2) p then y0 else if j = p then x0 else c j) ∈ units (e + 2)
      by_cases hjq : j = succσ (e + 2) p
      · rw [if_pos hjq]; exact hy0
      · by_cases hjp : j = p
        · rw [if_neg hjq, if_pos hjp]; exact hx0
        · rw [if_neg hjq, if_neg hjp]
          exact hc j (Finset.mem_erase.mpr ⟨hjq, hj⟩)
    · rw [hxeq]
      exact sum_erase_succ_eq (e + 2) he A p hp hq hpq c x0 y0 hxy

theorem lam_eq_S_add_two_delta (e : ℕ) (he : Odd e) (J : Finset (Fin e)) :
    Lam e J = (fun d => S e J + 2 * d) '' Delta e J := by
  ext x
  constructor
  · simp only [Lam, Set.mem_setOf_eq]
    rintro ⟨c, hc, hxeq⟩
    have hchoose : ∀ j : Fin e,
        ∃ d : ZMod (2 ^ e - 1), j ∈ J → d ∈ dset e ∧ c j = 1 + 2 * d := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨d, hdmem, hdeq⟩ := units_eq_one_add_two_dset e he (hc j hj)
        exact ⟨d, fun _ => ⟨hdmem, hdeq⟩⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose d hd using hchoose
    simp only [Set.mem_image]
    refine ⟨∑ j ∈ J, d j * 2 ^ (j : ℕ), ?_, ?_⟩
    · simp only [Delta, Set.mem_setOf_eq]
      exact ⟨d, fun j hj => (hd j hj).1, rfl⟩
    · rw [hxeq]
      simp only [S]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(hd j hj).2]
      ring
  · simp only [Set.mem_image]
    rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    simp only [Lam, Set.mem_setOf_eq]
    simp only [Delta, Set.mem_setOf_eq] at hy
    obtain ⟨d, hd, hyeq⟩ := hy
    refine ⟨fun j => 1 + 2 * d j, ?_, ?_⟩
    · intro j hj
      exact one_add_two_mem_units e he (hd j hj)
    · rw [hyeq]
      simp only [S]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end CFSG.StandardType.ReeB2Fixed
