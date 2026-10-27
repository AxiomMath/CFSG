module

public import CFSG.RepresentationTheory.SzMartineau.Devissage

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

@[expose] def Adm (a k j : ℕ) (r s t : Fin 4) : Prop :=
  (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szWt a r =
    szWt a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szWt a t

@[expose] def szRho (a : ℕ) : Fin 4 → ZMod (2 ^ (2 * a + 1) - 1) :=
  ![1, 2 ^ (a + 1) - 1, 1 - 2 ^ (a + 1), -1]

theorem szWt_eq_intCast_szWtInt (a : ℕ) (i : Fin 4) :
    szWt a i = ((szWtInt a i : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
  fin_cases i <;>
    simp [szWt, szWtInt, ← Int.natCast_pow] <;> push_cast <;> ring

private theorem two_pow_succ_sq (a : ℕ) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * 2 ^ (a + 1) = 2 := by
  rw [← pow_add]
  have h : a + 1 + (a + 1) = (2 * a + 1) + 1 := by omega
  rw [h]
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ ((2 * a + 1) + 1) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) * 2 := pow_succ _ _
  rw [h2, two_pow_self_eq_one, one_mul]

private theorem two_pow_mul_two_pow_succ (a : ℕ) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * 2 ^ (a + 1) = 1 := by
  rw [← pow_add]
  have h : a + (a + 1) = 2 * a + 1 := by omega
  rw [h, two_pow_self_eq_one]

private theorem one_add_two_pow_mul_two_pow_succ_sub_one (a : ℕ) :
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 ^ (a + 1) - 1) = 2 ^ a := by
  have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 ^ a * 2 := pow_succ _ _
  calc
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 ^ (a + 1) - 1)
        = 2 ^ (a + 1) - 1 + 2 ^ a * 2 ^ (a + 1) - 2 ^ a := by ring
    _ = 2 ^ (a + 1) - 1 + 1 - 2 ^ a := by rw [two_pow_mul_two_pow_succ]
    _ = 2 ^ a := by rw [hθ]; ring

private theorem one_add_two_pow_mul_two_sub_two_pow_succ (a : ℕ) :
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 - 2 ^ (a + 1)) = 1 := by
  have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 ^ a * 2 := pow_succ _ _
  calc
    (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * (2 - 2 ^ (a + 1))
        = 2 - 2 ^ (a + 1) + 2 ^ a * 2 - 2 ^ a * 2 ^ (a + 1) := by ring
    _ = 2 - 2 ^ (a + 1) + 2 ^ (a + 1) - 1 := by
          rw [← hθ, two_pow_mul_two_pow_succ]
    _ = 1 := by ring

private theorem isUnit_one_add_two_pow (a : ℕ) :
    IsUnit (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) :=
  isUnit_iff_exists_inv.mpr ⟨_, one_add_two_pow_mul_two_sub_two_pow_succ a⟩

private theorem isUnit_szWt_zero (a : ℕ) : IsUnit (szWt a 0) := by
  have h : szWt a 0 = 1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a := by simp [szWt]
  rw [h]
  exact isUnit_one_add_two_pow a

private theorem szWt_eq_zero_mul_szRho (a : ℕ) (i : Fin 4) :
    szWt a i = szWt a 0 * szRho a i := by
  fin_cases i
  · simp [szWt, szRho]
  · simpa [szWt, szRho] using (one_add_two_pow_mul_two_pow_succ_sub_one a).symm
  · have h := one_add_two_pow_mul_two_pow_succ_sub_one a
    simp [szWt, szRho]
    linear_combination h
  · simp [szWt, szRho]

theorem adm_iff_rho (a k j : ℕ) (r s t : Fin 4) :
    Adm a k j r s t ↔
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szRho a r =
        szRho a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szRho a t := by
  have hu := isUnit_szWt_zero a
  constructor
  · intro h
    rw [Adm] at h
    refine IsUnit.mul_left_cancel hu ?_
    calc
      szWt a 0 * ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szRho a r)
          = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * (szWt a 0 * szRho a r) := by ring
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szWt a r := by
            rw [← szWt_eq_zero_mul_szRho]
      _ = szWt a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szWt a t := h
      _ = szWt a 0 * szRho a s +
            (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * (szWt a 0 * szRho a t) := by
            rw [szWt_eq_zero_mul_szRho a s, szWt_eq_zero_mul_szRho a t]
      _ = szWt a 0 *
            (szRho a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szRho a t) := by ring
  · intro h
    rw [Adm]
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szWt a r
          = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * (szWt a 0 * szRho a r) := by
            rw [szWt_eq_zero_mul_szRho]
      _ = szWt a 0 * ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szRho a r) := by ring
      _ = szWt a 0 *
            (szRho a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szRho a t) := by rw [h]
      _ = szWt a 0 * szRho a s +
            (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * (szWt a 0 * szRho a t) := by ring
      _ = szWt a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szWt a t := by
            rw [szWt_eq_zero_mul_szRho a s, szWt_eq_zero_mul_szRho a t]

private theorem natCast_eq_zero_of_lt {n x : ℕ} (hx : x < n) (h : (x : ZMod n) = 0) : x = 0 := by
  have hdvd : n ∣ x := (ZMod.natCast_eq_zero_iff x n).mp h
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · exact h0
  · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

private theorem natCast_eq_of_lt {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at h'

private theorem two_pow_add_two_pow_lt_two_pow {a b c : ℕ} (ha : a < c) (hb : b < c)
    (hab : a ≠ b) : 2 ^ a + 2 ^ b < 2 ^ c := by
  have hc : 0 < c := by omega
  have htwo : 2 ^ (c - 1) + 2 ^ (c - 1) = 2 ^ c := by
    rw [← two_mul, mul_comm]
    rw [← pow_succ]
    congr 1
    omega
  have h1 : 2 ^ a ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases lt_or_gt_of_ne hab with h | h
  · have hlt : 2 ^ a < 2 ^ (c - 1) :=
      Nat.pow_lt_pow_iff_right (by norm_num) |>.mpr (by omega)
    rw [← htwo]
    omega
  · have hlt : 2 ^ b < 2 ^ (c - 1) :=
      Nat.pow_lt_pow_iff_right (by norm_num) |>.mpr (by omega)
    rw [← htwo]
    omega

private theorem sum_three_pow_lt {f a b c : ℕ} (hf : 4 ≤ f) (ha : a < f) (hb : b < f)
    (hc : c < f) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 ^ a + 2 ^ b + 2 ^ c < 2 ^ f - 1 := by
  obtain ⟨i, hi, hni⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset ℕ)) (t := Finset.range f) (by
      rw [Finset.card_range]
      have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton]
        · simpa using hbc
        · simp [hab, hac]
      omega)
  have hsub : ({a, b, c} : Finset ℕ) ⊆ Finset.range f := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simpa using ha
    · simpa using hb
    · simpa using hc
  have hlt := Finset.sum_lt_sum_of_subset hsub hi hni (Nat.two_pow_pos i)
    (fun j _ _ => Nat.zero_le (2 ^ j))
  have htotal : ∑ j ∈ Finset.range f, (2 : ℕ) ^ j = 2 ^ f - 1 := by
    rw [Nat.geomSum_eq (by norm_num)]
    simp
  have hsum : (∑ j ∈ ({a, b, c} : Finset ℕ), (2 : ℕ) ^ j) = 2 ^ a + 2 ^ b + 2 ^ c := by
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · ring
    · simpa using hbc
    · simp [hab, hac]
  rwa [hsum, htotal] at hlt

private lemma three_pow_add_ne_pow_of_lt {x y z d : ℕ} (hx : x < z) (hy : y < z)
    (hxy : x ≠ y) (h : 2 ^ x + 2 ^ y + 2 ^ z = 2 ^ d) : False := by
  have hlt : 2 ^ x + 2 ^ y < 2 ^ z := two_pow_add_two_pow_lt_two_pow hx hy hxy
  have hpos : 0 < 2 ^ x + 2 ^ y := by positivity
  have h1 : 2 ^ z < 2 ^ d := by
    rw [← h]
    omega
  have htwo : 2 ^ z + 2 ^ z = 2 ^ (z + 1) := by
    rw [← two_mul, mul_comm, ← pow_succ]
  have h2 : 2 ^ d < 2 ^ (z + 1) := by
    rw [← h, ← htwo]
    omega
  have h3 : z < d := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h4 : d < z + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

private theorem three_pow_add_ne_pow {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : 2 ^ a + 2 ^ b + 2 ^ c = 2 ^ d) : False := by
  by_cases hca : c < a
  · by_cases hba : b < a
    · have hperm : 2 ^ b + 2 ^ c + 2 ^ a = 2 ^ d := by rw [← h]; ring
      exact three_pow_add_ne_pow_of_lt (x := b) (y := c) (z := a) hba hca hbc hperm
    · have hab' : a < b := lt_of_le_of_ne (not_lt.mp hba) hab
      have hperm : 2 ^ c + 2 ^ a + 2 ^ b = 2 ^ d := by rw [← h]; ring
      exact three_pow_add_ne_pow_of_lt (x := c) (y := a) (z := b) (lt_trans hca hab') hab'
        (Ne.symm hac) hperm
  · have hac' : a < c := lt_of_le_of_ne (not_lt.mp hca) hac
    by_cases hbc' : b < c
    · exact three_pow_add_ne_pow_of_lt hac' hbc' hab h
    · have hcb : c < b := lt_of_le_of_ne (not_lt.mp hbc') (Ne.symm hbc)
      have hperm : 2 ^ a + 2 ^ c + 2 ^ b = 2 ^ d := by rw [← h]; ring
      exact three_pow_add_ne_pow_of_lt (x := a) (y := c) (z := b) (lt_trans hac' hcb) hcb hac
        hperm

private theorem sum_three_pow_eq_two_pow {f u v w x : ℕ} (hf : 4 ≤ f)
    (h : (2 : ZMod (2 ^ f - 1)) ^ u + 2 ^ v + 2 ^ w = 2 ^ x) :
    ((u : ZMod f) = v ∧ (w : ZMod f) = u + 1 ∧ (x : ZMod f) = u + 2) ∨
    ((u : ZMod f) = w ∧ (v : ZMod f) = u + 1 ∧ (x : ZMod f) = u + 2) ∨
    ((v : ZMod f) = w ∧ (u : ZMod f) = v + 1 ∧ (x : ZMod f) = v + 2) := by
  have hf2 : 2 ≤ f := by omega
  have hpow : (2 : ZMod (2 ^ f - 1)) ^ f = 1 := two_pow_self_eq_one f
  have hmerge : ∀ p q : ℕ, (p : ZMod f) = q →
      (2 : ZMod (2 ^ f - 1)) ^ p + 2 ^ q = 2 ^ (p + 1) := by
    intro p q hpq
    have hpq' : (2 : ZMod (2 ^ f - 1)) ^ p = 2 ^ q := by
      rw [two_pow_eq_two_pow_iff hf2]
      exact (ZMod.natCast_eq_natCast_iff' p q f).mp hpq
    rw [hpq', ← two_mul, ← hpq']
    rw [mul_comm, ← pow_succ]
  by_cases huv : (u : ZMod f) = v
  · left
    have h' : (2 : ZMod (2 ^ f - 1)) ^ (u + 1) + 2 ^ w = 2 ^ x := by
      rw [← hmerge u v huv]
      exact h
    obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := f) (u := u + 1) (v := w)
      (w := x) (by omega) h'
    refine ⟨huv, ?_, ?_⟩
    · have hz : ((w : ℕ) : ZMod f) = ((u + 1 : ℕ) : ZMod f) :=
        (ZMod.natCast_eq_natCast_iff' w (u + 1) f).mpr h1.symm
      push_cast at hz ⊢
      exact hz
    · have hz : ((x : ℕ) : ZMod f) = ((u + 1 + 1 : ℕ) : ZMod f) :=
        (ZMod.natCast_eq_natCast_iff' x (u + 1 + 1) f).mpr h2
      push_cast at hz ⊢
      linear_combination hz
  · by_cases huw : (u : ZMod f) = w
    · right; left
      have h' : (2 : ZMod (2 ^ f - 1)) ^ (u + 1) + 2 ^ v = 2 ^ x := by
        rw [← hmerge u w huw]
        linear_combination h
      obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := f) (u := u + 1) (v := v)
        (w := x) (by omega) h'
      refine ⟨huw, ?_, ?_⟩
      · have hz : ((v : ℕ) : ZMod f) = ((u + 1 : ℕ) : ZMod f) :=
          (ZMod.natCast_eq_natCast_iff' v (u + 1) f).mpr h1.symm
        push_cast at hz ⊢
        exact hz
      · have hz : ((x : ℕ) : ZMod f) = ((u + 1 + 1 : ℕ) : ZMod f) :=
          (ZMod.natCast_eq_natCast_iff' x (u + 1 + 1) f).mpr h2
        push_cast at hz ⊢
        linear_combination hz
    · by_cases hvw : (v : ZMod f) = w
      · right; right
        have h' : (2 : ZMod (2 ^ f - 1)) ^ (v + 1) + 2 ^ u = 2 ^ x := by
          rw [← hmerge v w hvw]
          linear_combination h
        obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := f) (u := v + 1) (v := u)
          (w := x) (by omega) h'
        refine ⟨hvw, ?_, ?_⟩
        · have hz : ((u : ℕ) : ZMod f) = ((v + 1 : ℕ) : ZMod f) :=
            (ZMod.natCast_eq_natCast_iff' u (v + 1) f).mpr h1.symm
          push_cast at hz ⊢
          exact hz
        · have hz : ((x : ℕ) : ZMod f) = ((v + 1 + 1 : ℕ) : ZMod f) :=
            (ZMod.natCast_eq_natCast_iff' x (v + 1 + 1) f).mpr h2
          push_cast at hz ⊢
          linear_combination hz
      · exfalso
        have hne : ∀ p q : ℕ, (p : ZMod f) ≠ q → p % f ≠ q % f := by
          intro p q hpq hpq'
          exact hpq ((ZMod.natCast_eq_natCast_iff' p q f).mpr hpq')
        have h1 : u % f ≠ v % f := hne u v huv
        have h2 : u % f ≠ w % f := hne u w huw
        have h3 : v % f ≠ w % f := hne v w hvw
        rw [pow_eq_pow_mod u hpow, pow_eq_pow_mod v hpow, pow_eq_pow_mod w hpow,
          pow_eq_pow_mod x hpow] at h
        have hu : u % f < f := Nat.mod_lt _ (by omega)
        have hv : v % f < f := Nat.mod_lt _ (by omega)
        have hw : w % f < f := Nat.mod_lt _ (by omega)
        have hx : x % f < f := Nat.mod_lt _ (by omega)
        have hSlt : 2 ^ (u % f) + 2 ^ (v % f) + 2 ^ (w % f) < 2 ^ f - 1 :=
          sum_three_pow_lt (by omega) hu hv hw h1 h2 h3
        have hXlt : 2 ^ (x % f) < 2 ^ f - 1 := by
          have hle : 2 ^ (x % f) ≤ 2 ^ (f - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have : 2 ^ (f - 1) < 2 ^ f - 1 := by
            have h2f : 2 ^ f = 2 ^ (f - 1) * 2 := by
              rw [← pow_succ]; congr 1; omega
            rw [h2f]
            have h2 : 2 ^ (f - 1) * 2 = 2 ^ (f - 1) + 2 ^ (f - 1) := by
              rw [mul_comm, two_mul]
            rw [h2]
            have h1 : 1 < 2 ^ (f - 1) := Nat.one_lt_two_pow (by omega)
            omega
          exact lt_of_le_of_lt hle this
        have hnat : 2 ^ (u % f) + 2 ^ (v % f) + 2 ^ (w % f) = 2 ^ (x % f) := by
          have hcast : (((2 ^ (u % f) + 2 ^ (v % f) + 2 ^ (w % f) : ℕ)) :
              ZMod (2 ^ f - 1)) = (((2 ^ (x % f) : ℕ)) : ZMod (2 ^ f - 1)) := by
            push_cast
            exact h
          have hval := congrArg ZMod.val hcast
          rwa [ZMod.val_natCast_of_lt hSlt, ZMod.val_natCast_of_lt hXlt] at hval
        exact three_pow_add_ne_pow h1 h2 h3 hnat

private theorem natCast_eq_of_pos_lt_two_mul {n y : ℕ} (hn : 0 < n) (hy0 : 0 < y)
    (hy : y < 2 * n) (h : (y : ZMod n) = 0) : y = n := by
  have hdvd : n ∣ y := (ZMod.natCast_eq_zero_iff y n).mp h
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  have hk2 : k < 2 := by
    rw [hk] at hy
    rw [mul_comm (2 : ℕ) n] at hy
    exact (Nat.mul_lt_mul_left hn).mp hy
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

theorem adm_row_zero_of_three_le {a k j : ℕ} (ha : 3 ≤ a) (hkB : k < 2 * a + 1)
    (hjB : j < 2 * a + 1) {s t : Fin 4} (h : Adm a k j 0 s t) :
    (k = 0 ∧ j = 1 ∧ s = 0 ∧ t = 0) ∨
    (k = 0 ∧ j = a + 1 ∧ ((s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))) ∨
    (k = 1 ∧ j = 0 ∧ s = 3 ∧ t = 0) ∨
    (k = a ∧ j = a ∧ ((s = 0 ∧ t = 2) ∨ (s = 1 ∧ t = 1))) ∨
    (k = a + 1 ∧ j = 0 ∧ ((s = 1 ∧ t = 1) ∨ (s = 2 ∧ t = 0))) ∨
    (k = 2 * a ∧ j = 2 * a ∧ s = 0 ∧ t = 3) := by
  have hn : 0 < 2 * a + 1 := by omega
  have h2n : 1 < 2 * a + 1 := by omega
  fin_cases s <;> fin_cases t <;>
    simp [adm_iff_rho, szRho] at h
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 + 2 ^ k = 2 ^ j := by
      rw [pow_zero]
      exact h.symm
    obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := 2 * a + 1) (u := 0) (v := k)
      (w := j) (by omega) h'
    have hk0 : k = 0 := by
      refine natCast_eq_zero_of_lt hkB ?_
      have := (ZMod.natCast_eq_natCast_iff' k 0 (2 * a + 1)).mpr h1.symm
      simpa using this
    have hj1 : j = 1 := by
      have hz : (j : ZMod (2 * a + 1)) = ((0 + 1 : ℕ) : ZMod (2 * a + 1)) :=
        (ZMod.natCast_eq_natCast_iff' j (0 + 1) (2 * a + 1)).mpr h2
      have := natCast_eq_of_lt hjB (by omega) hz
      omega
    simp [hk0, hj1]
  ·
    have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (k + a + 1) = 2 ^ k * 2 ^ (a + 1) := by
      rw [show k + a + 1 = k + (a + 1) by omega]
      exact pow_add _ _ _
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ k = 1 + 2 ^ (k + a + 1) := by
      rw [hθ]
      linear_combination h
    rcases two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) (u := j) (v := k)
      (x := 0) (y := k + a + 1) (by omega) (by simpa using h') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have hk' : (k : ZMod (2 * a + 1)) = ((k + a + 1 : ℕ) : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' k (k + a + 1) (2 * a + 1)).mpr h2
        push_cast at hk' ⊢
        linear_combination -hk'
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
    · have hk0 : k = 0 := by
        refine natCast_eq_zero_of_lt hkB ?_
        have := (ZMod.natCast_eq_natCast_iff' k 0 (2 * a + 1)).mpr h2
        simpa using this
      subst hk0
      have hj1 : j = a + 1 := by
        have hz : (j : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) := by
          have := (ZMod.natCast_eq_natCast_iff' j (0 + a + 1) (2 * a + 1)).mpr h1
          simpa only [Nat.zero_add] using this
        exact natCast_eq_of_lt hjB (by omega) hz
      simp [hj1]
  ·
    have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (k + a + 1) = 2 ^ k * 2 ^ (a + 1) := by
      rw [show k + a + 1 = k + (a + 1) by omega]
      exact pow_add _ _ _
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ (k + a + 1) = 1 + 2 ^ k := by
      rw [hθ]
      linear_combination h
    rcases two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) (u := j)
      (v := k + a + 1) (x := 0) (y := k) (by omega) (by simpa using h') with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have hk' : ((k + a + 1 : ℕ) : ZMod (2 * a + 1)) = (k : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' (k + a + 1) k (2 * a + 1)).mpr h2
        push_cast at hk' ⊢
        linear_combination hk'
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
    · have hk' : ((k + a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have := (ZMod.natCast_eq_natCast_iff' (k + a + 1) 0 (2 * a + 1)).mpr h2
        simpa using this
      have hkn : k + a + 1 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hk'
      have hka : k = a := by omega
      have hja : j = a := by
        have hz : (j : ZMod (2 * a + 1)) = (k : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' j k (2 * a + 1)).mpr h1
        have := natCast_eq_of_lt hjB hkB hz
        omega
      simp [hka, hja]
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ k = 2 ^ 0 := by
      rw [pow_zero]
      linear_combination h
    obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := k)
      (w := 0) (by omega) h'
    have hjn : j + 1 = 2 * a + 1 := by
      have hz : ((j + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have := (ZMod.natCast_eq_natCast_iff' (j + 1) 0 (2 * a + 1)).mpr h2.symm
        simpa using this
      exact natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
    have hjeq : j = 2 * a := by omega
    have hkeq : k = 2 * a := by
      have hz : (k : ZMod (2 * a + 1)) = (j : ZMod (2 * a + 1)) :=
        (ZMod.natCast_eq_natCast_iff' k j (2 * a + 1)).mpr h1.symm
      have := natCast_eq_of_lt hkB hjB hz
      omega
    simp [hjeq, hkeq]
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 = 2 ^ (a + 1) + 2 ^ k := by
      rw [pow_zero]
      linear_combination h
    rcases two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) (u := j) (v := 0)
      (x := a + 1) (y := k) (by omega) (by simpa using h') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hk0 : k = 0 := by
        refine natCast_eq_zero_of_lt hkB ?_
        have := (ZMod.natCast_eq_natCast_iff' k 0 (2 * a + 1)).mpr h2.symm
        simpa using this
      have hja : j = a + 1 := by
        have hz : (j : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' j (a + 1) (2 * a + 1)).mpr h1
        exact natCast_eq_of_lt hjB (by omega) hz
      simp [hk0, hja]
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have h0 : ((0 : ℕ) : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' 0 (a + 1) (2 * a + 1)).mpr h2
        simpa using h0.symm
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
  ·
    have hunit : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (2 ^ (a + 1) - 1) = 1 := by
      have hsq := two_pow_succ_sq (a := a)
      linear_combination hsq
    have hjθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j =
        (1 + 2 ^ (a + 1)) * 2 ^ j := by
      rw [show j + a + 1 = j + (a + 1) by omega]
      rw [pow_add]
      ring
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j = 1 + 2 ^ k := by
      calc (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j
          = (1 + 2 ^ (a + 1)) * 2 ^ j := hjθ
        _ = (1 + 2 ^ (a + 1)) *
              ((2 ^ (a + 1) - 1) + 2 ^ k * (2 ^ (a + 1) - 1)) := by rw [h]
        _ = (1 + 2 ^ (a + 1)) * (2 ^ (a + 1) - 1) +
              2 ^ k * ((1 + 2 ^ (a + 1)) * (2 ^ (a + 1) - 1)) := by ring
        _ = 1 + 2 ^ k := by rw [hunit]; ring
    rcases two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) (u := j + a + 1)
      (v := j) (x := 0) (y := k) (by omega) (by simpa using h') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hjn : j + a + 1 = 2 * a + 1 := by
        have hz : ((j + a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
          have := (ZMod.natCast_eq_natCast_iff' (j + a + 1) 0 (2 * a + 1)).mpr h1
          simpa using this
        exact natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
      have hja : j = a := by omega
      have hka : k = a := by
        have hz : (k : ZMod (2 * a + 1)) = (j : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' k j (2 * a + 1)).mpr h2.symm
        have := natCast_eq_of_lt hkB hjB hz
        omega
      simp [hja, hka]
    · have hj0 : j = 0 := by
        refine natCast_eq_zero_of_lt hjB ?_
        have := (ZMod.natCast_eq_natCast_iff' j 0 (2 * a + 1)).mpr h2
        simpa using this
      subst hj0
      have hka : k = a + 1 := by
        have hz : (k : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) := by
          have := (ZMod.natCast_eq_natCast_iff' k (0 + a + 1) (2 * a + 1)).mpr h1.symm
          simpa only [Nat.zero_add] using this
        exact natCast_eq_of_lt hkB (by omega) hz
      simp [hka]
  ·
    have hunit : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (2 ^ (a + 1) - 1) = 1 := by
      have hsq := two_pow_succ_sq (a := a)
      linear_combination hsq
    have hunit' : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (1 - 2 ^ (a + 1)) = -1 := by
      linear_combination -hunit
    have hjθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j =
        (1 + 2 ^ (a + 1)) * 2 ^ j := by
      rw [show j + a + 1 = j + (a + 1) by omega]
      rw [pow_add]
      ring
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 2 ^ k =
        2 ^ 0 := by
      rw [pow_zero]
      calc (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 2 ^ k
          = (1 + 2 ^ (a + 1)) * 2 ^ j + 2 ^ k := by rw [hjθ]
        _ = (1 + 2 ^ (a + 1)) *
              ((2 ^ (a + 1) - 1) + 2 ^ k * (1 - 2 ^ (a + 1))) + 2 ^ k := by rw [h]
        _ = (1 + 2 ^ (a + 1)) * (2 ^ (a + 1) - 1) +
              2 ^ k * ((1 + 2 ^ (a + 1)) * (1 - 2 ^ (a + 1))) + 2 ^ k := by ring
        _ = 1 + 2 ^ k * (-1) + 2 ^ k := by rw [hunit, hunit']
        _ = 1 := by ring
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j + a + 1) (v := j) (w := k)
      (x := 0) (by omega) h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h1 ⊢
        linear_combination h1
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
    · have hc : ((a + 2 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h2 ⊢
        linear_combination -h2
      have := natCast_eq_zero_of_lt (by omega : a + 2 < 2 * a + 1) hc
      omega
    · have hc : ((a : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h2 ⊢
        linear_combination h2
      have := natCast_eq_zero_of_lt (by omega : a < 2 * a + 1) hc
      omega
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 + 2 ^ k = 2 ^ (a + 1) := by
      rw [pow_zero]
      linear_combination h
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := 0) (w := k)
      (x := a + 1) (by omega) (by simpa using h') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · have hj0 : j = 0 := by
        refine natCast_eq_zero_of_lt hjB ?_
        simpa using h1
      subst hj0
      have h3' : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = ((2 : ℕ) : ZMod (2 * a + 1)) := by
        simpa using h3
      have := natCast_eq_of_lt (by omega : a + 1 < 2 * a + 1) (by omega : 2 < 2 * a + 1) h3'
      omega
    · have hz : ((j : ℕ) : ZMod (2 * a + 1)) = -1 := by
        push_cast at h2 ⊢
        linear_combination -h2
      have h3' : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 1 := by
        push_cast at h3 ⊢
        linear_combination h3 + hz
      have := natCast_eq_of_lt (by omega : a + 1 < 2 * a + 1) (by omega : 1 < 2 * a + 1) h3'
      omega
    · have h3' : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = ((2 : ℕ) : ZMod (2 * a + 1)) := by
        simpa using h3
      have := natCast_eq_of_lt (by omega : a + 1 < 2 * a + 1) (by omega : 2 < 2 * a + 1) h3'
      omega
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ (a + 1) = 2 ^ 0 + 2 ^ k := by
      rw [pow_zero]
      linear_combination h
    rcases two_pow_add_two_pow_eq_two_pow_add_two_pow (f := 2 * a + 1) (u := j) (v := a + 1)
      (x := 0) (y := k) (by omega) (by simpa using h') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hj0 : j = 0 := by
        refine natCast_eq_zero_of_lt hjB ?_
        have := (ZMod.natCast_eq_natCast_iff' j 0 (2 * a + 1)).mpr h1
        simpa using this
      have hka : k = a + 1 := by
        have hz : (k : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' k (a + 1) (2 * a + 1)).mpr h2.symm
        exact natCast_eq_of_lt hkB (by omega) hz
      simp [hj0, hka]
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have h0 : ((0 : ℕ) : ZMod (2 * a + 1)) = ((a + 1 : ℕ) : ZMod (2 * a + 1)) :=
          (ZMod.natCast_eq_natCast_iff' 0 (a + 1) (2 * a + 1)).mpr h2.symm
        simpa using h0.symm
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
  ·
    have hunit : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (2 ^ (a + 1) - 1) = 1 := by
      have hsq := two_pow_succ_sq (a := a)
      linear_combination hsq
    have hunit' : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (1 - 2 ^ (a + 1)) = -1 := by
      linear_combination -hunit
    have hjθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j =
        (1 + 2 ^ (a + 1)) * 2 ^ j := by
      rw [show j + a + 1 = j + (a + 1) by omega]
      rw [pow_add]
      ring
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 2 ^ 0 = 2 ^ k := by
      rw [pow_zero]
      calc (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 1
          = (1 + 2 ^ (a + 1)) * 2 ^ j + 1 := by rw [hjθ]
        _ = (1 + 2 ^ (a + 1)) * ((1 - 2 ^ (a + 1)) + 2 ^ k * (2 ^ (a + 1) - 1)) + 1 := by
              rw [h]
        _ = (1 + 2 ^ (a + 1)) * (1 - 2 ^ (a + 1)) +
              2 ^ k * ((1 + 2 ^ (a + 1)) * (2 ^ (a + 1) - 1)) + 1 := by ring
        _ = -1 + 2 ^ k + 1 := by rw [hunit, hunit', mul_one]
        _ = 2 ^ k := by ring
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j + a + 1) (v := j) (w := 0)
      (x := k) (by omega) (by simpa using h') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · have hc : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h1 ⊢
        linear_combination h1
      have := natCast_eq_zero_of_lt (by omega : a + 1 < 2 * a + 1) hc
      omega
    · have hc : ((a + 2 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h2 ⊢
        linear_combination -h2
      have := natCast_eq_zero_of_lt (by omega : a + 2 < 2 * a + 1) hc
      omega
    · have hc : ((a : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h2 ⊢
        linear_combination h2
      have := natCast_eq_zero_of_lt (by omega : a < 2 * a + 1) hc
      omega
  ·
    have hunit : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (2 ^ (a + 1) - 1) = 1 := by
      have hsq := two_pow_succ_sq (a := a)
      linear_combination hsq
    have hunit' : (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1)) *
        (1 - 2 ^ (a + 1)) = -1 := by
      linear_combination -hunit
    have hjθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j =
        (1 + 2 ^ (a + 1)) * 2 ^ j := by
      rw [show j + a + 1 = j + (a + 1) by omega]
      rw [pow_add]
      ring
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 2 ^ 0 + 2 ^ k =
        0 := by
      rw [pow_zero]
      calc (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (j + a + 1) + 2 ^ j + 1 + 2 ^ k
          = (1 + 2 ^ (a + 1)) * 2 ^ j + 1 + 2 ^ k := by rw [hjθ]
        _ = (1 + 2 ^ (a + 1)) *
              ((1 - 2 ^ (a + 1)) + 2 ^ k * (1 - 2 ^ (a + 1))) + 1 + 2 ^ k := by rw [h]
        _ = (1 + 2 ^ (a + 1)) * (1 - 2 ^ (a + 1)) +
              2 ^ k * ((1 + 2 ^ (a + 1)) * (1 - 2 ^ (a + 1))) + 1 + 2 ^ k := by ring
        _ = -1 + 2 ^ k * (-1) + 1 + 2 ^ k := by rw [hunit']
        _ = 0 := by ring
    have hlist : (([j + a + 1, j, 0, k].map fun u =>
        (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ u)).sum = 0 := by
      simpa [List.sum_cons, add_assoc] using h'
    exact absurd hlist (sum_two_pow_ne_zero (l := [j + a + 1, j, 0, k]) (by simp)
      (by simp; omega))
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ (a + 1) + 2 ^ k = 2 ^ 0 := by
      rw [pow_zero]
      linear_combination h
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := a + 1) (w := k)
      (x := 0) (by omega) (by simpa using h') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · have hz : ((j + 2 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h3 ⊢
        linear_combination -h3
      have hjn : j + 2 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
      have hja : j = a + 1 := natCast_eq_of_lt hjB (by omega) h1
      omega
    · have hz : ((j + 2 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h3 ⊢
        linear_combination -h3
      have hjn : j + 2 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
      have hja : ((a : ℕ) : ZMod (2 * a + 1)) = (j : ZMod (2 * a + 1)) := by
        push_cast at h2 ⊢
        linear_combination h2
      have hjeq : j = 2 * a - 1 := by omega
      have hval : ((a : ℕ) : ZMod (2 * a + 1)) = ((2 * a - 1 : ℕ) : ZMod (2 * a + 1)) := by
        simpa [hjeq] using hja
      have : a = 2 * a - 1 :=
        natCast_eq_of_lt (by omega : a < 2 * a + 1) (by omega : 2 * a - 1 < 2 * a + 1) hval
      omega
    · have hz : ((a + 3 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        push_cast at h3 ⊢
        linear_combination -h3
      have := natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
      omega
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 = 2 ^ k := by
      rw [pow_zero]
      linear_combination h
    obtain ⟨h1, h2⟩ := two_pow_add_two_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := 0)
      (w := k) (by omega) (by simpa using h')
    have hj0 : j = 0 := by
      refine natCast_eq_zero_of_lt hjB ?_
      have := (ZMod.natCast_eq_natCast_iff' j 0 (2 * a + 1)).mpr h1
      simpa using this
    subst hj0
    have hk1 : k = 1 := by
      have hz : (k : ZMod (2 * a + 1)) = ((0 + 1 : ℕ) : ZMod (2 * a + 1)) :=
        (ZMod.natCast_eq_natCast_iff' k (0 + 1) (2 * a + 1)).mpr h2
      have := natCast_eq_of_lt hkB (by omega) hz
      omega
    simp [hk1]
  ·
    have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (k + a + 1) = 2 ^ k * 2 ^ (a + 1) := by
      rw [show k + a + 1 = k + (a + 1) by omega]
      exact pow_add _ _ _
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 + 2 ^ k = 2 ^ (k + a + 1) := by
      rw [pow_zero, hθ]
      linear_combination h
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := 0) (w := k)
      (x := k + a + 1) (by omega) (by simpa using h') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · have hj0 : j = 0 := by
        refine natCast_eq_zero_of_lt hjB ?_
        simpa using h1
      have hk1 : k = 1 := by
        have hz : (k : ZMod (2 * a + 1)) = ((j : ZMod (2 * a + 1)) + 1) := h2
        rw [hj0] at hz
        have := natCast_eq_of_lt hkB (by omega) (by simpa using hz)
        omega
      have h3' : ((a + 2 : ℕ) : ZMod (2 * a + 1)) = ((2 : ℕ) : ZMod (2 * a + 1)) := by
        rw [hj0, hk1, show 1 + a + 1 = a + 2 by omega] at h3
        simpa using h3
      have := natCast_eq_of_lt (by omega : a + 2 < 2 * a + 1) (by omega : 2 < 2 * a + 1) h3'
      omega
    · have hz2 : ((j + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have h0 : ((0 : ℕ) : ZMod (2 * a + 1)) = ((j : ZMod (2 * a + 1)) + 1) := h2
        push_cast at h0 ⊢
        linear_combination -h0
      have hjn : j + 1 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz2
      have hj : j = 2 * a := by omega
      have hk : k = 2 * a := by
        have := natCast_eq_of_lt hkB hjB h1.symm
        omega
      have h3' : ((a : ℕ) : ZMod (2 * a + 1)) = 1 := by
        rw [hj, hk] at h3
        push_cast at h3 ⊢
        linear_combination h3
      have := natCast_eq_of_lt (by omega : a < 2 * a + 1) (by omega : 1 < 2 * a + 1) h3'
      omega
    · have hk0 : k = 0 := by
        refine natCast_eq_zero_of_lt hkB ?_
        simpa using h1.symm
      have hk : ((a + 1 : ℕ) : ZMod (2 * a + 1)) = 2 := by
        rw [hk0] at h3
        simpa using h3
      have := natCast_eq_of_lt (by omega : a + 1 < 2 * a + 1) (by omega : 2 < 2 * a + 1) hk
      omega
  ·
    have hθ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (k + a + 1) = 2 ^ k * 2 ^ (a + 1) := by
      rw [show k + a + 1 = k + (a + 1) by omega]
      exact pow_add _ _ _
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 + 2 ^ (k + a + 1) = 2 ^ k := by
      rw [pow_zero, hθ]
      linear_combination h
    rcases sum_three_pow_eq_two_pow (f := 2 * a + 1) (u := j) (v := 0) (w := k + a + 1)
      (x := k) (by omega) (by simpa using h') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · have hj0 : j = 0 := by
        refine natCast_eq_zero_of_lt hjB ?_
        simpa using h1
      have hval : (k : ZMod (2 * a + 1)) = ((2 : ℕ) : ZMod (2 * a + 1)) := by
        rw [hj0] at h3
        simpa using h3
      have hk2 : k = 2 := natCast_eq_of_lt hkB (by omega : 2 < 2 * a + 1) hval
      have h2' : ((a + 3 : ℕ) : ZMod (2 * a + 1)) = 1 := by
        rw [hj0, hk2, show 2 + a + 1 = a + 3 by omega] at h2
        simpa using h2
      have := natCast_eq_of_lt (by omega : a + 3 < 2 * a + 1) (by omega : 1 < 2 * a + 1) h2'
      omega
    · have hz2 : ((j + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have h0 : ((0 : ℕ) : ZMod (2 * a + 1)) = ((j : ZMod (2 * a + 1)) + 1) := h2
        push_cast at h0 ⊢
        linear_combination -h0
      have hjn : j + 1 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz2
      have hj : j = 2 * a := by omega
      have htwo1 : ((2 * a + 2 : ℕ) : ZMod (2 * a + 1)) = 1 := by
        rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega]
        rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
      have hrhs : ((2 * a : ℕ) : ZMod (2 * a + 1)) + 2 = 1 := by
        have : ((2 * a : ℕ) : ZMod (2 * a + 1)) + 2 =
            ((2 * a + 2 : ℕ) : ZMod (2 * a + 1)) := by push_cast; ring
        rw [this, htwo1]
      rw [hj] at h3
      have hk1 : k = 1 := natCast_eq_of_lt hkB (by omega) (h3.trans hrhs)
      have hja : ((2 * a : ℕ) : ZMod (2 * a + 1)) = ((a + 2 : ℕ) : ZMod (2 * a + 1)) := by
        have := h1
        rw [hj, hk1, show 1 + a + 1 = a + 2 by omega] at this
        simpa using this
      have := natCast_eq_of_lt (by omega : 2 * a < 2 * a + 1) (by omega : a + 2 < 2 * a + 1)
        hja
      omega
    · have hz : ((k + a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := by
        have h0 : ((0 : ℕ) : ZMod (2 * a + 1)) = ((k + a + 1 : ℕ) : ZMod (2 * a + 1)) := h1
        push_cast at h0 ⊢
        linear_combination -h0
      have hkn : k + a + 1 = 2 * a + 1 :=
        natCast_eq_of_pos_lt_two_mul hn (by omega) (by omega) hz
      have hk2 : k = 2 := by
        exact natCast_eq_of_lt hkB (by omega) (by simpa using h3)
      omega
  ·
    have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j + 2 ^ 0 + 2 ^ k = 0 := by
      rw [pow_zero]
      linear_combination h
    have hlist : (([j, 0, k].map fun u =>
        (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ u)).sum = 0 := by
      simpa [List.sum_cons, add_assoc] using h'
    exact absurd hlist (sum_two_pow_ne_zero (l := [j, 0, k]) (by simp) (by simp; omega))

@[expose] def AdmTwist (a c₁ c₂ c₃ : ℕ) (r s t : Fin 4) : Prop :=
  (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₃ * szWt a r =
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ * szWt a s +
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₂ * szWt a t

theorem admTwist_iff_adm {a c₁ c₂ c₃ : ℕ} (ha : 1 ≤ a) (r s t : Fin 4) :
    AdmTwist a c₁ c₂ c₃ r s t ↔
      Adm a ((c₂ + 2 * a * c₁) % (2 * a + 1)) ((c₃ + 2 * a * c₁) % (2 * a + 1)) r s t := by
  set d : ℕ := 2 * a * c₁ with hd
  have hμ : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₁ = 1 := by
    rw [hd, ← pow_add]
    have h : 2 * a * c₁ + c₁ = (2 * a + 1) * c₁ := by ring
    rw [h, pow_mul, two_pow_self_eq_one, one_pow]
  have hj1 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ ((c₃ + d) % (2 * a + 1)) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₃ + d) :=
    (pow_eq_pow_mod (c₃ + d) (two_pow_self_eq_one (2 * a + 1))).symm
  have hk1 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ ((c₂ + d) % (2 * a + 1)) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₂ + d) :=
    (pow_eq_pow_mod (c₂ + d) (two_pow_self_eq_one (2 * a + 1))).symm
  have hj : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ ((c₃ + d) % (2 * a + 1)) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃) := by
    rw [hj1]
    congr 1
    omega
  have hk : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ ((c₂ + d) % (2 * a + 1)) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂) := by
    rw [hk1]
    congr 1
    omega
  have hpow3 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₃)) = 2 ^ c₃ := by
    rw [two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)]
    rw [show c₁ + (d + c₃) = c₃ + c₁ * (2 * a + 1) by rw [hd]; ring]
    rw [Nat.add_mul_mod_self_right]
  have hpow2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₂)) = 2 ^ c₂ := by
    rw [two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)]
    rw [show c₁ + (d + c₂) = c₂ + c₁ * (2 * a + 1) by rw [hd]; ring]
    rw [Nat.add_mul_mod_self_right]
  constructor
  · intro h
    rw [AdmTwist] at h
    rw [Adm, hj, hk]
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃) * szWt a r
          = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d *
              ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₃ * szWt a r) := by
            rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃) =
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₃ from pow_add _ _ _]
            ring
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d *
            ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ * szWt a s +
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₂ * szWt a t) := by rw [h]
      _ = ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₁) * szWt a s +
            ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₂) * szWt a t := by ring
      _ = szWt a s + ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₂) * szWt a t := by
            rw [hμ, one_mul]
      _ = szWt a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂) * szWt a t := by
            rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂) =
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ d * 2 ^ c₂ from pow_add _ _ _]
  · intro h
    rw [Adm] at h
    rw [AdmTwist]
    rw [hj, hk] at h
    calc
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₃ * szWt a r
          = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₃)) * szWt a r := by
            rw [hpow3]
      _ = ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃)) * szWt a r := by
            rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₃)) =
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
                (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃) from pow_add _ _ _]
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
            ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₃) * szWt a r) := by ring
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
            (szWt a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂) * szWt a t) := by
            rw [h]
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ * szWt a s +
            ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂)) * szWt a t := by ring
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ * szWt a s +
            (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₂)) * szWt a t := by
            rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (c₁ + (d + c₂)) =
              (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ *
                (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (d + c₂) from pow_add _ _ _]
      _ = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₁ * szWt a s +
            (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ c₂ * szWt a t := by
            rw [hpow2]

theorem two_mul_sq_two_pow (a : ℕ) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) * ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) ^ 2 = 1 := by
  rw [sq, ← pow_add, show a + a = 2 * a by omega]
  rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) * 2 ^ (2 * a) =
    2 ^ (2 * a) * 2 by ring]
  rw [← pow_succ]
  exact two_pow_self_eq_one (2 * a + 1)

theorem two_pow_succ_ne_zero {a : ℕ} (ha : 1 ≤ a) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) ≠ 0 := by
  have h := sum_two_pow_ne_zero (f := 2 * a + 1) (l := [a + 1]) (by simp)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using h

theorem two_pow_succ_ne_one {a : ℕ} (ha : 1 ≤ a) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) ≠ 1 := by
  intro h
  have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 := by
    rw [pow_zero]
    exact h
  have := (two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)).mp h'
  rw [Nat.mod_eq_of_lt (by omega : a + 1 < 2 * a + 1), Nat.zero_mod] at this
  omega

theorem two_pow_succ_ne_two {a : ℕ} (ha : 1 ≤ a) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) ≠ 2 := by
  intro h
  have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 1 := by
    rw [pow_one]
    exact h
  have := (two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)).mp h'
  rw [Nat.mod_eq_of_lt (by omega : a + 1 < 2 * a + 1),
    Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)] at this
  omega

theorem two_pow_succ_ne_four {a : ℕ} (ha : 3 ≤ a) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) ≠ 4 := by
  intro h
  have h' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 2 := by
    rw [show (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 2 = 4 by norm_num]
    exact h
  have := (two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)).mp h'
  rw [Nat.mod_eq_of_lt (by omega : a + 1 < 2 * a + 1),
    Nat.mod_eq_of_lt (by omega : 2 < 2 * a + 1)] at this
  omega

end CFSG.RepresentationTheory.SzMartineau
