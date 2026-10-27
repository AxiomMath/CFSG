module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

private abbrev b3e (i : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1

private theorem b3_mulVec_mul (A B : G6) (v : Fin 6 → ZMod 2) :
    ((A * B : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ((B : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem b3_pow_fix (g : G6) (v : Fin 6 → ZMod 2)
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v) (n : ℕ) :
    ((g ^ n : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v := by
  induction n with
  | zero => rw [pow_zero, Units.val_one, Matrix.one_mulVec]
  | succ n ih => rw [pow_succ, b3_mulVec_mul, h, ih]

private theorem b3_mem_sig0_iff (g : G6) :
    g ∈ Sig0 ↔
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0 ∧
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 = b3e 2 ∧
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 5 = b3e 5 :=
  Iff.rfl

theorem u0_mem_sp0 : u0 ∈ Sp0 := by
  show (u0 : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
    (u0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0
  decide

theorem u2_mem_sig0 : u2 ∈ Sig0 :=
  (b3_mem_sig0_iff u2).2 ⟨by decide, by decide, by decide⟩

theorem u3_mem_sig0 : u3 ∈ Sig0 :=
  (b3_mem_sig0_iff u3).2 ⟨by decide, by decide, by decide⟩

theorem Sig0_le_sp0 : Sig0 ≤ Sp0 :=
  fun g hg => ((b3_mem_sig0_iff g).1 hg).1

theorem u0_pow_three : u0 ^ 3 = 1 := by
  rw [pow_three]
  apply Units.ext
  decide

theorem u2_pow_three : u2 ^ 3 = 1 := by
  rw [pow_three]
  apply Units.ext
  decide

theorem u3_pow_three : u3 ^ 3 = 1 := by
  rw [pow_three]
  apply Units.ext
  decide

theorem u0_comm_u2 : u0 * u2 = u2 * u0 := by
  apply Units.ext
  decide

theorem u0_comm_u3 : u0 * u3 = u3 * u0 := by
  apply Units.ext
  decide

theorem u2_comm_u3 : u2 * u3 = u3 * u2 := by
  apply Units.ext
  decide

private theorem b3_c02 : Commute u0 u2 := u0_comm_u2

private theorem b3_c03 : Commute u0 u3 := u0_comm_u3

private theorem b3_c23 : Commute u2 u3 := u2_comm_u3

private theorem b3_u0_ne_one : u0 ≠ 1 := by
  intro h
  have h' : (u0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := congrArg Units.val h
  revert h'
  decide

theorem orderOf_u0 : orderOf u0 = 3 :=
  orderOf_eq_prime u0_pow_three b3_u0_ne_one

private theorem b3_u0_fix0 : (u0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0 = b3e 0 := by
  decide

private theorem b3_u0_fix1 : (u0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1 = b3e 1 := by
  decide

private theorem b3_u2_fix1 : (u2 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1 = b3e 1 := by
  decide

private theorem b3_u2_fix2 : (u2 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 = b3e 2 := by
  decide

private theorem b3_u3_fix0 : (u3 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0 = b3e 0 := by
  decide

private theorem b3_u3_fix2 : (u3 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 = b3e 2 := by
  decide

private theorem b3_F_e2 (a b c : ℕ) :
    ((u0 ^ a * u2 ^ b * u3 ^ c : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 =
      ((u0 ^ a : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 := by
  rw [b3_mulVec_mul, b3_mulVec_mul, b3_pow_fix u3 _ b3_u3_fix2 c,
    b3_pow_fix u2 _ b3_u2_fix2 b]

private theorem b3_F_e0 (a b c : ℕ) :
    ((u0 ^ a * u2 ^ b * u3 ^ c : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0 =
      ((u2 ^ b : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0 := by
  rw [(b3_c02.pow_pow a b).eq, b3_mulVec_mul, b3_mulVec_mul, b3_pow_fix u3 _ b3_u3_fix0 c,
    b3_pow_fix u0 _ b3_u0_fix0 a]

private theorem b3_F_e1 (a b c : ℕ) :
    ((u0 ^ a * u2 ^ b * u3 ^ c : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1 =
      ((u3 ^ c : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1 := by
  have hc : u3 ^ c * (u0 ^ a * u2 ^ b) = u0 ^ a * u2 ^ b * u3 ^ c :=
    (Commute.mul_right (b3_c03.pow_pow a c).symm (b3_c23.pow_pow b c).symm).eq
  rw [← hc, b3_mulVec_mul, b3_mulVec_mul, b3_pow_fix u2 _ b3_u2_fix1 b,
    b3_pow_fix u0 _ b3_u0_fix1 a]

private theorem b3_u0pow_inj {a a' : ℕ} (ha : a < 3) (ha' : a' < 3)
    (h : ((u0 ^ a : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 =
      ((u0 ^ a' : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2) : a = a' := by
  interval_cases a <;> interval_cases a' <;> first | rfl | exact absurd h (by decide)

private theorem b3_u2pow_inj {b b' : ℕ} (hb : b < 3) (hb' : b' < 3)
    (h : ((u2 ^ b : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0 =
      ((u2 ^ b' : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0) : b = b' := by
  interval_cases b <;> interval_cases b' <;> first | rfl | exact absurd h (by decide)

private theorem b3_u3pow_inj {c c' : ℕ} (hc : c < 3) (hc' : c' < 3)
    (h : ((u3 ^ c : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1 =
      ((u3 ^ c' : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1) : c = c' := by
  interval_cases c <;> interval_cases c' <;> first | rfl | exact absurd h (by decide)

private theorem b3_inj (a b c a' b' c' : Fin 3)
    (h : u0 ^ (a : ℕ) * u2 ^ (b : ℕ) * u3 ^ (c : ℕ) =
      u0 ^ (a' : ℕ) * u2 ^ (b' : ℕ) * u3 ^ (c' : ℕ)) :
    a = a' ∧ b = b' ∧ c = c' := by
  have e2 := congrArg (fun g : G6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2) h
  have e0 := congrArg (fun g : G6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 0) h
  have e1 := congrArg (fun g : G6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 1) h
  rw [b3_F_e2, b3_F_e2] at e2
  rw [b3_F_e0, b3_F_e0] at e0
  rw [b3_F_e1, b3_F_e1] at e1
  exact ⟨Fin.ext (b3_u0pow_inj a.isLt a'.isLt e2), Fin.ext (b3_u2pow_inj b.isLt b'.isLt e0),
    Fin.ext (b3_u3pow_inj c.isLt c'.isLt e1)⟩

private theorem b3_mul_form (a b c a' b' c' : ℕ) :
    u0 ^ a * u2 ^ b * u3 ^ c * (u0 ^ a' * u2 ^ b' * u3 ^ c') =
      u0 ^ (a + a') * u2 ^ (b + b') * u3 ^ (c + c') := by
  have hA : u0 ^ a' * (u2 ^ b * u3 ^ c) = u2 ^ b * u3 ^ c * u0 ^ a' :=
    (Commute.mul_right (b3_c02.pow_pow a' b) (b3_c03.pow_pow a' c)).eq
  have hB : u3 ^ c * u2 ^ b' = u2 ^ b' * u3 ^ c := (b3_c23.pow_pow b' c).eq.symm
  calc u0 ^ a * u2 ^ b * u3 ^ c * (u0 ^ a' * u2 ^ b' * u3 ^ c')
      = u0 ^ a * (u2 ^ b * u3 ^ c * u0 ^ a') * (u2 ^ b' * u3 ^ c') := by
        simp only [mul_assoc]
    _ = u0 ^ a * (u0 ^ a' * (u2 ^ b * u3 ^ c)) * (u2 ^ b' * u3 ^ c') := by
        rw [hA]
    _ = u0 ^ a * u0 ^ a' * (u2 ^ b * (u3 ^ c * u2 ^ b')) * u3 ^ c' := by
        simp only [mul_assoc]
    _ = u0 ^ a * u0 ^ a' * (u2 ^ b * (u2 ^ b' * u3 ^ c)) * u3 ^ c' := by
        rw [hB]
    _ = u0 ^ (a + a') * u2 ^ (b + b') * u3 ^ (c + c') := by
        rw [pow_add, pow_add, pow_add]
        simp only [mul_assoc]

private theorem b3_inv_form (a b c : ℕ) :
    (u0 ^ a * u2 ^ b * u3 ^ c)⁻¹ = u0 ^ (2 * a) * u2 ^ (2 * b) * u3 ^ (2 * c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [b3_mul_form]
  have e0 : u0 ^ (a + 2 * a) = 1 := by
    rw [show a + 2 * a = 3 * a by ring, pow_mul, u0_pow_three, one_pow]
  have e2 : u2 ^ (b + 2 * b) = 1 := by
    rw [show b + 2 * b = 3 * b by ring, pow_mul, u2_pow_three, one_pow]
  have e3 : u3 ^ (c + 2 * c) = 1 := by
    rw [show c + 2 * c = 3 * c by ring, pow_mul, u3_pow_three, one_pow]
  rw [e0, e2, e3, one_mul, one_mul]

private def b3_sub : Subgroup G6 where
  carrier := {g | ∃ a b c : ℕ, g = u0 ^ a * u2 ^ b * u3 ^ c}
  one_mem' := ⟨0, 0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', b3_mul_form a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨2 * a, 2 * b, 2 * c, b3_inv_form a b c⟩

private theorem b3_mem_sub_iff (g : G6) :
    g ∈ b3_sub ↔ ∃ a b c : ℕ, g = u0 ^ a * u2 ^ b * u3 ^ c :=
  Iff.rfl

private theorem b3_pow_mod0 (a : ℕ) : u0 ^ (a % 3) = u0 ^ a :=
  (pow_eq_pow_mod a u0_pow_three).symm

private theorem b3_pow_mod2 (a : ℕ) : u2 ^ (a % 3) = u2 ^ a :=
  (pow_eq_pow_mod a u2_pow_three).symm

private theorem b3_pow_mod3 (a : ℕ) : u3 ^ (a % 3) = u3 ^ a :=
  (pow_eq_pow_mod a u3_pow_three).symm

theorem mem_B3_iff {g : G6} :
    g ∈ B3 ↔ ∃ a b c : Fin 3, g = u0 ^ (a : ℕ) * u2 ^ (b : ℕ) * u3 ^ (c : ℕ) := by
  have hle : B3 ≤ b3_sub := by
    unfold B3
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  constructor
  · intro h
    obtain ⟨a, b, c, hg⟩ := (b3_mem_sub_iff g).1 (hle h)
    refine ⟨⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨c % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    rw [hg]
    simp only [Fin.val_mk, b3_pow_mod0, b3_pow_mod2, b3_pow_mod3]
  · rintro ⟨a, b, c, rfl⟩
    have h0 : u0 ∈ B3 := Subgroup.subset_closure (by simp)
    have h2 : u2 ∈ B3 := Subgroup.subset_closure (by simp)
    have h3 : u3 ∈ B3 := Subgroup.subset_closure (by simp)
    exact mul_mem (mul_mem (pow_mem h0 _) (pow_mem h2 _)) (pow_mem h3 _)

theorem card_B3 : Nat.card B3 = 27 := by
  set F : Fin 3 × Fin 3 × Fin 3 → G6 :=
    fun t => u0 ^ (t.1 : ℕ) * u2 ^ (t.2.1 : ℕ) * u3 ^ (t.2.2 : ℕ) with hF
  have hmem : ∀ t, F t ∈ B3 := fun t => mem_B3_iff.2 ⟨t.1, t.2.1, t.2.2, rfl⟩
  have hbij : Function.Bijective (fun t : Fin 3 × Fin 3 × Fin 3 => (⟨F t, hmem t⟩ : B3)) := by
    refine ⟨fun t t' h => ?_, fun x => ?_⟩
    · have h' : F t = F t' := congrArg Subtype.val h
      obtain ⟨a, b, c⟩ := t
      obtain ⟨a', b', c'⟩ := t'
      obtain ⟨rfl, rfl, rfl⟩ := b3_inj a b c a' b' c' h'
      rfl
    · obtain ⟨a, b, c, hx⟩ := mem_B3_iff.1 x.2
      exact ⟨(a, b, c), Subtype.ext hx.symm⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [← hcard]
  simp

theorem commute_u0_of_mem_sig0 {g : G6} (hg : g ∈ Sig0) : g * u0 = u0 * g := by
  obtain ⟨hsp, h2, h5⟩ := (b3_mem_sig0_iff g).1 hg
  set G : Matrix (Fin 6) (Fin 6) (ZMod 2) := (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hG
  have hc2 : ∀ i, G i 2 = if i = 2 then 1 else 0 := by
    intro i
    have h := congrFun ((mulVec_single_one G 2).symm.trans h2) i
    simpa [b3e, Pi.single_apply] using h
  have hc5 : ∀ i, G i 5 = if i = 5 then 1 else 0 := by
    intro i
    have h := congrFun ((mulVec_single_one G 5).symm.trans h5) i
    simpa [b3e, Pi.single_apply] using h
  have hr5 : ∀ j, G 5 j = if j = 5 then 1 else 0 := by
    intro j
    have h := congrFun (congrFun hsp j) 2
    fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_six, hc2, J0] using h
  have hr2 : ∀ j, G 2 j = if j = 2 then 1 else 0 := by
    intro j
    have h := congrFun (congrFun hsp j) 5
    fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_six, hc5, J0] using h
  apply Units.ext
  show G * u0M = u0M * G
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, u0M, hc2, hc5, hr2, hr5]

theorem B3_le_K0 : B3 ≤ K0 := by
  unfold B3
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u0)
  · exact Subgroup.mem_sup_left u2_mem_sig0
  · exact Subgroup.mem_sup_left u3_mem_sig0

theorem K0_le_sp0 : K0 ≤ Sp0 :=
  sup_le Sig0_le_sp0 (Subgroup.zpowers_le.2 u0_mem_sp0)

theorem u0_not_mem_sig0_of_pow {k : ℕ} (hk : ¬ 3 ∣ k) : u0 ^ k ∉ Sig0 := by
  intro h
  have hfix : ((u0 ^ k : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ b3e 2 = b3e 2 :=
    ((b3_mem_sig0_iff _).1 h).2.1
  rw [pow_eq_pow_mod k u0_pow_three] at hfix
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h1 | h1 <;> rw [h1] at hfix
  · rw [pow_one] at hfix
    exact absurd hfix (by decide)
  · rw [pow_two, b3_mulVec_mul] at hfix
    exact absurd hfix (by decide)

private theorem b3_inf_eq_one (x : G6) (h1 : x ∈ Sig0) (h2 : x ∈ Subgroup.zpowers u0) :
    x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h2
  have hk : u0 ^ k = u0 ^ (k % 3) := by
    have := zpow_mod_orderOf u0 k
    rw [orderOf_u0] at this
    simpa using this.symm
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hk, hr, zpow_zero]
  · exfalso
    rw [hk, hr, zpow_one] at h1
    exact u0_not_mem_sig0_of_pow (k := 1) (by decide) (by rw [pow_one]; exact h1)
  · exfalso
    rw [hk, hr, zpow_ofNat] at h1
    exact u0_not_mem_sig0_of_pow (k := 2) (by decide) h1

private theorem b3_comm_zpow {t s : G6} (ht : t ∈ Subgroup.zpowers u0) (hs : s ∈ Sig0) :
    t * s = s * t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hc : Commute u0 s := (commute_u0_of_mem_sig0 hs).symm
  exact (hc.zpow_left k).eq

private theorem b3_K0_factor (g : G6) (hg : g ∈ K0) :
    ∃ s ∈ Sig0, ∃ t ∈ Subgroup.zpowers u0, s * t = g := by
  unfold K0 at hg
  rw [Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    · exact ⟨1, one_mem _, x, hx, one_mul x⟩
  · exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  · rintro x y _ _ ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    refine ⟨s * s', mul_mem hs hs', t * t', mul_mem ht ht', ?_⟩
    calc s * s' * (t * t') = s * (s' * t) * t' := by simp only [mul_assoc]
      _ = s * (t * s') * t' := by rw [b3_comm_zpow ht hs']
      _ = s * t * (s' * t') := by simp only [mul_assoc]
  · rintro x _ ⟨s, hs, t, ht, rfl⟩
    refine ⟨s⁻¹, inv_mem hs, t⁻¹, inv_mem ht, ?_⟩
    rw [_root_.mul_inv_rev, b3_comm_zpow (inv_mem ht) (inv_mem hs)]

theorem card_K0 (h720 : Nat.card Sig0 = 720) : Nat.card K0 = 2160 := by
  have hK : ∀ s ∈ Sig0, ∀ t ∈ Subgroup.zpowers u0, s * t ∈ K0 := fun s hs t ht =>
    mul_mem (show s ∈ K0 from Subgroup.mem_sup_left hs) (show t ∈ K0 from Subgroup.mem_sup_right ht)
  let Φ : Sig0 × Subgroup.zpowers u0 → K0 := fun p => ⟨p.1.1 * p.2.1, hK _ p.1.2 _ p.2.2⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    have hst : s * t = s' * t' := congrArg Subtype.val h
    have hq : s'⁻¹ * s = t' * t⁻¹ := by
      calc s'⁻¹ * s = s'⁻¹ * (s * t) * t⁻¹ := by group
        _ = s'⁻¹ * (s' * t') * t⁻¹ := by rw [hst]
        _ = t' * t⁻¹ := by group
    have hsig : s'⁻¹ * s ∈ Sig0 := mul_mem (inv_mem hs') hs
    have hz : s'⁻¹ * s ∈ Subgroup.zpowers u0 := by
      rw [hq]
      exact mul_mem ht' (inv_mem ht)
    have h1 : s'⁻¹ * s = 1 := b3_inf_eq_one _ hsig hz
    have h2 : t' * t⁻¹ = 1 := by
      rw [← hq]
      exact h1
    obtain rfl := inv_mul_eq_one.1 h1
    obtain rfl := mul_inv_eq_one.1 h2
    rfl
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := b3_K0_factor g hg
    exact ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, rfl⟩
  have hcard := Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩
  rw [← hcard, Nat.card_prod, h720, Nat.card_zpowers, orderOf_u0]

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
