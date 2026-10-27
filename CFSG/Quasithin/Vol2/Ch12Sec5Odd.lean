module

public import CFSG.Quasithin.Vol2.Ch12Sec5L5a

public section

namespace CFSG.Quasithin.H13.S125Odd

open Matrix

local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def x31 : M5 :=
  !![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]

@[expose] def x7 : M5 :=
  !![0, 0, 1, 0, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def x5 : M5 :=
  !![0, 0, 0, 1, 0; 1, 0, 0, 1, 0; 0, 1, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def x3 : M5 :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def y3 : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

theorem x31_pow : x31 ^ 31 = 1 := by decide +kernel

theorem x7_pow : x7 ^ 7 = 1 := by decide

theorem x5_pow : x5 ^ 5 = 1 := by decide

theorem x3_pow : x3 ^ 3 = 1 := by decide

theorem y3_pow : y3 ^ 3 = 1 := by decide

theorem x3_y3 : x3 * y3 = y3 * x3 := by decide

theorem det_eq_one_of_pow {A : M5} {n : ℕ} (hn : n ≠ 0) (h : A ^ n = 1) : A.det = 1 := by
  have h1 : A.det ^ n = 1 := by rw [← Matrix.det_pow, h, Matrix.det_one]
  rcases (show ∀ d : ZMod 2, d = 0 ∨ d = 1 by decide) A.det with h0 | h0
  · rw [h0, zero_pow hn] at h1
    exact absurd h1 (by decide)
  · exact h0

@[expose] def X31 : SL5 := ⟨x31, det_eq_one_of_pow (by norm_num) x31_pow⟩

@[expose] def X7 : SL5 := ⟨x7, det_eq_one_of_pow (by norm_num) x7_pow⟩

@[expose] def X5 : SL5 := ⟨x5, det_eq_one_of_pow (by norm_num) x5_pow⟩

@[expose] def X3 : SL5 := ⟨x3, det_eq_one_of_pow (by norm_num) x3_pow⟩

@[expose] def Y3 : SL5 := ⟨y3, det_eq_one_of_pow (by norm_num) y3_pow⟩

theorem orderOf_of_prime {X : SL5} {p : ℕ} [Fact p.Prime] (h : (X : M5) ^ p = 1)
    (h1 : (X : M5) ≠ 1) : orderOf X = p :=
  orderOf_eq_prime (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, h]; rfl))
    fun he => h1 (by rw [he]; rfl)

theorem orderOf_X31 : orderOf X31 = 31 :=
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  orderOf_of_prime x31_pow (by decide)

theorem orderOf_X7 : orderOf X7 = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_of_prime x7_pow (by decide)

theorem orderOf_X5 : orderOf X5 = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_of_prime x5_pow (by decide)

theorem fix_x31 : (Finset.univ.filter fun v : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat x31 *ᵥ v = v).card < 128 := by decide +kernel

theorem fix_x7 : (Finset.univ.filter fun v : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat x7 *ᵥ v = v).card < 128 := by decide +kernel

theorem fix_x5 : (Finset.univ.filter fun v : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat x5 *ᵥ v = v).card < 128 := by decide +kernel

theorem fix_x3y3 : ∀ a b : Fin 3, (a, b) ≠ (0, 0) → (Finset.univ.filter fun v : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat (x3 ^ (a : ℕ) * y3 ^ (b : ℕ)) *ᵥ v = v).card < 128 := by
  decide +kernel

@[expose] noncomputable def nFix (x : SL5) : ℕ :=
  (Finset.univ.filter fun v : Fin 10 → ZMod 2 => JonesParshall.wedgeRep x v = v).card

theorem nFix_eq (x : SL5) : nFix x = (Finset.univ.filter fun v : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat (x : M5) *ᵥ v = v).card := by
  unfold nFix
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S125ZV.wedgeRep_apply]

theorem wedgeRep_mul_apply (a b : SL5) (v : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep (a * b) v = JonesParshall.wedgeRep a (JonesParshall.wedgeRep b v) := by
  rw [map_mul, Module.End.mul_apply]

theorem wedgeRep_inv_apply (a : SL5) (v : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep a⁻¹ (JonesParshall.wedgeRep a v) = v := by
  rw [← wedgeRep_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]

theorem wedgeRep_apply_inv (a : SL5) (v : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep a (JonesParshall.wedgeRep a⁻¹ v) = v := by
  rw [← wedgeRep_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]

theorem nFix_conj (g x : SL5) : nFix (g⁻¹ * x * g) = nFix x := by
  unfold nFix
  refine Finset.card_nbij' (fun v => JonesParshall.wedgeRep g v)
    (fun v => JonesParshall.wedgeRep g⁻¹ v) (fun v hv => ?_) (fun v hv => ?_)
    (fun v _ => wedgeRep_inv_apply g v) (fun v _ => wedgeRep_apply_inv g v)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have := congrArg (JonesParshall.wedgeRep g) hv
    rwa [wedgeRep_mul_apply, wedgeRep_mul_apply, wedgeRep_apply_inv] at this
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [wedgeRep_mul_apply, wedgeRep_mul_apply, wedgeRep_apply_inv, hv]

@[expose] def stab (v : Fin 10 → ZMod 2) : Subgroup SL5 where
  carrier := {g | JonesParshall.wedgeRep g v = v}
  one_mem' := by
    change JonesParshall.wedgeRep 1 v = v
    rw [map_one, Module.End.one_apply]
  mul_mem' := fun {a b} ha hb => by
    change JonesParshall.wedgeRep (a * b) v = v
    rw [wedgeRep_mul_apply, show JonesParshall.wedgeRep b v = v from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change JonesParshall.wedgeRep a⁻¹ v = v
    conv_lhs => rw [← show JonesParshall.wedgeRep a v = v from ha]
    exact wedgeRep_inv_apply a v

theorem nFix_le_of_mem_zpowers {y z : SL5} (hz : (orderOf z).Prime)
    (hy : y ∈ Subgroup.zpowers z) (hy1 : y ≠ 1) : nFix y ≤ nFix z := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers z :=
    (Subgroup.zpowers_le (G := SL5)).2 hy
  have hyz : orderOf y ∣ orderOf z := orderOf_dvd_of_mem_zpowers hy
  have hoy : orderOf y = orderOf z := by
    rcases (Nat.dvd_prime hz).1 hyz with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hoy])
  have hzy : z ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers z
  unfold nFix
  refine Finset.card_le_card fun v hv => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have hst : Subgroup.zpowers y ≤ stab v := (Subgroup.zpowers_le (G := SL5)).2 hv
  exact hst hzy

theorem X3_Y3 : X3 * Y3 = Y3 * X3 := Subtype.ext x3_y3

theorem coe_X3_pow_mul (a b : ℕ) : ((X3 ^ a * Y3 ^ b : SL5) : M5) = x3 ^ a * y3 ^ b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_pow]
  rfl

theorem mul_closed : ∀ a b c d : Fin 3, ∃ e f : Fin 3,
    x3 ^ (a : ℕ) * y3 ^ (b : ℕ) * (x3 ^ (c : ℕ) * y3 ^ (d : ℕ)) =
      x3 ^ (e : ℕ) * y3 ^ (f : ℕ) := by
  decide +kernel

theorem cube_eq : ∀ a b : Fin 3, (x3 ^ (a : ℕ) * y3 ^ (b : ℕ)) ^ 3 = 1 := by decide +kernel

theorem inj : ∀ a b c d : Fin 3, x3 ^ (a : ℕ) * y3 ^ (b : ℕ) = x3 ^ (c : ℕ) * y3 ^ (d : ℕ) →
    a = c ∧ b = d := by
  decide +kernel

@[expose] def P3 : Subgroup SL5 where
  carrier := {g | ∃ a b : Fin 3, g = X3 ^ (a : ℕ) * Y3 ^ (b : ℕ)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    obtain ⟨e, f, h⟩ := mul_closed a b c d
    refine ⟨e, f, Subtype.ext ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_X3_pow_mul, coe_X3_pow_mul, coe_X3_pow_mul]
    exact h
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    have h3 : (X3 ^ (a : ℕ) * Y3 ^ (b : ℕ)) ^ 3 = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, coe_X3_pow_mul, cube_eq]
      rfl)
    have hinv : (X3 ^ (a : ℕ) * Y3 ^ (b : ℕ))⁻¹ =
        (X3 ^ (a : ℕ) * Y3 ^ (b : ℕ)) * (X3 ^ (a : ℕ) * Y3 ^ (b : ℕ)) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_three, h3]
    obtain ⟨e, f, h⟩ := mul_closed a b a b
    refine ⟨e, f, ?_⟩
    rw [hinv]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_X3_pow_mul, coe_X3_pow_mul]
    exact h

theorem card_P3 : Nat.card P3 = 9 := by
  have hbij : Function.Bijective (fun ab : Fin 3 × Fin 3 =>
      (⟨X3 ^ (ab.1 : ℕ) * Y3 ^ (ab.2 : ℕ), ab.1, ab.2, rfl⟩ : ↥P3)) := by
    refine ⟨fun ⟨a, b⟩ ⟨c, d⟩ h => ?_, fun ⟨g, a, b, hg⟩ => ⟨(a, b), Subtype.ext hg.symm⟩⟩
    have h1 := congrArg (fun g : ↥P3 => ((g : SL5) : M5)) h
    simp only [coe_X3_pow_mul] at h1
    obtain ⟨rfl, rfl⟩ := inj a b c d h1
    rfl
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

theorem nFix_P3 {g : SL5} (hg : g ∈ P3) (hg1 : g ≠ 1) : nFix g < 128 := by
  obtain ⟨a, b, rfl⟩ := hg
  rw [nFix_eq, coe_X3_pow_mul]
  refine fix_x3y3 a b fun h => hg1 ?_
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  simp

theorem exists_conj_mem {p : ℕ} [Fact p.Prime] {P : Subgroup SL5}
    (hP : Nat.card P = p ^ (Nat.card SL5).factorization p) {x : SL5} (hx : orderOf x = p) :
    ∃ g : SL5, g⁻¹ * x * g ∈ P := by
  have hQ : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  let S : Sylow p SL5 := Sylow.ofCard P hP
  obtain ⟨Q', hQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL5 S Q'
  refine ⟨g, ?_⟩
  have hq' : x ∈ (Q' : Subgroup SL5) := hQ' (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
  simpa [S, MulAut.smul_def, MulAut.conj_inv_apply, mul_assoc] using hq'

theorem factorization_eq {p q n : ℕ} (hp : p.Prime) (hn : 9999360 = p ^ q * n) (hpn : ¬ p ∣ n) :
    (Nat.card SL5).factorization p = q := by
  have hn0 : n ≠ 0 := fun h => by rw [h, mul_zero] at hn; exact absurd hn (by norm_num)
  rw [card_sl_five_zmod_two, hn, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hn0,
    Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]

theorem odd_prime_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 9999360) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  rw [show (9999360 : ℕ) = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 by norm_num] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · exact absurd (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h)) hp2
        · exact Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl (hq 5 (by norm_num) h))
    · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (hq 31 (by norm_num) h)))

theorem nFix_lt {x : SL5} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : orderOf x = p) :
    nFix x < 128 := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 9999360 := by
    rw [← card_sl_five_zmod_two, ← hx]
    exact orderOf_dvd_natCard x
  have hx1 : ∀ g : SL5, g⁻¹ * x * g ≠ 1 := fun g h => by
    have : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hcyc : ∀ {X : SL5}, orderOf X = p → Nat.card (Subgroup.zpowers X) =
      p ^ (Nat.card SL5).factorization p → nFix X < 128 → nFix x < 128 := by
    intro X hX hP hfix
    obtain ⟨g, hg⟩ := exists_conj_mem hP hx
    rw [← nFix_conj g x]
    exact lt_of_le_of_lt (nFix_le_of_mem_zpowers (hX ▸ hp) hg (hx1 g)) hfix
  rcases odd_prime_dvd hp hp2 hdvd with rfl | rfl | rfl | rfl
  · obtain ⟨g, hg⟩ := exists_conj_mem (P := P3)
      (by rw [card_P3, factorization_eq Nat.prime_three (q := 2) (n := 1111040) (by norm_num)
        (by norm_num)]; norm_num) hx
    rw [← nFix_conj g x]
    exact nFix_P3 hg (hx1 g)
  · exact hcyc orderOf_X5 (by rw [Nat.card_zpowers, orderOf_X5,
      factorization_eq (by norm_num) (q := 1) (n := 1999872) (by norm_num) (by norm_num),
      pow_one]) (by rw [nFix_eq]; exact fix_x5)
  · exact hcyc orderOf_X7 (by rw [Nat.card_zpowers, orderOf_X7,
      factorization_eq (by norm_num) (q := 1) (n := 1428480) (by norm_num) (by norm_num),
      pow_one]) (by rw [nFix_eq]; exact fix_x7)
  · exact hcyc orderOf_X31 (by rw [Nat.card_zpowers, orderOf_X31,
      factorization_eq (by norm_num) (q := 1) (n := 322560) (by norm_num) (by norm_num),
      pow_one]) (by rw [nFix_eq]; exact fix_x31)

end CFSG.Quasithin.H13.S125Odd
