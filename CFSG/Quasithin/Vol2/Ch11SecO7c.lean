module

public import CFSG.Quasithin.Vol2.Ch11SecAKE11

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem cube_sub_lt {y z : ℕ} (hy : 1 ≤ y) (h : y < z) : y * (y ^ 2 - 1) < z * (z ^ 2 - 1) := by
  have h1 : y ^ 2 < z ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  have h2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ hy
  have h3 : y ^ 2 - 1 < z ^ 2 - 1 := by omega
  calc y * (y ^ 2 - 1) ≤ y * (z ^ 2 - 1) := Nat.mul_le_mul_left _ h3.le
    _ < z * (z ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right h (by omega)

theorem cube_sub_le {y z : ℕ} (hy : 1 ≤ y) (h : y ≤ z) : y * (y ^ 2 - 1) ≤ z * (z ^ 2 - 1) := by
  rcases h.lt_or_eq with h | rfl
  · exact (cube_sub_lt hy h).le
  · exact le_rfl

theorem eq_of_cube_sub {y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z)
    (h : y * (y ^ 2 - 1) = z * (z ^ 2 - 1)) : y = z := by
  rcases lt_trichotomy y z with hlt | heq | hgt
  · exact absurd h (cube_sub_lt hy hlt).ne
  · exact heq
  · exact absurd h (cube_sub_lt hz hgt).ne'

theorem cube_sub_ne {p k N : ℕ} (hk : 1 ≤ k) (h1 : k * (k ^ 2 - 1) < N)
    (h2 : N < (k + 1) * ((k + 1) ^ 2 - 1)) : p * (p ^ 2 - 1) ≠ N := by
  intro hp
  rcases Nat.lt_or_ge p (k + 1) with hlt | hge
  · rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp at hp
      omega
    · have := cube_sub_le hp0 (show p ≤ k by omega)
      omega
  · have := cube_sub_le (by omega : 1 ≤ k + 1) hge
    omega

theorem psl2_ne_two_pow {p n : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    p * (p ^ 2 - 1) ≠ 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  intro h
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ n = a + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  rw [ha] at h
  have hsq : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq] at h
  have hp2 : ¬ p ∣ 2 := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hpx : ¬ p ∣ a + 1 := fun hd => by
    rw [← ha] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    omega
  have hdvd : p ∣ 2 * ((a + 1) * (a * (a + 2))) := h ▸ dvd_mul_right p _
  have h3 : p ≤ a + 2 := by
    rcases hp.dvd_mul.mp hdvd with h' | h'
    · exact absurd h' hp2
    rcases hp.dvd_mul.mp h' with h' | h'
    · exact absurd h' hpx
    rcases hp.dvd_mul.mp h' with h' | h'
    · rcases Nat.eq_zero_or_pos a with rfl | ha0
      · simp at h
        have : 1 ≤ p ^ 2 - 1 := by
          have : 121 ≤ p ^ 2 := by nlinarith
          omega
        have : 1 ≤ p * (p ^ 2 - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      · have := Nat.le_of_dvd ha0 h'
        omega
    · exact Nat.le_of_dvd (by omega) h'
  have h4 := cube_sub_le (by omega : 1 ≤ p) h3
  have hsq2 : (a + 2) ^ 2 - 1 = (a + 1) * (a + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq2, h] at h4
  have ha3 : a ≤ 3 := by nlinarith
  have h5 : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := cube_sub_le (by norm_num) hp11
  rw [h] at h5
  interval_cases a <;> omega

theorem card_of_psl2 {B : Type} [Group B] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e : B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :
    Nat.card B = p * (p ^ 2 - 1) / 2 := by
  have hp : p.Prime := Fact.out
  rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula (ZMod p)
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [Nat.card_zmod, pow_one]⟩,
    Nat.card_zmod]

theorem isSimpleGroup_of_psl2 {B : Type} [Group B] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e : B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) : IsSimpleGroup B :=
  @MulEquiv.isSimpleGroup _ _ _ _
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)) e

theorem center_eq_bot_of_simple {B : Type} [Group B] [Finite B] [IsSimpleGroup B]
    (h : ¬ (Nat.card B).Prime) : Subgroup.center B = ⊥ :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (SecA.C10KH.nonabelian_of_simple (X := B) h)).2

theorem pCore_eq_bot_of_simple {B : Type} [Group B] [Finite B] [IsSimpleGroup B] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card B) : CFSG.pCore 2 B = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 B) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 B := by
      intro g
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))

noncomputable def modO2EquivOfBot {G : Type} [Group G] {B : Subgroup G}
    (h : CFSG.pCore 2 ↥B = ⊥) : CFSG.Quasithin.ModO2 B ≃* ↥B :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem not_isExt_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hV : ∀ (V : Type) [Group V], PV V → Nontrivial V)
    (hY : ∀ (Q : Type) [Group Q], PY Q → Nontrivial Q) : ¬ IsExt X PV PY := by
  rintro ⟨V, hVn, hPV, hPY⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with rfl | rfl
  · have := hV _ hPV
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := this
    rw [Subgroup.mem_bot] at ha hb
    exact hab (Subtype.ext (ha.trans hb.symm))
  · have := hY _ hPY
    obtain ⟨a, b, hab⟩ := this
    apply hab
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y => exact QuotientGroup.eq.mpr (Subgroup.mem_top _)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
