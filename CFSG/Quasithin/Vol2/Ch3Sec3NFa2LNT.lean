module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2G1
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Assembly.LowTwoRank

private theorem sq_dvd_prod_aux {ι : Type} [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (f : ι → ℕ) (h : p ^ 2 ∣ ∏ i ∈ s, f i) :
    (∃ i ∈ s, p ^ 2 ∣ f i) ∨ (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p ∣ f i ∧ p ∣ f j) := by
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    rw [Finset.prod_empty] at h
    have h1 : p ^ 2 ≤ 1 := Nat.le_of_dvd one_pos h
    have h2 : 2 ≤ p := hp.two_le
    nlinarith
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    by_cases hpa : p ∣ f a
    · by_cases hps : p ∣ ∏ i ∈ s, f i
      · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime f).1 hps
        exact Or.inr ⟨a, Finset.mem_insert_self a s, i, Finset.mem_insert_of_mem hi,
          fun hai => ha (by rw [hai]; exact hi), hpa, hpi⟩
      · have hcop : Nat.Coprime (p ^ 2) (∏ i ∈ s, f i) :=
          Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hps)
        exact Or.inl ⟨a, Finset.mem_insert_self a s, hcop.dvd_of_dvd_mul_right h⟩
    · have hcop : Nat.Coprime (p ^ 2) (f a) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
      rcases ih (hcop.dvd_of_dvd_mul_left h) with ⟨i, hi, hpi⟩ | ⟨i, hi, j, hj, hij, hpi, hpj⟩
      · exact Or.inl ⟨i, Finset.mem_insert_of_mem hi, hpi⟩
      · exact Or.inr ⟨i, Finset.mem_insert_of_mem hi, j, Finset.mem_insert_of_mem hj, hij, hpi, hpj⟩

private theorem gcd_le_nine_of_ne {j j' : ℕ} (hj1 : 1 ≤ j) (hj1' : 1 ≤ j') (hj : j ≤ 19)
    (hj' : j' ≤ 19) (hne : j ≠ j') : Nat.gcd j j' ≤ 9 := by
  by_contra hg
  have hg10 : 10 ≤ Nat.gcd j j' := by omega
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left j j'
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right j j'
  have ha1 : a = 1 := by
    rcases Nat.lt_or_ge a 2 with h | h
    · interval_cases a
      · omega
      · rfl
    · have := Nat.mul_le_mul hg10 h
      omega
  have hb1 : b = 1 := by
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b
      · omega
      · rfl
    · have := Nat.mul_le_mul hg10 h
      omega
  subst ha1 hb1
  exact hne (by omega)

private theorem not_sq_dvd_two_pow_sub_one {q j : ℕ} (hq : q.Prime)
    (h24 : q % 24 = 11 ∨ q % 24 = 13) (hj1 : 1 ≤ j) (hj19 : j ≤ 19) :
    ¬ q ^ 2 ∣ 2 ^ j - 1 := by
  intro hd
  have h2j : 2 ^ j ≤ 2 ^ 19 := Nat.pow_le_pow_right (by norm_num) hj19
  have h2j' : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have hpos : 0 < 2 ^ j - 1 := by omega
  have hsq : q ^ 2 ≤ 2 ^ j - 1 := Nat.le_of_dvd hpos hd
  have h19 : (2 : ℕ) ^ 19 = 524288 := by norm_num
  have hq2 : q ^ 2 ≤ 524287 := by omega
  have hqle : q ≤ 724 := by nlinarith
  obtain ⟨k, hk⟩ : ∃ k, q = 24 * k + 11 ∨ q = 24 * k + 13 := ⟨q / 24, by omega⟩
  have hk30 : k ≤ 30 := by omega
  rcases hk with rfl | rfl <;> interval_cases k <;> norm_num at hq <;> interval_cases j <;>
    norm_num at hd

private theorem nfa2_sq_not_dvd_gl (q : ℕ) (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (n : ℕ) (hn : n ≤ 19) : ¬ q ^ 2 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  intro hd
  have hq2 : q ≠ 2 := by omega
  have hcop1 : ∀ i : ℕ, Nat.Coprime q (2 ^ i) := fun i =>
    Nat.Coprime.pow_right i ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have hcop2 : ∀ i : ℕ, Nat.Coprime (q ^ 2) (2 ^ i) := fun i =>
    Nat.Coprime.pow_left 2 (hcop1 i)
  have hfac : ∀ i : Fin n, 2 ^ n - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (n - i) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ n := i.2.le
    have h1 : 2 ^ n = 2 ^ (i : ℕ) * 2 ^ (n - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, Nat.mul_sub_one]
  rcases sq_dvd_prod_aux hq Finset.univ (fun i : Fin n => 2 ^ n - 2 ^ (i : ℕ)) hd with
    ⟨i, -, hi⟩ | ⟨i, -, i', -, hne, hi, hi'⟩
  ·
    rw [hfac i] at hi
    have hj : q ^ 2 ∣ 2 ^ (n - i) - 1 := (hcop2 i).dvd_of_dvd_mul_left hi
    have hi19 := i.2
    exact not_sq_dvd_two_pow_sub_one hq h24 (by omega) (by omega) hj
  ·
    have hne' : (i : ℕ) ≠ (i' : ℕ) := fun h => hne (Fin.ext h)
    have h1 : q ∣ 2 ^ (n - i) - 1 :=
      (hcop1 i).dvd_of_dvd_mul_left (by rw [← hfac i]; exact hi)
    have h2 : q ∣ 2 ^ (n - i') - 1 :=
      (hcop1 i').dvd_of_dvd_mul_left (by rw [← hfac i']; exact hi')
    have hgcd : q ∣ 2 ^ (Nat.gcd (n - i) (n - i')) - 1 := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one]
      exact Nat.dvd_gcd h1 h2
    have hi19 := i.2
    have hi'19 := i'.2
    have hg9 : Nat.gcd (n - i) (n - i') ≤ 9 :=
      gcd_le_nine_of_ne (by omega) (by omega) (by omega) (by omega) (by omega)
    have hgpos : 1 ≤ Nat.gcd (n - i) (n - i') := Nat.gcd_pos_of_pos_left _ (by omega)
    exact nfa2G1_not_dvd_two_pow_sub_one hq h24 hgpos hg9 hgcd

@[expose] def nfa2ProdRep {Kb : Type} [Group Kb] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ₁ ρ₂ : Kb →* (W ≃ₗ[ZMod 2] W)) (hcomm : ∀ k k', ρ₁ k * ρ₂ k' = ρ₂ k' * ρ₁ k) :
    (Kb × Kb) →* (W ≃ₗ[ZMod 2] W) where
  toFun x := ρ₁ x.1 * ρ₂ x.2
  map_one' := by simp
  map_mul' := fun x y => by
    obtain ⟨k, k'⟩ := x
    obtain ⟨l, l'⟩ := y
    simp only [Prod.mk_mul_mk, map_mul, mul_assoc]
    congr 1
    rw [← mul_assoc, hcomm l k', mul_assoc]

theorem nfa2_two_factor_dim (q : ℕ) (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (Kb : Type) [Group Kb] (hmodel : StatedClassicalModel Kb .PSL 2 q 1)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ₁ ρ₂ : Kb →* (W ≃ₗ[ZMod 2] W))
    (hcomm : ∀ k k', ρ₁ k * ρ₂ k' = ρ₂ k' * ρ₁ k)
    (h₁ : ∃ k, ρ₁ k ≠ 1) (h₂ : ∃ k, ρ₂ k ≠ 1) :
    20 ≤ Module.finrank (ZMod 2) W := by
  have hq11 : 11 ≤ q := by omega
  have hq2 : q ≠ 2 := by omega
  have hq5 : 5 ≤ q := by omega
  have hsimKb : IsSimpleGroup Kb := isSimpleGroup_of_psl_two_model hq5 hmodel
  obtain ⟨eK⟩ := nonempty_mulEquiv_psl_zmod hq hmodel
  have hq_odd : Odd q := hq.odd_of_ne_two hq2
  have h2dvd : 2 ∣ q ^ 2 - 1 := by
    have hodd2 : Odd (q ^ 2) := hq_odd.pow
    obtain ⟨s, hs⟩ := hodd2
    exact ⟨s, by omega⟩
  have hNcard : Nat.card Kb = q * ((q ^ 2 - 1) / 2) := by
    rw [Nat.card_congr eK.toEquiv, card_psl_two_zmod hq hq2, Nat.mul_div_assoc q h2dvd]
  have hq121 : 121 ≤ q ^ 2 := by nlinarith
  have hqKb : q ∣ Nat.card Kb := by
    rw [hNcard]
    exact dvd_mul_right q _
  have hZ : Subgroup.center Kb = ⊥ := by
    rcases hsimKb.eq_bot_or_eq_top_of_normal (Subgroup.center Kb) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative Kb := Subgroup.center_eq_top_iff.1 h
      have hp : (Nat.card Kb).Prime := (Group.is_simple_iff_prime_card (α := Kb)).1 hsimKb
      rw [hNcard] at hp
      exact Nat.not_prime_mul (by omega) (by omega) hp
  have hinj : ∀ ρ : Kb →* (W ≃ₗ[ZMod 2] W), (∃ k, ρ k ≠ 1) → Function.Injective ρ := by
    intro ρ hρ
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimKb.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hρ
      have hkker : k ∈ ρ.ker := by
        rw [h]
        exact Subgroup.mem_top k
      exact hk (MonoidHom.mem_ker.1 hkker)
  have hinj₁ := hinj ρ₁ h₁
  have hinj₂ := hinj ρ₂ h₂
  have hinjP : Function.Injective (nfa2ProdRep ρ₁ ρ₂ hcomm) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, k'⟩ hkk
    have hkk' : ρ₁ k * ρ₂ k' = 1 := hkk
    have hk : k ∈ Subgroup.center Kb := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply hinj₁
      have hc : Commute (ρ₁ l) (ρ₂ k') := hcomm l k'
      have hk1 : ρ₁ k = (ρ₂ k')⁻¹ := eq_inv_of_mul_eq_one_left hkk'
      rw [map_mul, map_mul, hk1]
      exact hc.inv_right.eq
    rw [hZ, Subgroup.mem_bot] at hk
    subst hk
    have hk' : ρ₂ k' = 1 := by simpa using hkk'
    have hk'1 : k' = 1 := hinj₂ (by rw [hk', map_one])
    subst hk'1
    rfl
  have hdvd : Nat.card (Kb × Kb) ∣ Nat.card (W ≃ₗ[ZMod 2] W) :=
    Subgroup.card_dvd_of_injective (nfa2ProdRep ρ₁ ρ₂ hcomm) hinjP
  rw [Nat.card_prod] at hdvd
  have hsq : q ^ 2 ∣ Nat.card (W ≃ₗ[ZMod 2] W) := by
    rw [pow_two]
    exact dvd_trans (mul_dvd_mul hqKb hqKb) hdvd
  have hGL : Nat.card (W ≃ₗ[ZMod 2] W) = ∏ i : Fin (Module.finrank (ZMod 2) W),
      (2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ)) := by
    have eX : Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) ≃*
        (W ≃ₗ[ZMod 2] W) :=
      (Matrix.GeneralLinearGroup.toLin' (Module.finBasis (ZMod 2) W)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
    rw [← Nat.card_congr eX.toEquiv, Matrix.card_GL_field, ZMod.card]
  rw [hGL] at hsq
  by_contra hlt
  rw [not_le] at hlt
  exact nfa2_sq_not_dvd_gl q hq h24 _ (by omega) hsq

end CFSG.Quasithin.H13.NFa2
