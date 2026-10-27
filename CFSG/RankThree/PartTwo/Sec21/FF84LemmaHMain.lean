module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHClass2
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHQuot
public import CFSG.RankThree.PartOne.MB3.FixedPoint
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH

open Equiv

variable {K : Type} [Group K]

theorem exists_order_three (e : K ≃* A5) : ∃ y : K, y ^ 3 = 1 ∧ y ≠ 1 := by
  refine ⟨e.symm (mk5 c[0, 1, 2]), ?_, ?_⟩
  · have : (mk5 c[0, 1, 2]) ^ 3 = 1 := by decide
    rw [← map_pow, this, map_one]
  · intro h
    have : (mk5 c[0, 1, 2]) = 1 := by simpa using h
    revert this; decide

theorem higman_comm [Finite K] [IsSimpleGroup K] (e : K ≃* A5) :
    ∀ (n : ℕ) (S : Type) [Group S] [Finite S] (ρ : K →* MulAut S), Nat.card S = n →
      ¬ 3 ∣ n → Fpf ρ → ∀ u v : S, u * v = v * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ ρ hn h3 hρ
  by_cases hS : Subsingleton S
  · intro u v; haveI := hS; exact Subsingleton.elim (u * v) (v * u)
  have hnt : Nontrivial S := not_subsingleton_iff_nontrivial.1 hS
  obtain ⟨y, hy3, hy1⟩ := exists_order_three e
  have hα3 : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hα1 : ρ y ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := exists_ne (1 : S)
    exact hu (hρ y hy3 hy1 u (by rw [h]; rfl))
  have hord : orderOf (ρ y) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hα3) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hα1
    · exact h
  have hnil : Group.IsNilpotent S :=
    CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime (ρ y)
      (by rw [hord]; exact Nat.prime_three) (hρ y hy3 hy1)
  haveI := hnil
  haveI : Nontrivial (Subgroup.center S) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (Group.IsNilpotent.center_ne_bot S)
  have hZinv : ∀ k : K, ∀ a ∈ Subgroup.center S, ρ k a ∈ Subgroup.center S := by
    intro k a ha
    rw [Subgroup.mem_center_iff] at ha ⊢
    intro g
    have hk : ρ k (ρ k⁻¹ g) = g := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    have h2 := congrArg (ρ k) (ha (ρ k⁻¹ g))
    rw [map_mul, map_mul, hk] at h2
    exact h2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
  have hZ1 : 1 < Nat.card (Subgroup.center S) := Finite.one_lt_card
  have hnpos : 0 < n := hn ▸ Nat.card_pos
  have hlt : Nat.card (S ⧸ Subgroup.center S) < n := by
    rw [← hn, hcard]
    have : 0 < Nat.card (S ⧸ Subgroup.center S) := Nat.card_pos
    nlinarith
  have hdvdq : Nat.card (S ⧸ Subgroup.center S) ∣ n := ⟨_, by rw [← hn, hcard]⟩
  have hdvdz : Nat.card (Subgroup.center S) ∣ n := ⟨_, by rw [← hn, hcard, mul_comm]⟩
  have hq := ih _ hlt (S ⧸ Subgroup.center S) (quotAct ρ (Subgroup.center S) hZinv) rfl
    (fun h => h3 (h.trans hdvdq))
    (fpf_quot hρ (Subgroup.center S) hZinv (fun h => h3 (h.trans hdvdz)))
  have hcc : ∀ u v : S, cm u v ∈ Subgroup.center S := by
    intro u v
    rw [← QuotientGroup.eq_one_iff]
    have := hq (u : S ⧸ Subgroup.center S) (v : S ⧸ Subgroup.center S)
    simp only [cm, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]
    group
  exact comm_of_class_two e hρ hcc

theorem four_dvd_of_pow_two (m : ℕ) (h : 2 ^ m % 5 = 1) : 4 ∣ m := by
  have h16 : 16 ^ (m / 4) % 5 = 1 := by rw [Nat.pow_mod]; norm_num
  have e2 : 2 ^ m = 16 ^ (m / 4) * 2 ^ (m % 4) := by
    conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul]
    norm_num
  rw [e2, Nat.mul_mod, h16, one_mul, Nat.mod_mod] at h
  have hr : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : m % 4
  · omega
  all_goals simp at h

theorem higman_abstract [Finite K] [IsSimpleGroup K] (e : K ≃* A5) {S : Type} [Group S] [Finite S]
    (ρ : K →* MulAut S) (h3 : ¬ 3 ∣ Nat.card S) (hρ : Fpf ρ) :
    (∀ u v : S, u * v = v * u) ∧ (∀ u : S, u * u = 1) ∧ ∃ r : ℕ, Nat.card S = 16 ^ r := by
  have hcomm := higman_comm e _ S ρ rfl h3 hρ
  have hA : InvAb ρ (⊤ : Subgroup S) := ⟨fun a _ b _ => hcomm a b, fun _ _ _ => trivial⟩
  have h6 := pow_six_eq_one e hρ hA
  have hsq : ∀ u : S, u * u = 1 := by
    intro u
    have h6u : u ^ 6 = 1 := h6 u trivial
    have hdvd : orderOf u ∣ 6 := orderOf_dvd_of_pow_eq_one h6u
    have hcop : Nat.Coprime (orderOf u) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h => h3 (h.trans (orderOf_dvd_natCard u))
    have : orderOf u ∣ 2 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 this
  refine ⟨hcomm, hsq, ?_⟩
  have hpow2 : Nat.card S = 2 ^ (Nat.card S).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro p hp hpd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := S) p hpd
    have : orderOf u ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hsq u
    rw [hu] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  set m := (Nat.card S).primeFactorsList.length with hm
  let z : K := e.symm z5
  have hz5 : z ^ 5 = 1 := by
    have : z5 ^ 5 = 1 := by decide
    show (e.symm z5) ^ 5 = 1
    rw [← map_pow, this, map_one]
  have hfix := fixed_five_eq_one e hρ hA (fun a _ => hsq a)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hα : ρ z ^ 5 = 1 := by rw [← map_pow, hz5, map_one]
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime (ρ z) hα
  have hone : Nat.card {x : S // ρ z x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, map_one _⟩⟩⟩
    rw [hfix a.1 trivial a.2, hfix b.1 trivial b.2]
  rw [hone, hpow2] at hmod
  have h5 : 2 ^ m % 5 = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    simpa using this
  obtain ⟨r, hr⟩ := four_dvd_of_pow_two m h5
  refine ⟨r, ?_⟩
  rw [hpow2, hr, pow_mul]
  norm_num

end CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH
