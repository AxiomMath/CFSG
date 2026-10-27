module

public import CFSG.Sporadic.J4.QT2LocUniq

public section

namespace CFSG.Quasithin.ModH.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem card_J4_eq : (86775571046077562880 : ℕ) =
    2 ^ 21 * (27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43) := by
  norm_num

theorem not_dvd_pow_sub_one {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : 1 ≤ c)
    (hdvd : p ^ c ∣ 86775571046077562880) : ¬ 256 ∣ p ^ c - 1 := by
  have hpodd : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hM : p ^ c ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 := by
    rw [card_J4_eq] at hdvd
    exact (Nat.Coprime.pow c 21 hpodd).dvd_of_dvd_mul_left hdvd
  have hpM : p ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
    (dvd_pow_self p (by omega)).trans hM
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43 := by
    have p3 : (3 : ℕ).Prime := by norm_num
    have p5 : (5 : ℕ).Prime := by norm_num
    have p7 : (7 : ℕ).Prime := by norm_num
    have p11 : (11 : ℕ).Prime := by norm_num
    have p23 : (23 : ℕ).Prime := by norm_num
    have p29 : (29 : ℕ).Prime := by norm_num
    have p31 : (31 : ℕ).Prime := by norm_num
    have p37 : (37 : ℕ).Prime := by norm_num
    have p43 : (43 : ℕ).Prime := by norm_num
    simp only [Nat.Prime.dvd_mul hp] at hpM
    rcases hpM with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
    · have : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 by norm_num at h ⊢; exact h)
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp p3).1 this)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp p5).1 h))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp p7).1 h)))
    · have : p ∣ 11 := hp.dvd_of_dvd_pow (show p ∣ 11 ^ 3 by norm_num at h ⊢; exact h)
      exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp p11).1 this))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp p23).1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp p29).1 h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp p31).1 h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp p37).1 h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp p43).1 h))))))))
  intro h256
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc3 : c ≤ 3 := by
      by_contra hlt
      have : 3 ^ 4 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 3 (by omega)).trans hM
      norm_num at this
    interval_cases c <;> norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 5 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 5 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 7 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 7 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 3 := by
      by_contra hlt
      have : 11 ^ 4 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 11 (by omega)).trans hM
      norm_num at this
    interval_cases c <;> norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 23 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 23 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 29 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 29 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 31 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 31 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 37 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 37 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256
  · have hc3 : c ≤ 1 := by
      by_contra hlt
      have : 43 ^ 2 ∣ 27 * 5 * 7 * 1331 * 23 * 29 * 31 * 37 * 43 :=
        (pow_dvd_pow 43 (by omega)).trans hM
      norm_num at this
    interval_cases c
    norm_num at h256

theorem not_dvd_256_pow_sub {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hab : b < a)
    (hdvd : p ^ a ∣ 86775571046077562880) : ¬ 256 ∣ p ^ a - p ^ b := by
  intro h
  have hc : 1 ≤ a - b := by omega
  have hpow : p ^ a = p ^ b * p ^ (a - b) := by
    rw [← pow_add]
    congr 1
    omega
  have hsub : p ^ a - p ^ b = p ^ b * (p ^ (a - b) - 1) := by
    rw [hpow, Nat.mul_sub_one]
  rw [hsub] at h
  have hodd : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hcop : Nat.Coprime 256 (p ^ b) := by
    have h2 : Nat.Coprime (2 ^ 8) (p ^ b) := Nat.Coprime.pow 8 b hodd.symm
    simpa using h2
  have h' : 256 ∣ p ^ (a - b) - 1 := hcop.dvd_of_dvd_mul_left h
  exact not_dvd_pow_sub_one hp hp2 hc ((pow_dvd_pow p (Nat.sub_le a b)).trans hdvd) h'

@[expose] noncomputable def conjOut (P E : Subgroup J) (hEP : E ≤ Subgroup.normalizer (P : Set J))
    (hEH : E ≤ Hj) (e : ↥E) (x : {x : J // x ∈ P ∧ x ∉ Hj}) : {x : J // x ∈ P ∧ x ∉ Hj} :=
  ⟨(e : J) * x.1 * (e : J)⁻¹, by
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hEP e.2) x.1).1 x.2.1, fun h => x.2.2 ?_⟩
    have := Hj.mul_mem (Hj.mul_mem (Hj.inv_mem (hEH e.2)) h) (hEH e.2)
    simpa [mul_assoc] using this⟩

theorem conjOut_val (P E : Subgroup J) (hEP : E ≤ Subgroup.normalizer (P : Set J))
    (hEH : E ≤ Hj) (e : ↥E) (x : {x : J // x ∈ P ∧ x ∉ Hj}) :
    (conjOut P E hEP hEH e x).1 = (e : J) * x.1 * (e : J)⁻¹ := rfl

@[expose, instance_reducible] noncomputable def outAction (P E : Subgroup J)
    (hEP : E ≤ Subgroup.normalizer (P : Set J)) (hEH : E ≤ Hj) :
    MulAction ↥E {x : J // x ∈ P ∧ x ∉ Hj} where
  smul := conjOut P E hEP hEH
  one_smul x := by
    apply Subtype.ext
    show (conjOut P E hEP hEH 1 x).1 = x.1
    rw [conjOut_val]
    simp
  mul_smul e f x := by
    apply Subtype.ext
    show (conjOut P E hEP hEH (e * f) x).1 = (conjOut P E hEP hEH e (conjOut P E hEP hEH f x)).1
    rw [conjOut_val, conjOut_val, conjOut_val]
    simp [mul_assoc]

theorem dvd_card_of_small_stabilizers {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hG : Nat.card G = 2 ^ 11) (h : ∀ x : X, Nat.card ↥(MulAction.stabilizer G x) ≤ 8) :
    256 ∣ Nat.card X := by
  classical
  have : Fintype G := Fintype.ofFinite _
  have : Fintype X := Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  have : ∀ b : X, Fintype ↥(MulAction.stabilizer G b) := fun b => Fintype.ofFinite _
  have hcardX := MulAction.card_eq_sum_card_group_div_card_stabilizer G X
  rw [Nat.card_eq_fintype_card, hcardX]
  refine Finset.dvd_sum fun ω _ => ?_
  have hdvd2 : Nat.card ↥(MulAction.stabilizer G ω.out) ∣ 2 ^ 11 := by
    rw [← hG]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj11, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hj3 : j ≤ 3 := by
    by_contra hlt
    have h1 : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := h ω.out
    rw [hj] at h2
    omega
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hG, hj, Nat.pow_div hj11 (by norm_num)]
  exact (show 256 = 2 ^ 8 by norm_num) ▸ pow_dvd_pow 2 (by omega)

theorem stab_small
    (hF : J4Facts) (P : Subgroup J) (hEP : Eg uJ 11 ≤ Subgroup.normalizer (P : Set J))
    (hEH : Eg uJ 11 ≤ Hj) (y : {x : J // x ∈ P ∧ x ∉ Hj}) :
    @Nat.card ↥(@MulAction.stabilizer ↥(Eg uJ 11) _ _ (outAction P (Eg uJ 11) hEP hEH) y) ≤ 8 := by
  classical
  have hy : y.1 ∉ Hj := y.2.2
  have hmem : ∀ s : ↥(@MulAction.stabilizer ↥(Eg uJ 11) _ _ (outAction P (Eg uJ 11) hEP hEH) y),
      y.1⁻¹ * (s.1 : J) * y.1 ∈ Eg uJ 11 := by
    intro s
    have h1 : conjOut P (Eg uJ 11) hEP hEH s.1 y = y := s.2
    have h2 : (s.1 : J) * y.1 * (s.1 : J)⁻¹ = y.1 := by
      have := congrArg Subtype.val h1
      rwa [conjOut_val] at this
    have h3 : (s.1 : J) * y.1 = y.1 * (s.1 : J) := by
      calc (s.1 : J) * y.1 = (s.1 : J) * y.1 * (s.1 : J)⁻¹ * (s.1 : J) := by group
        _ = y.1 * (s.1 : J) := by rw [h2]
    have h4 : y.1⁻¹ * (s.1 : J) * y.1 = (s.1 : J) := by
      calc y.1⁻¹ * (s.1 : J) * y.1 = y.1⁻¹ * ((s.1 : J) * y.1) := by group
        _ = (s.1 : J) := by rw [h3]; group
    rw [h4]
    exact s.1.2
  have hinj : Function.Injective
      (fun s : ↥(@MulAction.stabilizer ↥(Eg uJ 11) _ _ (outAction P (Eg uJ 11) hEP hEH) y) =>
        (⟨(s.1 : J), s.1.2, hmem s⟩ : ↥{x : J | x ∈ Eg uJ 11 ∧ y.1⁻¹ * x * y.1 ∈ Eg uJ 11})) := by
    intro s t hst
    have := congrArg Subtype.val hst
    exact Subtype.ext (Subtype.ext this)
  have h5 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq] at h5
  exact h5.trans (card_inter_le hF hy)

theorem eq_bot_of_normalized_by_E
    (hF : J4Facts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup J} (hP : IsPGroup p ↥P)
    (hEP : Eg uJ 11 ≤ Subgroup.normalizer (P : Set J)) : P = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hM : MatFacts := hF.mat
  have hEcard : Nat.card ↥(Eg uJ 11) = 2 ^ 11 := card_Eg_uJ hM
  have hE2 : IsPGroup 2 ↥(Eg uJ 11) := IsPGroup.of_card hEcard
  have hEH : Eg uJ 11 ≤ Hj := Eg_le_Hj
  have hEP1 : ∀ z : J, z ∈ Eg uJ 11 → z ∈ P → z = 1 := by
    intro z hzE hzP
    obtain ⟨k, hk⟩ := hP ⟨z, hzP⟩
    obtain ⟨m, hm⟩ := hE2 ⟨z, hzE⟩
    have hk' : z ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : z ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h1 := pow_gcd_eq_one.2 ⟨hk', hm'⟩
    rwa [hcop.gcd_eq_one, pow_one] at h1
  have hPH : P ≤ Hj := by
    by_contra hnot
    have h256 : 256 ∣ Nat.card {x : J // x ∈ P ∧ x ∉ Hj} :=
      @dvd_card_of_small_stabilizers ↥(Eg uJ 11) {x : J // x ∈ P ∧ x ∉ Hj} _ _
        (outAction P (Eg uJ 11) hEP hEH) _ hEcard (stab_small hF P hEP hEH)
    have hXcard : Nat.card {x : J // x ∈ P ∧ x ∉ Hj} = Nat.card ↥P - Nat.card ↥(P ⊓ Hj) := by
      have h1 : Nat.card {x : J // x ∈ P ∧ x ∉ Hj} = Set.ncard {x : J | x ∈ P ∧ x ∉ Hj} :=
        (Nat.card_coe_set_eq _).symm
      rw [h1]
      have hsub : ((P ⊓ Hj : Subgroup J) : Set J) ⊆ (P : Set J) := fun x hx => hx.1
      have hdiff : {x : J | x ∈ P ∧ x ∉ Hj} = (P : Set J) \ ((P ⊓ Hj : Subgroup J) : Set J) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_inf]
        tauto
      rw [hdiff, Set.ncard_sdiff hsub (Set.toFinite _)]
      rfl
    obtain ⟨x0, hx0P, hx0H⟩ : ∃ x ∈ P, x ∉ Hj := by
      by_contra hcon
      exact hnot fun x hx => by_contra fun hxH => hcon ⟨x, hx, hxH⟩
    have hXpos : 0 < Nat.card {x : J // x ∈ P ∧ x ∉ Hj} :=
      Nat.card_pos_iff.2 ⟨⟨⟨x0, hx0P, hx0H⟩⟩, inferInstance⟩
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    obtain ⟨b, hb⟩ := (hP.to_inf_left (K := Hj)).exists_card_eq
    have hlt : Nat.card ↥(P ⊓ Hj) < Nat.card ↥P := by
      rw [hXcard] at hXpos
      omega
    have hab : b < a := by
      rw [ha, hb] at hlt
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    have hdvd : p ^ a ∣ 86775571046077562880 := by
      rw [← ha, ← card_J hF]
      exact Subgroup.card_subgroup_dvd_card _
    refine not_dvd_256_pow_sub hp hp2 hab hdvd ?_
    rw [← ha, ← hb, ← hXcard]
    exact h256
  rw [eq_bot_iff]
  intro x hx
  have hxH := hPH hx
  have hcomm : ∀ y ∈ Eg uJ 11, x * y = y * x := by
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ Eg uJ 11 := by
      have := (Eg uJ 11).mul_mem (Hj_normalizes_Eg hM x hxH y hy) ((Eg uJ 11).inv_mem hy)
      simpa [mul_assoc] using this
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ P := by
      have hy' := (Subgroup.mem_normalizer_iff.1 (hEP hy) x⁻¹).1 (P.inv_mem hx)
      have := P.mul_mem hx hy'
      simpa [mul_assoc] using this
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := hEP1 _ h1 h2
    calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y * x := by rw [h3]; group
  have hxE : x ∈ Eg uJ 11 := centralizer_Hj hM hF x hxH hcomm
  exact (Subgroup.mem_bot).2 (hEP1 x hxE hx)

end CFSG.Quasithin.ModH.J4
