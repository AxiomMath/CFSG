module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cr2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem card_inf_of_sup_top {R N : Subgroup X} [N.Normal] (hN : N.index = 4) (hsup : R ⊔ N = ⊤) :
    Nat.card R = 4 * Nat.card (R ⊓ N : Subgroup X) := by
  have h1 : N.relIndex R = 4 := by
    have := Subgroup.relIndex_sup_right R N
    rw [hsup, Subgroup.relIndex_top_right, hN] at this
    exact this.symm
  have h2 : (R ⊓ N).relIndex R = 4 := by rw [inf_comm, Subgroup.inf_relIndex_right]; exact h1
  have h3 := Subgroup.card_mul_index ((R ⊓ N).subgroupOf R)
  have h4 : Nat.card ↥((R ⊓ N).subgroupOf R) = Nat.card ↥(R ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : R ⊓ N ≤ R)).toEquiv
  rw [h4] at h3
  have h5 : ((R ⊓ N).subgroupOf R).index = 4 := h2
  rw [h5] at h3
  omega

theorem exists_normal_index_eight (R T E U : Subgroup X) (f ρ z : X) (m : ℕ)
    (hX : Nat.card X = 64 * m) (hm : Odd m) (hR2 : IsPGroup 2 R) (hR64 : Nat.card R = 64)
    (hTi : T.relIndex R = 2) (hEi : E.relIndex R = 2)
    (hfc : ∀ x : X, x * f = f * x) (hf2 : f ^ 2 = 1) (hρR : ρ ∈ R) (hρ2 : ρ ^ 2 = f)
    (hzR : z ∈ R) (hz2 : z ^ 2 = 1) (hρz : ρ * z * ρ⁻¹ = f * z)
    (hUR : U ≤ R) (hU8 : Nat.card U = 8) (hfU : f ∉ U)
    (hUodd : U ≤ Subgroup.closure {x : X | Odd (orderOf x)})
    (nf1 : ∀ a : X, a⁻¹ * ρ * a ∉ T) (nf2 : ∀ a : X, a⁻¹ * z * a ∉ E)
    (nf3 : ∀ a : X, a⁻¹ * (ρ * z) * a ∉ E) :
    ∃ Q : Subgroup X, Q.Normal ∧ Q.index = 8 ∧ R ⊓ Q = U ∧
      Q = Subgroup.closure {x : X | Odd (orderOf x)} := by
  have hRindex : R.index = m := by
    have := Subgroup.card_mul_index R
    rw [hX, hR64] at this
    omega
  have hRidx : ¬ 2 ∣ R.index := by
    rw [hRindex]; exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hm)
  obtain ⟨A, B, hA, hB, hAi, hBi, hne, hsA, hsB⟩ := exists_two_normal R T E f ρ z hR2 hRidx hTi
    hEi hfc hf2 hρR hρ2 hzR hz2 hρz nf1 nf2 nf3
  set N := A ⊓ B with hN
  have hNn : N.Normal := inferInstance
  have hNi : N.index = 4 := index_inf_eq_four hAi hBi hne
  have hNsq : ∀ x : X, x ^ 2 ∈ N := fun x => ⟨hsA x, hsB x⟩
  have hNodd : ∀ x : X, Odd (orderOf x) → x ∈ N := fun x hx =>
    mem_of_odd_orderOf (H := ⊤) (fun y _ => hNsq y) (Subgroup.mem_top x) hx
  have hclN : Subgroup.closure {x : X | Odd (orderOf x)} ≤ N :=
    (Subgroup.closure_le N).2 fun x hx => hNodd x hx
  have hUN : U ≤ N := hUodd.trans hclN
  have hfN : f ∈ N := hρ2 ▸ hNsq ρ
  have hfR : f ∈ R := hρ2 ▸ R.pow_mem hρR 2
  have hsup : R ⊔ N = ⊤ := by
    have h1 : (R ⊔ N).index ∣ m := hRindex ▸ Subgroup.index_dvd_of_le le_sup_left
    have h2 : (R ⊔ N).index ∣ 4 := hNi ▸ Subgroup.index_dvd_of_le le_sup_right
    have hcop : Nat.Coprime m 4 := by
      exact (Odd.coprime_two_right hm).pow_right 2
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    exact Subgroup.index_eq_one.1 this
  have hK16 : Nat.card (R ⊓ N : Subgroup X) = 16 := by
    have := card_inf_of_sup_top hNi hsup
    omega
  set K : Subgroup X := R ⊓ N with hK
  have hKR : K ≤ R := inf_le_left
  have hKN : K ≤ N := inf_le_right
  have hUK : U ≤ K := le_inf hUR hUN
  have hfK : f ∈ K := ⟨hfR, hfN⟩
  have hKidx : K.index = 4 * m := by
    have := Subgroup.card_mul_index K
    rw [hX, hK16] at this
    omega
  have hKN' : K.relIndex N = m := by
    have := Subgroup.relIndex_mul_index hKN
    rw [hNi, hKidx] at this
    omega
  have hUKidx : U.relIndex K = 2 := by
    have h3 := Subgroup.card_mul_index (U.subgroupOf K)
    have h4 : Nat.card ↥(U.subgroupOf K) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
    rw [h4, hU8, hK16] at h3
    have h5 : (U.subgroupOf K).index = U.relIndex K := rfl
    omega
  have hKp : IsPGroup 2 K := hR2.to_le hKR
  have hKodd : ¬ 2 ∣ K.relIndex N := by
    rw [hKN']; exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hm)
  have hf4 : f ^ 4 = 1 := by
    calc f ^ 4 = (f ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hf2, one_pow]
  obtain ⟨N3, hN3N, hN3n, hN3i, hN3sq, hN3f⟩ := thompson_transfer_quartic_subgroup (X := N)
    (P := K) (Q := U) hKN hKp hKodd hUKidx hfK hf4
    (fun x _ => by rw [hf2]; simp) (fun x _ => by rw [conj_central hfc x]; exact hfU)
  have hN3idx : N3.index = 8 := by
    have := Subgroup.relIndex_mul_index hN3N
    rw [hN3i, hNi] at this
    omega
  have hcl3 : Subgroup.closure {x : X | Odd (orderOf x)} ≤ N3 :=
    (Subgroup.closure_le N3).2 fun x hx =>
      mem_of_odd_orderOf (H := N) (fun y hy => hN3sq y hy) (hNodd x hx) hx
  set Q := Subgroup.closure {x : X | Odd (orderOf x)} with hQ
  have hQn : Q.Normal := normal_closure_odd
  have hUQ : U ≤ Q := hUodd
  have hQN3 : Q ≤ N3 := hcl3
  have hQidx : Q.index = 8 := by
    have h8 : 8 ∣ Q.index := hN3idx ▸ Subgroup.index_dvd_of_le hQN3
    have hQne : Q.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hpow : Q.index = 2 ^ Q.index.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hQne fun {p} hp hpd => by
        by_contra hne
        exact prime_dvd_index_closure_odd hp hne hpd
    have hcard := Subgroup.card_mul_index Q
    have h8Q : 8 ∣ Nat.card Q := hU8 ▸ Subgroup.card_dvd_of_le hUQ
    have hdvd64 : Q.index ∣ 64 := by
      have h1 : Q.index ∣ 64 * m := hX ▸ ⟨Nat.card Q, by rw [← hcard, mul_comm]⟩
      have hc : Nat.Coprime Q.index m := by
        rw [hpow]
        exact (Odd.coprime_two_left hm).pow_left _
      exact hc.dvd_of_dvd_mul_right h1
    obtain ⟨a, ha, haeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Q.index ∣ 2 ^ 6 from hdvd64)
    obtain ⟨k, hk⟩ := hm
    have h3a : 3 ≤ a := by
      have : 2 ^ 3 ∣ 2 ^ a := haeq ▸ h8
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    rw [haeq] at hcard ⊢
    interval_cases a
    · norm_num
    all_goals (norm_num at hcard ⊢; omega)
  have hQeq : Q = N3 := by
    have h1 := Subgroup.relIndex_mul_index hQN3
    rw [hN3idx, hQidx] at h1
    have h2 : Q.relIndex N3 = 1 := by omega
    exact le_antisymm hQN3 (Subgroup.relIndex_eq_one.1 h2)
  have hRN3 : R ⊓ N3 = U := by
    have hle : R ⊓ N3 ≤ K := inf_le_inf_left R hN3N
    have hUle : U ≤ R ⊓ N3 := le_inf hUR (hUodd.trans hcl3)
    have hd : Nat.card ↥(R ⊓ N3 : Subgroup X) ∣ 16 := hK16 ▸ Subgroup.card_dvd_of_le hle
    have h8 : 8 ∣ Nat.card ↥(R ⊓ N3 : Subgroup X) := hU8 ▸ Subgroup.card_dvd_of_le hUle
    have hne : R ⊓ N3 ≠ K := fun h => hN3f (by
      have : f ∈ R ⊓ N3 := h ▸ hfK
      exact this.2)
    have hle16 : Nat.card ↥(R ⊓ N3 : Subgroup X) ≤ 16 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.card ↥(R ⊓ N3 : Subgroup X) := Nat.card_pos
    have hlt : Nat.card ↥(R ⊓ N3 : Subgroup X) ≠ 16 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hK16, h]))
    have h8c : Nat.card ↥(R ⊓ N3 : Subgroup X) = 8 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hUle (by omega)).symm
  exact ⟨Q, hQn, hQidx, by rw [hQeq]; exact hRN3, rfl⟩

end CFSG.Quasithin.H13.F431.U42Aut
