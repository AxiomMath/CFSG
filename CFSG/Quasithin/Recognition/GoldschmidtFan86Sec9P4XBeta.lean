module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

theorem swap_of_fixed (F : FanTree Γ G) {β p q r : V} {g : G} (hg : g • β = β)
    (hq : Γ.Adj β q) (hr : Γ.Adj β r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcov : ∀ c, Γ.Adj β c → c = p ∨ c = q ∨ c = r) (hgp : g • p = p) (hgq : g • q ≠ q) :
    g • q = r ∧ g • r = q := by
  have hadj : ∀ c, Γ.Adj β c → Γ.Adj β (g • c) := fun c hc => by
    have := (F.adj_smul g β c).2 hc
    rwa [hg] at this
  have h1 : g • q = r := by
    rcases hcov _ (hadj q hq) with h | h | h
    · exact absurd (MulAction.injective g (h.trans hgp.symm)) hpq.symm
    · exact absurd h hgq
    · exact h
  refine ⟨h1, ?_⟩
  rcases hcov _ (hadj r hr) with h | h | h
  · exact absurd (MulAction.injective g (h.trans hgp.symm)) hpr.symm
  · exact h
  · exact absurd (MulAction.injective g (h.trans h1.symm)) hqr.symm

theorem pow_smul_ne_of_cycle {u : G} {α A B : V} (huα : u • α = A) (huA : u • A = B)
    (huB : u • B = α) (hαA : α ≠ A) (hαB : α ≠ B) (n : ℕ) (hn : n % 3 ≠ 0) :
    (u ^ n) • α ≠ α := by
  have e3 : u ^ 3 = u * u * u := by rw [pow_succ, pow_succ, pow_one]
  have hu3 : ∀ c, (c = α ∨ c = A ∨ c = B) → (u ^ 3) • c = c := by
    rintro c (rfl | rfl | rfl) <;> rw [e3, mul_smul, mul_smul]
    · rw [huα, huA, huB]
    · rw [huA, huB, huα]
    · rw [huB, huα, huA]
  have hpow : ∀ q : ℕ, ∀ c, (c = α ∨ c = A ∨ c = B) → ((u ^ 3) ^ q) • c = c := by
    intro q c hc
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, mul_smul, hu3 c hc, ih]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  have hr0 : r ≠ 0 := fun h => hn (by omega)
  interval_cases r
  · exact absurd rfl hr0
  · rw [pow_add, pow_mul, mul_smul, pow_one, huα, hpow q A (Or.inr (Or.inl rfl))]
    exact hαA.symm
  · have h2 : (u ^ 2) • α = B := by rw [pow_two, mul_smul, huα, huA]
    rw [pow_add, pow_mul, mul_smul, h2, hpow q B (Or.inr (Or.inr rfl))]
    exact hαB.symm

theorem exists_xbeta_of_t (F : FanTree Γ G) {α β A : V} {t : G} (hβ3 : valence Γ β = 3)
    (hαβ : Γ.Adj α β) (hβA : Γ.Adj β A) (hAα : A ≠ α) (ht2 : t * t = 1) (htα : t • α = α)
    (htβ : t • β = β) (htA : t • A ≠ A) :
    ∃ x : G, x • β = β ∧ orderOf x = 3 ∧ t * x * t = x⁻¹ ∧ x • α ≠ α := by
  have hβα : Γ.Adj β α := hαβ.symm
  obtain ⟨B, hset, hαB, hAB⟩ := exists_third_neighbor hβ3 hβα hβA hAα.symm
  have hβB : Γ.Adj β B := by
    have : B ∈ Γ.neighborSet β := by rw [hset]; simp
    exact this
  have hcov : ∀ c, Γ.Adj β c → c = α ∨ c = A ∨ c = B := by
    intro c hc
    have : c ∈ Γ.neighborSet β := hc
    rw [hset] at this
    simpa using this
  have hcov' : ∀ c, Γ.Adj β c → c = A ∨ c = α ∨ c = B := fun c hc => by
    rcases hcov c hc with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  obtain ⟨h, hh, hhα⟩ := F.loc_trans β α A hβα hβA
  have hhβ : h • β = β := MulAction.mem_stabilizer_iff.1 hh
  have hhinv : h⁻¹ • β = β := inv_smul_eq_iff.2 hhβ.symm
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨y, hy⟩ : ∃ y, y = h * t * h⁻¹ := ⟨_, rfl⟩
  have hyβ : y • β = β := by rw [hy, mul_smul, mul_smul, hhinv, htβ, hhβ]
  have hy2 : y * y = 1 := by
    rw [hy]
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyA : y • A = A := by
    rw [hy, mul_smul, mul_smul, inv_smul_eq_iff.2 hhα.symm, htα, hhα]
  have hyα : y • α ≠ α := by
    intro hyα
    have hfix := F.frobenius_two β α A hβα hβA hAα.symm y (MulAction.mem_stabilizer_iff.2 hyβ)
      hyα hyA
    apply htA
    have ht_eq : t = h⁻¹ * y * h := by rw [hy]; group
    have hA' : Γ.Adj β (h • A) := by
      have := (F.adj_smul h β A).2 hβA
      rwa [hhβ] at this
    rw [ht_eq, mul_smul, mul_smul, hfix _ hA', inv_smul_smul]
  obtain ⟨htA', htB'⟩ := swap_of_fixed F htβ hβA hβB hAα.symm hαB hAB hcov htα htA
  obtain ⟨hyα_B, hyB_α⟩ := swap_of_fixed F hyβ hβα hβB hAα hAB hαB hcov' hyA hyα
  obtain ⟨u, hu⟩ : ∃ u, u = t * y := ⟨_, rfl⟩
  have huα : u • α = A := by rw [hu, mul_smul, hyα_B, htB']
  have huA : u • A = B := by rw [hu, mul_smul, hyA, htA']
  have huB : u • B = α := by rw [hu, mul_smul, hyB_α, htα]
  have huβ : u • β = β := by rw [hu, mul_smul, hyβ, htβ]
  have hu3α : (u ^ 3) • α = α := by
    have e3 : u ^ 3 = u * u * u := by rw [pow_succ, pow_succ, pow_one]
    rw [e3, mul_smul, mul_smul, huα, huA, huB]
  have hu3β : (u ^ 3) • β = β :=
    MulAction.mem_stabilizer_iff.1 (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.2 huβ) 3)
  have hmem : u ^ 3 ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    ⟨MulAction.mem_stabilizer_iff.2 hu3α, MulAction.mem_stabilizer_iff.2 hu3β⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (F.edge_two α β hαβ)) ⟨u ^ 3, hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨N, hN⟩ : ∃ N, N = orderOf (u ^ 3) := ⟨_, rfl⟩
  have hN3 : N % 3 ≠ 0 := by
    intro h0
    have h1 : 3 ∣ 2 ^ k := by rw [← hk, ← hN]; exact Nat.dvd_of_mod_eq_zero h0
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hxα : (u ^ N) • α ≠ α := pow_smul_ne_of_cycle huα huA huB hAα.symm hαB N hN3
  have hx3 : (u ^ N) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hN, pow_orderOf_eq_one]
  have htu : t * u * t⁻¹ = u⁻¹ := by
    rw [hu, htinv, mul_inv_rev, hyinv, htinv]
    calc t * (t * y) * t = (t * t) * y * t := by group
      _ = y * t := by rw [ht2, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨u ^ N, MulAction.mem_stabilizer_iff.1
    (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.2 huβ) N),
    orderOf_eq_prime hx3 (fun h => hxα (by rw [h, one_smul])), ?_, hxα⟩
  have h1 : t * u ^ N * t⁻¹ = (u ^ N)⁻¹ := by rw [← conj_pow, htu, inv_pow]
  rwa [htinv] at h1

end P4X

end CFSG.Quasithin.Fan86
