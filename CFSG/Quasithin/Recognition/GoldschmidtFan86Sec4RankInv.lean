module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Three

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

section Abs

variable {X C : Type*} [Group X] [Group C]

set_option synthInstance.maxSize 2000 in
theorem fact_prod3 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ s₁ s₂ : Equiv.Perm (Fin 3), s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ σ = s₁ * s₂ := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
theorem fact_prod4 : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ s₁ s₂ : Equiv.Perm (Fin 4), s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ σ = s₁ * s₂ := by
  decide +kernel

theorem exists_involution_not_mem {n : ℕ} (hn : n = 3 ∨ n = 4) (hC : IsPGroup 2 C)
    (e : X ≃* Equiv.Perm (Fin n) × C) {p : X} (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1)
    {K : Subgroup X} (hK : IsPGroup 2 K) : ∃ t : X, t * t = 1 ∧ t ∉ K := by
  have hc : (e p).2 = 1 := by
    have h := congrArg (fun x => (e x).2) hp3
    exact eq_one_of_pow_three_eq_one hC (by simpa [map_pow] using h)
  have hσ3 : (e p).1 ^ 3 = 1 := by
    have h := congrArg (fun x => (e x).1) hp3
    simpa [map_pow] using h
  have hσ1 : (e p).1 ≠ 1 := by
    intro h
    exact hp1 (e.injective (Prod.ext (by simpa using h) (by simpa using hc)))
  obtain ⟨s₁, s₂, h1, h2, hs⟩ : ∃ s₁ s₂ : Equiv.Perm (Fin n), s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧
      (e p).1 = s₁ * s₂ := by
    rcases hn with rfl | rfl
    · exact fact_prod3 _ hσ3 hσ1
    · exact fact_prod4 _ hσ3 hσ1
  have hp : p = e.symm (s₁, 1) * e.symm (s₂, 1) := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Prod.ext (by simpa using hs) (by simpa using hc)
  by_contra hcon
  push Not at hcon
  have hK1 : e.symm (s₁, 1) ∈ K := hcon _ (by rw [← map_mul]; simp [h1])
  have hK2 : e.symm (s₂, 1) ∈ K := hcon _ (by rw [← map_mul]; simp [h2])
  have hpK : p ∈ K := hp ▸ K.mul_mem hK1 hK2
  obtain ⟨k, hk⟩ := hK ⟨p, hpK⟩
  have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have := (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))).1
    ⟨hk', hp3⟩
  exact hp1 this

end Abs

section Geo

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Track.le_fixer_of_normalizer (T' : Track Γ G) {Y : Subgroup G}
    (hτ : T'.τ ∈ Subgroup.normalizer (Y : Set G))
    (h1 : ∀ y ∈ Y, y • T'.line.vert 1 = T'.line.vert 1)
    (h2 : ∀ y ∈ Y, y • T'.line.vert 2 = T'.line.vert 2) : Y ≤ T'.fixer := by
  intro y hy
  rw [T'.mem_fixer]
  have key : ∀ (m : ℤ) (v : V), (∀ z ∈ Y, z • v = v) → y • (T'.τ ^ m • v) = T'.τ ^ m • v := by
    intro m v hv
    have h1' := (Subgroup.mem_normalizer_iff.1
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hτ m)) y).1 hy
    have h2' := hv _ h1'
    rw [inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at h2'
    exact h2'
  intro j
  rcases Int.emod_two_eq_zero_or_one j with hj | hj
  · obtain ⟨m, rfl⟩ : ∃ m : ℤ, j = 2 + 2 * m := ⟨(j - 2) / 2, by omega⟩
    rw [← T'.zpow_smul_vert m 2]
    exact key m _ h2
  · obtain ⟨m, rfl⟩ : ∃ m : ℤ, j = 1 + 2 * m := ⟨(j - 1) / 2, by omega⟩
    rw [← T'.zpow_smul_vert m 1]
    exact key m _ h1

theorem exists_pow_moving {g : G} {α : V} (hmove : g • α ≠ α) (hord : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    ∃ y ∈ Subgroup.zpowers g, y • α ≠ α ∧ (y * y) • α = α := by
  classical
  obtain ⟨k, hk⟩ := hord
  have hex : ∃ j : ℕ, g ^ 2 ^ (j + 1) • α = α := by
    refine ⟨k, ?_⟩
    rw [pow_succ, pow_mul, hk, one_pow, one_smul]
  refine ⟨g ^ 2 ^ Nat.find hex, ?_, ?_, ?_⟩
  · rw [← zpow_natCast]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      simpa using hmove
    · have := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      rw [Nat.sub_add_cancel hpos] at this
      exact this
  · have hspec := Nat.find_spec hex
    have e : g ^ 2 ^ (Nat.find hex + 1) = g ^ 2 ^ Nat.find hex * g ^ 2 ^ Nat.find hex := by
      rw [pow_succ, mul_two, pow_add]
    rw [e] at hspec
    exact hspec

end Geo

section Pair

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_involution_moving (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c)
    {L : Subgroup G} (hL : L ∈ LamSet Γ G a b c) (h3 : valence Γ a = 3) (h28 : Fan28) :
    ∃ t ∈ L ⊓ MulAction.stabilizer G a, t * t = 1 ∧ t • b ≠ b := by
  obtain ⟨n, hn, C, hCg, hCf, hC2, ⟨e⟩⟩ := fan41_3 F a b c L hab hac hL h3 h28
  obtain ⟨hfin, htr, hcard, hP⟩ := lamSet_setup F hab hL
  have hdvd : 3 ∣ Nat.card ↥(L ⊓ MulAction.stabilizer G a) := by
    rw [hcard, h3]
    exact dvd_mul_right _ _
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ MulAction.stabilizer G a)) 3 hdvd
  have hp3 : p ^ 3 = 1 := by rw [← hp]; exact pow_orderOf_eq_one p
  have hp1 : p ≠ 1 := fun h => by
    rw [h, orderOf_one] at hp
    omega
  have hKL : L ⊓ nbrStab Γ G a ≤ L ⊓ MulAction.stabilizer G a := fun g hg =>
    ⟨hg.1, F.nbrStab_le_stabilizer _ hg.2⟩
  have hK2 : IsPGroup 2 ↥((L ⊓ nbrStab Γ G a).subgroupOf (L ⊓ MulAction.stabilizer G a)) :=
    ((F.nbrStab_isPGroup a).to_le (inf_le_right : L ⊓ nbrStab Γ G a ≤ _)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hKL).symm
  obtain ⟨t₁, ht₁, ht₁K⟩ := exists_involution_not_mem hn hC2 e hp3 hp1 hK2
  obtain ⟨y, hy, hty⟩ : ∃ y, Γ.Adj a y ∧ (t₁ : G) • y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact ht₁K ⟨t₁.2.1, fun w hw => hcon w hw⟩
  obtain ⟨g, hg, hgy⟩ := htr y b hy hab
  refine ⟨g * t₁ * g⁻¹, (L ⊓ MulAction.stabilizer G a).mul_mem
    ((L ⊓ MulAction.stabilizer G a).mul_mem hg t₁.2) ((L ⊓ MulAction.stabilizer G a).inv_mem hg),
    ?_, ?_⟩
  · have h1 : (t₁ : G) * t₁ = 1 := congrArg Subtype.val ht₁
    calc g * t₁ * g⁻¹ * (g * t₁ * g⁻¹) = g * (t₁ * t₁) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h
    have hgy' : g⁻¹ • b = y := by rw [← hgy, inv_smul_smul]
    apply hty
    rw [mul_smul, mul_smul, hgy'] at h
    have := eq_inv_smul_iff.2 h
    rw [hgy'] at this
    exact this

theorem exists_t_y (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c)
    {L : Subgroup G} (hL : L ∈ LamSet Γ G a b c) (h3 : valence Γ a = 3) (h28 : Fan28) :
    ∃ t y : G, t ∈ L ⊓ MulAction.stabilizer G a ∧ y ∈ L ⊓ MulAction.stabilizer G b ∧
      t * t = 1 ∧ t • b ≠ b ∧ y • a ≠ a ∧ (y * y) • a = a := by
  obtain ⟨t, htL, ht2, htb⟩ := exists_involution_moving F hab hac hL h3 h28
  have hL' := hL
  obtain ⟨Q, hQ0, hQ, hLQ, hloc, ⟨g₀, hg₀, hg₀a⟩⟩ := hL
  rcases F.fixes_or_trans b (inf_le_right : L ⊓ MulAction.stabilizer G b ≤ _) with
    ⟨w₀, hw₀, hfix⟩ | htr
  swap
  · exact absurd htr (fan41_nt F hab hL')
  have hP2 : IsPGroup 2 ↥(L ⊓ MulAction.stabilizer G b) :=
    (F.edge_two b w₀ hw₀).to_le fun g hg => ⟨hg.2, MulAction.mem_stabilizer_iff.2 (hfix g hg)⟩
  obtain ⟨k, hk⟩ := hP2 ⟨g₀, hg₀⟩
  have hk' : g₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hmove : g₀ • a ≠ a := by
    rw [hg₀a]
    exact fun h => hac h.symm
  obtain ⟨y, hy, hya, hyy⟩ := exists_pow_moving hmove ⟨k, hk'⟩
  exact ⟨t, y, htL, (Subgroup.zpowers_le.2 hg₀) hy, ht2, htb, hya, hyy⟩

end Pair

end CFSG.Quasithin.Fan86
