module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section NumberTheory

theorem dvd_sub_one_of_pow_dvd_pow_sub_one {p s e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hs : 1 ≤ s) (h : p ^ s ∣ e ^ p - 1) : p ∣ e - 1 ∧ p ^ (s - 1) ∣ e - 1 := by
  have hpe : p ∣ e ^ p - 1 := (dvd_pow_self p (by omega : s ≠ 0)).trans h
  have hep : 1 ≤ e ^ p := Nat.one_le_pow _ _ he
  have h1 : p ∣ e - 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (e ^ p - 1) p).mpr hpe
    rw [Nat.cast_sub hep, Nat.cast_pow, ZMod.pow_card, Nat.cast_one, sub_eq_zero] at hz
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub he, Nat.cast_one, hz, sub_self]
  refine ⟨h1, ?_⟩
  rcases he.lt_or_eq with he1 | rfl
  · have hne : ¬ p ∣ e := fun hd => by
      have := Nat.dvd_sub hd h1
      rw [Nat.sub_sub_self he] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := padicValNat.pow_sub_pow (hp.out.odd_of_ne_two hp2) he1 h1 hne
      (n := p) hp.out.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hne0 : e ^ p - 1 ≠ 0 := by
      have : 1 < e ^ p := Nat.one_lt_pow hp.out.ne_zero he1
      omega
    have hle := (padicValNat_dvd_iff_le hne0).mp h
    rw [hlte] at hle
    exact (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  · simp

theorem one_add_pow_modEq (N j : ℕ) : (1 + N) ^ j ≡ 1 + j * N [MOD N ^ 2] := by
  induction j with
  | zero => simp [Nat.ModEq]
  | succ j ih =>
    have e : (1 + j * N) * (1 + N) = 1 + (j + 1) * N + j * N ^ 2 := by ring
    calc (1 + N) ^ (j + 1) = (1 + N) ^ j * (1 + N) := pow_succ _ _
      _ ≡ (1 + j * N) * (1 + N) [MOD N ^ 2] := ih.mul_right _
      _ = 1 + (j + 1) * N + j * N ^ 2 := e
      _ ≡ 1 + (j + 1) * N [MOD N ^ 2] := Nat.add_mul_mod_self_right _ _ _

theorem one_add_mul_pow_pow_modEq {p s c j : ℕ} (hs : 2 ≤ s) (hcj : c * j % p = 1) :
    (1 + c * p ^ (s - 1)) ^ j ≡ 1 + p ^ (s - 1) [MOD p ^ s] := by
  have hdvd : p ^ s ∣ (c * p ^ (s - 1)) ^ 2 := by
    have h1 : p ^ s ∣ p ^ (2 * (s - 1)) := pow_dvd_pow p (by omega)
    have h2 : p ^ (2 * (s - 1)) ∣ (c * p ^ (s - 1)) ^ 2 := ⟨c ^ 2, by ring⟩
    exact h1.trans h2
  have h3 := (one_add_pow_modEq (c * p ^ (s - 1)) j).of_dvd hdvd
  have e : 1 + j * (c * p ^ (s - 1)) = 1 + p ^ (s - 1) + (c * j / p) * p ^ s := by
    have hdm := Nat.div_add_mod (c * j) p
    rw [hcj] at hdm
    have hps : p ^ s = p * p ^ (s - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc 1 + j * (c * p ^ (s - 1)) = 1 + (c * j) * p ^ (s - 1) := by ring
      _ = 1 + (p * (c * j / p) + 1) * p ^ (s - 1) := by rw [hdm]
      _ = 1 + p ^ (s - 1) + (c * j / p) * p ^ s := by rw [hps]; ring
  rw [e] at h3
  exact h3.trans (Nat.add_mul_mod_self_right _ _ _)

end NumberTheory

@[expose] def GGL45TorusAbInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)

@[expose] def GGL45TorusPowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∃ e : ℕ, ∀ u ∈ U₁, (u ^ e)⁻¹ * (x⁻¹ * u * x) ∈ U ⊓ Subgroup.centralizer (K : Set G)

theorem ggL45TorusInput_of_pow (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hab : GGL45TorusAbInput) (hpow : GGL45TorusPowInput) (hrankx : GGL45RankXInput) :
    GGL45TorusInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hcfg.odd
  have hcomm := hab G p B Bs x L D J X B₂ d y K U U₁ hcfg
  obtain ⟨e, he⟩ := hpow G p B Bs x L D J X B₂ d y K U U₁ hcfg
  obtain ⟨a₁, ha₁, a₂, -, -, -, hind⟩ := hrankx G p B Bs x L D J X B₂ d y K U U₁ hcfg
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hU₁U : U₁ ≤ U := hcfg.part_le
  have hNV : U ≤ Subgroup.normalizer (V : Set G) := fun u hu =>
    mem_normalizer_of_forall_conj_mem fun v hv => by
      have := hcfg.conj_mem_V (U.inv_mem hu) hv
      rwa [inv_inv] at this
  obtain ⟨-, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hx1 : x ≠ 1 := fun h => hxU₁ (h ▸ U₁.one_mem)
  have ha₁x : a₁ * x * a₁⁻¹ * x⁻¹ ∉ V := fun h => by
    have := hind 1 0 (by simpa using h)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.1)
  set N : Subgroup U := V.subgroupOf U with hNdef
  have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNV
  set q : U →* U ⧸ N := QuotientGroup.mk' N with hqdef
  have hq : ∀ a b : U, q a = q b ↔ (a : G)⁻¹ * b ∈ V := fun a b => by
    rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hNdef,
      Subgroup.mem_subgroupOf]
    simp
  have hq1 : ∀ a : U, q a = 1 ↔ (a : G) ∈ V := fun a => by
    rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
  set xU : U := ⟨x, hxU⟩ with hxUdef
  have hpowq : ∀ u : U, (u : G) ∈ U₁ → (q xU)⁻¹ * q u * q xU = q u ^ e := by
    intro u hu
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    refine ((hq _ _).mpr ?_).symm
    simpa [hxUdef] using he u hu
  have hiter : ∀ k : ℕ, ∀ u : U, (u : G) ∈ U₁ →
      (q xU ^ k)⁻¹ * q u * q xU ^ k = q u ^ e ^ k := by
    intro k
    induction k with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have e1 : (q xU ^ (k + 1))⁻¹ * q u * q xU ^ (k + 1) =
          (q xU)⁻¹ * ((q xU ^ k)⁻¹ * q u * q xU ^ k) * q xU := by
        rw [pow_succ]
        group
      have e2 : (q xU)⁻¹ * q u ^ e ^ k * q xU = ((q xU)⁻¹ * q u * q xU) ^ e ^ k := by
        have := conj_pow (a := (q xU)⁻¹) (b := q u) (i := e ^ k)
        rw [inv_inv] at this
        exact this.symm
      rw [e1, ih u hu, e2, hpowq u hu, ← pow_mul, pow_succ']
  have hfin : ∃ n : ℕ, ∀ u ∈ U₁, u ^ p ^ n ∈ V := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hcfg.isPGroup.to_le hU₁U)
    refine ⟨n, fun u hu => ?_⟩
    have h := pow_card_eq_one' (x := (⟨u, hu⟩ : U₁))
    have h' : u ^ Nat.card U₁ = 1 := congrArg Subtype.val h
    rw [← hn, h']
    exact one_mem _
  classical
  obtain ⟨s, hs, hmin⟩ : ∃ s : ℕ, (∀ u ∈ U₁, u ^ p ^ s ∈ V) ∧
      ∀ m < s, ¬ ∀ u ∈ U₁, u ^ p ^ m ∈ V :=
    ⟨Nat.find hfin, Nat.find_spec hfin, fun m hm => Nat.find_min hfin hm⟩
  have hs1 : 1 ≤ s := by
    by_contra h0
    have h0' : s = 0 := by omega
    apply ha₁x
    have h1 : a₁ ∈ V := by simpa [h0'] using hs a₁ ha₁
    have h2 : x * a₁⁻¹ * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hNV hxU) _).mp (V.inv_mem h1)
    have e : a₁ * x * a₁⁻¹ * x⁻¹ = a₁ * (x * a₁⁻¹ * x⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 h2
  obtain ⟨u₀, hu₀, hu₀V⟩ : ∃ u ∈ U₁, u ^ p ^ (s - 1) ∉ V := by
    obtain ⟨u, hu, huV⟩ := not_forall₂.mp (hmin (s - 1) (by omega))
    exact ⟨u, hu, huV⟩
  have hordle : ∀ u : U, (u : G) ∈ U₁ → orderOf (q u) ∣ p ^ s := fun u hu =>
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hq1]; simpa using hs u hu)
  set u₀U : U := ⟨u₀, hU₁U hu₀⟩ with hu₀U
  have hord : orderOf (q u₀U) = p ^ s := by
    have h1 : ¬ q u₀U ^ p ^ (s - 1) = 1 := fun h => hu₀V (by
      rw [← map_pow, hq1] at h
      simpa using h)
    have h2 : q u₀U ^ p ^ (s - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel hs1, ← map_pow, hq1]
      simpa using hs u₀ hu₀
    have := orderOf_eq_prime_pow h1 h2
    rwa [Nat.sub_add_cancel hs1] at this
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    apply hu₀V
    have h := he (u₀ ^ p ^ (s - 1)) (U₁.pow_mem hu₀ _)
    rw [he0, pow_zero, inv_one, one_mul] at h
    have := (Subgroup.mem_normalizer_iff.mp (hNV hxU) _).mp h
    simpa [mul_assoc] using this
  have hdvd : p ^ s ∣ e ^ p - 1 := by
    have h := hiter p u₀U hu₀
    have hxp : q xU ^ p = 1 := by
      rw [← map_pow, hq1]
      simp [hxUdef, hcfg.x_pow]
    rw [hxp, inv_one, one_mul, mul_one] at h
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    have hep : 1 ≤ e ^ p := Nat.one_le_pow _ _ he1
    have h3 : q u₀U ^ (e ^ p - 1) * q u₀U = q u₀U := by
      rw [← pow_succ, Nat.sub_add_cancel hep]
      exact h.symm
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  obtain ⟨hp1e, c, hc⟩ := dvd_sub_one_of_pow_dvd_pow_sub_one hp2 he1 hs1 hdvd
  have hec : e = 1 + c * p ^ (s - 1) := by
    rw [mul_comm c, ← hc]
    omega
  have hnt : ¬ p ^ s ∣ e - 1 := by
    intro h
    apply ha₁x
    have htriv : ∀ u : U, (u : G) ∈ U₁ → (q xU)⁻¹ * q u * q xU = q u := by
      intro u hu
      rw [hpowq u hu]
      have hmod : e ≡ 1 [MOD orderOf (q u)] :=
        ((Nat.modEq_iff_dvd' he1).mpr ((hordle u hu).trans h)).symm
      rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
    set a₁U : U := ⟨a₁, hU₁U ha₁⟩ with ha₁U
    have h1 := htriv a₁U ha₁
    have hcq : q a₁U * q xU = q xU * q a₁U := by
      calc q a₁U * q xU = q xU * ((q xU)⁻¹ * q a₁U * q xU) := by group
        _ = q xU * q a₁U := by rw [h1]
    have h2 : q (a₁U * xU * a₁U⁻¹ * xU⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcq]
      group
    rw [hq1] at h2
    simpa [ha₁U, hxUdef] using h2
  have hs2 : 2 ≤ s := by
    by_contra h
    have hs1' : s = 1 := by omega
    apply hnt
    rw [hs1', pow_one]
    exact hp1e
  have hpc : ¬ p ∣ c := by
    rintro ⟨t, rfl⟩
    apply hnt
    refine ⟨t, ?_⟩
    have hps : p ^ s = p * p ^ (s - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hc, hps]
    ring
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc).symm hp.one_lt
  have hxj1 : x ^ j ≠ 1 := by
    intro h
    have hpj : p ∣ j := by
      have := orderOf_dvd_of_pow_eq_one h
      rwa [orderOf_eq_prime hcfg.x_pow hx1] at this
    rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hpj c)] at hj
    exact absurd hj zero_ne_one
  have hzx : Subgroup.zpowers (x ^ j) = Subgroup.zpowers x :=
    zpowers_eq_of_mem_of_ne_one hcfg.x_pow (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j) hxj1
  refine ⟨s, hs2, hcomm, hs, ⟨u₀, hu₀, hu₀V⟩, x ^ j, hzx, fun u hu => ?_⟩
  set uU : U := ⟨u, hU₁U hu⟩ with huU
  have h1 := hiter j uU hu
  have hmod : e ^ j ≡ 1 + p ^ (s - 1) [MOD orderOf (q uU)] := by
    rw [hec]
    exact (one_add_mul_pow_pow_modEq hs2 hj).of_dvd (hordle uU hu)
  have h2 : q uU ^ e ^ j = q uU ^ (1 + p ^ (s - 1)) := pow_eq_pow_iff_modEq.mpr hmod
  have h3 : q (uU ^ (1 + p ^ (s - 1))) = q ((xU ^ j)⁻¹ * uU * xU ^ j) := by
    rw [map_pow, ← h2, ← h1, map_mul, map_mul, map_inv, map_pow]
  have := (hq _ _).mp h3
  simpa [huU, hxUdef] using this

end CFSG.StandardType

end
