module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourNA5
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan

public section

namespace CFSG.Quasithin.A7Std

open Equiv Equiv.Perm

theorem p0L_orbit_zero_check :
    (List.finRange 7).all (fun a => (List.finRange 7).all fun b =>
      (p0L.any fun p => decide (p a ≠ 0 ∧ p a ≠ a ∧ p a ≠ b)) ||
        decide (a = 0 ∨ a = 5 ∨ a = 6)) = true := by
  decide +kernel

theorem p0L_orbit_zero {a b : Fin 7} (h : ∀ p ∈ p0L, p a = 0 ∨ p a = a ∨ p a = b) :
    a = 0 ∨ a = 5 ∨ a = 6 := by
  have hc := p0L_orbit_zero_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hc
  rcases hc a b with ⟨p, hp, h0, ha, hb⟩ | hc
  · rcases h p hp with h' | h' | h'
    · exact absurd h' h0
    · exact absurd h' ha
    · exact absurd h' hb
  · exact hc

theorem p0L_orbit_five_check :
    (List.finRange 7).all (fun a => (List.finRange 7).all fun b =>
      !(decide (a = 5 ∨ a = 6)) || (p0L.any fun p => decide (p a ≠ 0 ∧ p a ≠ a ∧ p a ≠ b)) ||
        decide ((b = 5 ∨ b = 6) ∧ b ≠ a)) = true := by
  decide +kernel

theorem p0L_orbit_five {a b : Fin 7} (ha : a = 5 ∨ a = 6)
    (h : ∀ p ∈ p0L, p a = 0 ∨ p a = a ∨ p a = b) : (b = 5 ∨ b = 6) ∧ b ≠ a := by
  have hc := p0L_orbit_five_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq] at hc
  rcases hc a b with (hc | ⟨p, hp, h0, ha', hb⟩) | hc
  · exact absurd ha hc
  · rcases h p hp with h' | h' | h'
    · exact absurd h' h0
    · exact absurd h' ha'
    · exact absurd h' hb
  · exact hc

theorem p0L_trans :
    ∀ a c : Fin 7, (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) → (c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) →
      ∃ p ∈ p0L, p a = c := by
  decide +kernel

theorem eq_one_of_forall_ne_zero {β : Perm (Fin 7)} (h : ∀ c : Fin 7, c ≠ 0 → β c = c) :
    β = 1 := by
  refine Equiv.ext fun c => ?_
  rw [Perm.one_apply]
  by_cases hc : c = 0
  · subst hc
    by_contra h0
    exact h0 (β.injective (h (β 0) h0))
  · exact h c hc

theorem pow_apply_of_pow_three {x : Perm (Fin 7)} (hx3 : x ^ 3 = 1) (j : ℕ) (i : Fin 7) :
    (x ^ j) i = i ∨ (x ^ j) i = x i ∨ (x ^ j) i = x (x i) := by
  have e : x ^ j = x ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hx3, one_pow, one_mul]
  rw [e]
  obtain h0 | h1 | h2 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  · rw [h0, pow_zero, Perm.one_apply]
    exact Or.inl rfl
  · rw [h1, pow_one]
    exact Or.inr (Or.inl rfl)
  · rw [h2, pow_two, Perm.mul_apply]
    exact Or.inr (Or.inr rfl)

theorem pow_apply_mem_of_forall {x : Perm (Fin 7)} {S : Fin 7 → Prop} (hx : ∀ i, S i → S (x i)) :
    ∀ (k : ℕ) (i : Fin 7), S i → S ((x ^ k) i) := by
  intro k
  induction k with
  | zero => intro i hi; rwa [pow_zero, Perm.one_apply]
  | succ k ih => intro i hi; rw [pow_succ, Perm.mul_apply]; exact ih _ (hx i hi)

theorem commute_of_conj_eq_pow {Γ : Type*} [Group Γ] {x β : Γ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hβ3 : β ^ 3 = 1) {j : ℕ} (h : β * x * β⁻¹ = x ^ j) : x * β = β * x := by
  have e : x ^ j = x ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hx3, one_pow, one_mul]
  rw [e] at h
  have hb3 : β ^ 3 = β * β * β := by rw [pow_succ, pow_succ, pow_one]
  have hβ : β * (β * (β * x * β⁻¹) * β⁻¹) * β⁻¹ = x := by
    calc β * (β * (β * x * β⁻¹) * β⁻¹) * β⁻¹ = (β * β * β) * x * (β * β * β)⁻¹ := by group
      _ = x := by rw [← hb3, hβ3]; group
  obtain h0 | h1 | h2 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  · rw [h0, pow_zero] at h
    exact absurd (calc x = β⁻¹ * (β * x * β⁻¹) * β := by group
      _ = 1 := by rw [h]; group) hx1
  · rw [h1, pow_one] at h
    calc x * β = (β * x * β⁻¹) * β := by rw [h]
      _ = β * x := by group
  · rw [h2] at h
    have h4 : β * x ^ 2 * β⁻¹ = x := by
      rw [← conj_pow, h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul,
        pow_one]
    rw [h, h4, h] at hβ
    exact absurd (calc x = x ^ 2 * x⁻¹ := by group
      _ = 1 := by rw [hβ]; group) hx1

theorem preserves_zero_five_six {x β : Perm (Fin 7)} (hx3 : x ^ 3 = 1)
    (hx56 : ¬ ((x 5 = 5 ∧ x 6 = 6) ∨ (x 5 = 6 ∧ x 6 = 5)))
    (hβ5 : β 5 = 5) (hβ6 : β 6 = 6) (hβ1 : β ≠ 1) (hβx : x * β = β * x)
    (hP : ∀ p ∈ p0L, ∃ j : ℕ, ∃ p' ∈ p0L, p * x = x ^ j * p') :
    x 0 ≠ 0 ∧ ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) → (x i = 0 ∨ x i = 5 ∨ x i = 6) := by
  have hpow := pow_apply_of_pow_three hx3
  have hx3' : ∀ i, x (x (x i)) = i := fun i => by
    have h := congrArg (fun σ : Perm (Fin 7) => σ i) hx3
    simpa only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply] using h
  have hPi : ∀ p ∈ p0L, ∀ i : Fin 7, ∃ j : ℕ, ∃ p' ∈ p0L, p (x i) = (x ^ j) (p' i) := by
    intro p hp i
    obtain ⟨j, p', hp', he⟩ := hP p hp
    exact ⟨j, p', hp', by rw [← Perm.mul_apply, he, Perm.mul_apply]⟩
  have h0 : ∀ p ∈ p0L, p (x 0) = 0 ∨ p (x 0) = x 0 ∨ p (x 0) = x (x 0) := by
    intro p hp
    obtain ⟨j, p', hp', he⟩ := hPi p hp 0
    rw [he, p0L_zero hp']
    exact hpow j 0
  rcases p0L_orbit_zero h0 with h00 | h05 | h06
  ·
    exfalso
    apply hx56
    have hcomm : Commute x β := hβx
    have hβpow : ∀ (j : ℕ) (i : Fin 7), β i = i → β ((x ^ j) i) = (x ^ j) i := by
      intro j i hi
      rw [← Perm.mul_apply, ← (hcomm.pow_left j).eq, Perm.mul_apply, hi]
    have key : ∀ i : Fin 7, (i = 5 ∨ i = 6) → (x i = 5 ∨ x i = 6) := by
      intro i hi
      have hβi : β i = i := by
        rcases hi with rfl | rfl
        · exact hβ5
        · exact hβ6
      have hfix : ∀ p ∈ p0L, β (p (x i)) = p (x i) := by
        intro p hp
        obtain ⟨j, p', hp', he⟩ := hPi p hp i
        rw [he]
        apply hβpow
        rcases A7ZK.p0L_stab56 p' hp' with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
          rcases hi with rfl | rfl <;> simp only [h5, h6, hβ5, hβ6]
      have hxi0 : x i ≠ 0 := by
        intro h
        rw [← h00] at h
        have := x.injective h
        rcases hi with rfl | rfl <;> exact absurd this (by decide)
      by_contra hne
      have h14 : x i = 1 ∨ x i = 2 ∨ x i = 3 ∨ x i = 4 := by
        revert hxi0 hne
        generalize x i = a
        revert a
        decide
      apply hβ1
      refine eq_one_of_forall_ne_zero fun c hc => ?_
      by_cases hc56 : c = 5 ∨ c = 6
      · rcases hc56 with rfl | rfl
        · exact hβ5
        · exact hβ6
      · have hc14 : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
          revert hc hc56
          revert c
          decide
        obtain ⟨p, hp, hpc⟩ := p0L_trans _ _ h14 hc14
        rw [← hpc]
        exact hfix p hp
    have hne : x 5 ≠ x 6 := fun h => absurd (x.injective h) (by decide)
    rcases key 5 (Or.inl rfl) with h5 | h5 <;> rcases key 6 (Or.inr rfl) with h6 | h6
    · exact absurd (h5.trans h6.symm) hne
    · exact Or.inl ⟨h5, h6⟩
    · exact Or.inr ⟨h5, h6⟩
    · exact absurd (h5.trans h6.symm) hne
  ·
    obtain ⟨hb, hba⟩ := p0L_orbit_five (Or.inl h05) h0
    have h3 := hx3' 0
    rw [h05] at hb hba h3
    have h56 : x 5 = 6 := hb.resolve_left hba
    rw [h56] at h3
    refine ⟨by rw [h05]; decide, fun i hi => ?_⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inr (Or.inl h05)
    · exact Or.inr (Or.inr h56)
    · exact Or.inl h3
  ·
    obtain ⟨hb, hba⟩ := p0L_orbit_five (Or.inr h06) h0
    have h3 := hx3' 0
    rw [h06] at hb hba h3
    have h65 : x 6 = 5 := hb.resolve_right hba
    rw [h65] at h3
    refine ⟨by rw [h06]; decide, fun i hi => ?_⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inr (Or.inr h06)
    · exact Or.inl h3
    · exact Or.inr (Or.inl h65)

end CFSG.Quasithin.A7Std

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_orderOf_of_mem_sup {P S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) {x : G} (hx : x ∈ P ⊔ S)
    (ho : Odd (orderOf x)) : x ∈ P := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left P S hSP
  have hx' : x ∈ ((P ⊔ S : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨p, hp, s, hs, hps⟩ := hx'
  have hps' : p * s = x := hps
  subst hps'
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨q, hq, hqe⟩ := CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow hp (hSP hs) (2 ^ k)
  rw [hk', mul_one] at hqe
  have hcop : Nat.Coprime (2 ^ k) (orderOf (p * s)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [show p * s = q ^ u by rw [← hqe]; exact hu.symm]
  exact P.pow_mem hq u

theorem le_normalizer_of_stab56 {K Kh D₃ : Subgroup G} (hKKh : K ≤ Kh) (hK : ⁅K, K⁆ = K)
    (hON : pCoreOf 2 Kh ≤ Subgroup.normalizer (K : Set G))
    {e : O2Q Kh ≃* alternatingGroup (Fin 7)}
    (hr0 : (modO2Image Kh K).map e.toMonoidHom = A7Std.r0) (hD₃ : D₃ ≤ Kh)
    (h56 : ∀ d : ↥Kh, (d : G) ∈ D₃ →
      ((((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 5 = 5 ∧
          ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 6) ∨
        (((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 5 = 6 ∧
          ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 5))) :
    D₃ ≤ Subgroup.normalizer (K : Set G) := by
  have hconj : ∀ d ∈ D₃, ∀ k ∈ K, d * k * d⁻¹ ∈ K := by
    intro d hd k hk
    have hdKh : d ∈ Kh := hD₃ hd
    have hσ := A7ZK.permAct_v56 (h56 ⟨d, hdKh⟩ hd)
    refine mem_of_conj_mem_modO2Image hKKh hK hON hdKh ?_ hk
    intro k' hk'
    have hr : e (QuotientGroup.mk k') ∈ A7Std.r0 := by
      rw [← hr0]
      exact ⟨_, hk', rfl⟩
    have h1 := A7ZK.mem_r0_of_permAct_v56 hσ hr
    rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← hr0] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    rw [show x = _ from e.injective hxe] at hx
    exact hx
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact hconj d hd k
  · intro hk
    have h1 := hconj d⁻¹ (D₃.inv_mem hd) _ hk
    simpa [mul_assoc] using h1

theorem d3_stab_zero_five_six_of {T K Kh D D₃ B : Subgroup G} (hKKh : K ≤ Kh) (hK : ⁅K, K⁆ = K)
    (hON : pCoreOf 2 Kh ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T)
    (hTKh : T ≤ Subgroup.normalizer (Kh : Set G)) {e : O2Q Kh ≃* alternatingGroup (Fin 7)}
    (hr0 : (modO2Image Kh K).map e.toMonoidHom = A7Std.r0)
    (hp0 : (modO2Image Kh (T ⊓ Kh)).map e.toMonoidHom = A7Std.p0) (hDodd : Odd (Nat.card D))
    (hDT : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t')
    (hD₃ : D₃ ≤ D ⊓ Kh) (h3 : Nat.card D₃ = 3)
    (hD₃K : ¬ D₃ ≤ Subgroup.normalizer (K : Set G)) (hDK : D ⊓ Kh ≤ D₃)
    (hB3 : Nat.card B = 3) (hBK : B ≤ K) (hBD : B ≤ Subgroup.normalizer (D : Set G)) :
    (∀ d : ↥Kh, (d : G) ∈ D₃ → ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6) ∧
    ∃ d : ↥Kh, (d : G) ∈ D₃ ∧
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥Kh →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh))) with hφ
  obtain ⟨d₀, hd₀, hx56⟩ : ∃ d₀ : ↥Kh, (d₀ : G) ∈ D₃ ∧
      ¬ ((φ d₀ 5 = 5 ∧ φ d₀ 6 = 6) ∨ (φ d₀ 5 = 6 ∧ φ d₀ 6 = 5)) := by
    by_contra hall
    refine hD₃K (le_normalizer_of_stab56 hKKh hK hON hr0 (fun d hd => (hD₃ hd).2) fun d hd => ?_)
    by_contra hne
    exact hall ⟨d, hd, hne⟩
  set x := φ d₀ with hx
  have hx1 : x ≠ 1 := by
    intro h1
    apply hx56
    rw [h1]
    exact Or.inl ⟨rfl, rfl⟩
  have hd₀1 : (⟨d₀, hd₀⟩ : ↥D₃) ≠ 1 := by
    intro h1
    apply hx1
    have h2 : (d₀ : G) = 1 := by simpa using congrArg Subtype.val h1
    have h2' : d₀ = 1 := Subtype.ext h2
    rw [hx, h2', map_one]
  have hgen : ∀ y : ↥Kh, (y : G) ∈ D₃ → ∃ k : ℕ, y = d₀ ^ k := by
    intro y hy
    have htop := zpowers_eq_top_of_prime_card h3 hd₀1
    have hy' : (⟨y, hy⟩ : ↥D₃) ∈ Subgroup.zpowers (⟨d₀, hd₀⟩ : ↥D₃) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [← mem_powers_iff_mem_zpowers] at hy'
    obtain ⟨k, hk⟩ := hy'
    refine ⟨k, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow] at h1
    rw [← h1]
    simp
  have hx3 : x ^ 3 = 1 := by
    have h1 : (⟨d₀, hd₀⟩ : ↥D₃) ^ 3 = 1 := by
      rw [← h3]
      exact pow_card_eq_one'
    have h2 : d₀ ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val h1)
    rw [hx, ← map_pow, h2, map_one]
  have hP : ∀ p ∈ A7Std.p0L, ∃ j : ℕ, ∃ p' ∈ A7Std.p0L, p * x = x ^ j * p' := by
    intro p hp
    obtain ⟨g, hg, hgp⟩ := A7Std.exists_mem_p0 hp
    subst hgp
    rw [← hp0] at hg
    obtain ⟨q, ⟨t, ht, rfl⟩, hqe⟩ := hg
    have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    obtain ⟨d', hd', t', ht', he⟩ := hDT _ htT _ (hD₃ hd₀).1
    have hd'sup : d' ∈ Kh ⊔ T := by
      have h1 : d' = (t : G) * d₀ * t'⁻¹ := by rw [he]; group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Kh.mul_mem t.2 d₀.2))
        (Subgroup.mem_sup_right (T.inv_mem ht'))
    have hd'odd : Odd (orderOf d') := by
      have h1 := orderOf_dvd_natCard (⟨d', hd'⟩ : ↥D)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hDodd h1
    have hd'Kh : d' ∈ Kh := mem_of_odd_orderOf_of_mem_sup hT2 hTKh hd'sup hd'odd
    have ht'Kh : t' ∈ Kh := by
      have h1 : t' = d'⁻¹ * ((t : G) * d₀) := by rw [he]; group
      rw [h1]
      exact Kh.mul_mem (Kh.inv_mem hd'Kh) (Kh.mul_mem t.2 d₀.2)
    obtain ⟨j, hj⟩ := hgen ⟨d', hd'Kh⟩ (hDK ⟨hd', hd'Kh⟩)
    refine ⟨j, φ ⟨t', ht'Kh⟩, ?_, ?_⟩
    · have h1 : e (QuotientGroup.mk ⟨t', ht'Kh⟩) ∈ A7Std.p0 := by
        rw [← hp0]
        exact ⟨_, ⟨⟨t', ht'Kh⟩, Subgroup.mem_subgroupOf.mpr ⟨ht', ht'Kh⟩, rfl⟩, rfl⟩
      exact A7Std.mem_p0.mp h1
    · have hkh : t * d₀ = ⟨d', hd'Kh⟩ * ⟨t', ht'Kh⟩ := Subtype.ext he
      rw [hj] at hkh
      have h1 := congrArg φ hkh
      rw [map_mul, map_mul, map_pow] at h1
      rw [← hqe]
      exact h1
  have hBne : B ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hb3 : b ^ 3 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
    rw [hB3, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hbKh : b ∈ Kh := hKKh (hBK hbB)
  set bk : ↥Kh := ⟨b, hbKh⟩ with hbk
  have hbk3 : bk ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hβr : e (QuotientGroup.mk bk) ∈ A7Std.r0 := by
    rw [← hr0]
    exact ⟨_, ⟨bk, Subgroup.mem_subgroupOf.mpr (hBK hbB), rfl⟩, rfl⟩
  obtain ⟨hβ5, hβ6⟩ := (A7Std.mem_r0 _).mp hβr
  have hβ3 : φ bk ^ 3 = 1 := by rw [← map_pow, hbk3, map_one]
  have hβ1 : φ bk ≠ 1 := by
    intro h1
    have h2 : e (QuotientGroup.mk bk) = 1 := Subtype.ext h1
    have h3' : (QuotientGroup.mk bk : O2Q Kh) = 1 := by
      rw [← map_one e] at h2
      exact e.injective h2
    rw [QuotientGroup.eq_one_iff] at h3'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Kh)) ⟨bk, h3'⟩
    have e1 : bk ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf bk ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e1) (orderOf_dvd_of_pow_eq_one hbk3)
    rw [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), Nat.dvd_one,
      orderOf_eq_one_iff] at hord
    exact hb1' (congrArg Subtype.val hord)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, bk * d₀ * bk⁻¹ = d₀ ^ j := by
    refine hgen _ (hDK ⟨?_, Kh.mul_mem (Kh.mul_mem hbKh d₀.2) (Kh.inv_mem hbKh)⟩)
    exact (Subgroup.mem_normalizer_iff.mp (hBD hbB) _).mp (hD₃ hd₀).1
  have hβx : x * φ bk = φ bk * x := by
    refine A7Std.commute_of_conj_eq_pow hx3 hx1 hβ3 (j := j) ?_
    rw [hx, ← map_inv, ← map_mul, ← map_mul, hj, map_pow]
  obtain ⟨hx0, hxS⟩ := A7Std.preserves_zero_five_six hx3 hx56 hβ5 hβ6 hβ1 hβx hP
  refine ⟨fun d hd i hi => ?_, d₀, hd₀, hx0⟩
  obtain ⟨k, rfl⟩ := hgen d hd
  show φ (d₀ ^ k) i = 0 ∨ φ (d₀ ^ k) i = 5 ∨ φ (d₀ ^ k) i = 6
  rw [map_pow]
  exact A7Std.pow_apply_mem_of_forall (S := fun i => i = 0 ∨ i = 5 ∨ i = 6) hxS k i hi

end General

variable {G : Type} [Group G] [Finite G]

theorem Main513.d3_stab_zero_five_six {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}
    (h510 : Stmt5_1_10) (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hc5 : Case5_512 T H X Kh₁)
    {e : O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)}
    (hr0 : (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom = A7Std.r0)
    (hp0 : (modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map e.toMonoidHom =
      A7Std.p0)
    {D₃ : Subgroup G} (hD₃ : D₃ ≤ D ⊓ conjClosure Kh₁ T) (h3 : Nat.card D₃ = 3)
    (hD₃K : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hDK : D ⊓ conjClosure Kh₁ T ≤ D₃) :
    (∀ d : ↥(conjClosure Kh₁ T), (d : G) ∈ D₃ → ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6) ∧
    ∃ d : ↥(conjClosure Kh₁ T), (d : G) ∈ D₃ ∧
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := le_normalizer_conjClosure Kh₁ T
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hON : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    refine le_trans ?_ ((F7.isSylowTwoOf_pCoreOf_le hTY).trans hTK)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (hTKh.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hD := m.nota.2.1
  have hDT : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t' := by
    intro t ht d hd
    have hBT := Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) T
      h.T_le_normalizer_borel
    have hDL : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hD.1.trans inf_le_right
    have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDL
    have h1 : t * d ∈ ((borelL T L ⊔ T : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hD.1 hd))
    rw [hBT] at h1
    obtain ⟨y, hy, s, hs, hys⟩ := h1
    have hys' : y * s = t * d := hys
    have hy' : y ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
      rw [h.borelL_eq_sup hD]
      exact hy
    rw [hDS] at hy'
    obtain ⟨d', hd', r, hr, hdr⟩ := hy'
    have hdr' : d' * r = y := hdr
    exact ⟨d', hd', r * s, T.mul_mem (Subgroup.mem_inf.mp hr).1 hs,
      by rw [← hys', ← hdr', mul_assoc]⟩
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  rw [m.hyp.borel_eq hBorel] at hHall
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hTKs : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hB3 : Nat.card B = 3 := by
    have := (isCyclic_card_of_isHall_borelOf le_rfl hc5.1 hTKs hHall).2
    norm_num at this
    exact this
  exact d3_stab_zero_five_six_of m.lt.le hKperf hON h.sylow.1 hTKh hr0 hp0 hD.2.1 hDT hD₃ h3
    hD₃K hDK hB3 (fun b hb => (hHall.1 hb).1) m.nota.2.2

end CFSG.Quasithin.H13
