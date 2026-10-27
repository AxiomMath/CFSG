module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

namespace TableBUR

section Index

variable {M : Type*} [CommGroup M]

theorem div_mem_or_mul_mem {T W : Subgroup M} [Finite T] (hWT : W ≤ T)
    (hexp : ∀ x ∈ T, x ^ 3 = 1) (hcard : Nat.card T ≤ 3 * Nat.card W) {x y : M} (hx : x ∈ T)
    (hy : y ∈ T) (hxW : x ∉ W) (hyW : y ∉ W) : x * y⁻¹ ∈ W ∨ x * y ∈ W := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Finite.of_injective _ (Subgroup.inclusion_injective hWT)
  set W' := W.subgroupOf T with hW'
  have hmem : ∀ a : T, ((a : ↥T ⧸ W') = 1 ↔ (a : M) ∈ W) := fun a => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have heq : ∀ a b : T, ((a : ↥T ⧸ W') = (b : ↥T ⧸ W') ↔ (a : M)⁻¹ * b ∈ W) := fun a b => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  set xb : ↥T ⧸ W' := ((⟨x, hx⟩ : T) : ↥T ⧸ W') with hxb
  set yb : ↥T ⧸ W' := ((⟨y, hy⟩ : T) : ↥T ⧸ W') with hyb
  have hx1 : xb ≠ 1 := fun h => hxW ((hmem _).mp h)
  have hy1 : yb ≠ 1 := fun h => hyW ((hmem _).mp h)
  have hx3 : xb ^ 3 = 1 := by
    rw [hxb, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : T) ^ 3 = 1 := Subtype.ext (by simpa using hexp x hx)
    rw [this, QuotientGroup.mk_one]
  have hord : orderOf xb = 3 := orderOf_eq_prime hx3 hx1
  have hQ : Nat.card (↥T ⧸ W') ≤ 3 := by
    have hT := Subgroup.card_eq_card_quotient_mul_card_subgroup W'
    have hW'c : Nat.card W' = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWT).toEquiv
    have hWpos : 0 < Nat.card W := Nat.card_pos
    rw [hW'c] at hT
    nlinarith
  have htop : Subgroup.zpowers xb = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord]
    have h3 : 3 ∣ Nat.card (↥T ⧸ W') := hord ▸ orderOf_dvd_natCard xb
    have hpos : 0 < Nat.card (↥T ⧸ W') := Nat.card_pos
    omega
  have hyz : yb ∈ Subgroup.zpowers xb := htop ▸ Subgroup.mem_top yb
  rw [← mem_powers_iff_mem_zpowers] at hyz
  obtain ⟨k, hk⟩ := hyz
  dsimp only at hk
  rw [← pow_mod_orderOf, hord] at hk
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hx2 : (x ^ 2)⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hexp x hx]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · rw [h0, pow_zero] at hk
    exact absurd hk.symm hy1
  · rw [h1, pow_one, hxb, hyb, heq] at hk
    left
    have e : x * y⁻¹ = ((x : M)⁻¹ * y)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [e]
    exact W.inv_mem hk
  · rw [h2, hxb, ← QuotientGroup.mk_pow, hyb, heq] at hk
    right
    have e : ((((⟨x, hx⟩ : T) ^ 2 : T)) : M)⁻¹ * y = x * y := by
      rw [Subgroup.coe_pow, hx2]
    rw [← e]
    exact hk

end Index

theorem exists_triple_of_equivalence (r : Fin 5 → Fin 5 → Prop) (hr : Equivalence r) :
    ∃ a b c : Fin 5, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ((r a b ∧ r b c) ∨ (¬ r a b ∧ ¬ r b c ∧ ¬ r a c)) := by
  classical
  set S := (Finset.univ.erase (0 : Fin 5)).filter (r 0) with hS
  by_cases hS1 : 1 < S.card
  · obtain ⟨j, k, hj, hk, hjk⟩ := Finset.one_lt_card_iff.mp hS1
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hj hk
    exact ⟨j, 0, k, hj.1.1, Ne.symm hk.1.1, hjk, Or.inl ⟨hr.symm hj.2, hk.2⟩⟩
  · set N := (Finset.univ.erase (0 : Fin 5)) \ S with hN
    have hSsub : S ⊆ Finset.univ.erase (0 : Fin 5) := Finset.filter_subset _ _
    have hNc : N.card = 4 - S.card := by
      rw [hN, Finset.card_sdiff_of_subset hSsub, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
    have hN3 : 2 < N.card := by omega
    have hmemN : ∀ a ∈ N, a ≠ 0 ∧ ¬ r 0 a := by
      intro a ha
      rw [hN, Finset.mem_sdiff, Finset.mem_erase, hS, Finset.mem_filter, Finset.mem_erase] at ha
      exact ⟨ha.1.1, fun h => ha.2 ⟨ha.1, h⟩⟩
    obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := Finset.two_lt_card_iff.mp hN3
    obtain ⟨hj0, hj⟩ := hmemN j hj
    obtain ⟨hk0, hk⟩ := hmemN k hk
    obtain ⟨hl0, hl⟩ := hmemN l hl
    by_cases hrjk : r j k
    · by_cases hrkl : r k l
      · exact ⟨j, k, l, hjk, hkl, hjl, Or.inl ⟨hrjk, hrkl⟩⟩
      · exact ⟨0, k, l, Ne.symm hk0, hkl, Ne.symm hl0, Or.inr ⟨hk, hrkl, hl⟩⟩
    · exact ⟨0, j, k, Ne.symm hj0, hjk, Ne.symm hk0, Or.inr ⟨hj, hrjk, hk⟩⟩

section Torus

variable {K : Type} [Field K]

variable (K) in
@[expose] def torusThree (d : ℕ) : Subgroup (Fin d → Kˣ) where
  carrier := {σ | (∀ k, σ k ^ 3 = 1) ∧ ∏ k, σ k = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun k => by rw [Pi.mul_apply, mul_pow, ha k, hb k, one_mul], ?_⟩
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, ha', hb', one_mul]
  one_mem' := ⟨fun k => by rw [Pi.one_apply, one_pow], by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun k => by rw [Pi.inv_apply, inv_pow, ha k, inv_one], ?_⟩
    simp only [Pi.inv_apply, Finset.prod_inv_distrib, ha', inv_one]

theorem pow_three_of_mem_torusThree {d : ℕ} {σ : Fin d → Kˣ} (h : σ ∈ torusThree K d) :
    σ ^ 3 = 1 :=
  funext h.1

theorem card_torusThree_le [Finite K] (hK : 3 ∣ Nat.card K - 1) (m : ℕ) :
    Nat.card (torusThree K (m + 1)) ≤ 3 ^ m := by
  classical
  let f : torusThree K (m + 1) → (Fin m → rootsOfUnity 3 K) := fun σ i =>
    ⟨σ.1 i.castSucc, by rw [mem_rootsOfUnity]; exact σ.2.1 _⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hc : ∀ i : Fin m, a.1 i.castSucc = b.1 i.castSucc := fun i =>
      congrArg Subtype.val (congrFun hab i)
    have hpa := a.2.2
    have hpb := b.2.2
    rw [Fin.prod_univ_castSucc] at hpa hpb
    have hl : a.1 (Fin.last m) = b.1 (Fin.last m) := by
      have e : ∏ i : Fin m, a.1 i.castSucc = ∏ i : Fin m, b.1 i.castSucc :=
        Finset.prod_congr rfl fun i _ => hc i
      rw [e] at hpa
      exact mul_left_cancel (hpa.trans hpb.symm)
    funext k
    induction k using Fin.lastCases with
    | last => exact hl
    | cast i => exact hc i
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd Nat.prime_three hK,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at hle

section Four

variable [Finite K]

omit [Finite K] in
theorem card_units_of_four (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem exists_omega (hK : Nat.card K = 4) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [card_units_of_four hK])
  refine ⟨ω, by rw [← hω, pow_orderOf_eq_one], fun h => ?_⟩
  rw [h, orderOf_one] at hω
  exact absurd hω (by norm_num)

theorem mem_powers_omega (hK : Nat.card K = 4) {ω : Kˣ} (hω1 : ω ≠ 1) (c : Kˣ) :
    ∃ k : ℕ, ω ^ k = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 : ω ^ 3 = 1 := by
    have := pow_card_eq_one' (x := ω)
    rwa [card_units_of_four hK] at this
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have htop : Subgroup.zpowers ω = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, card_units_of_four hK])
  have hc : c ∈ Subgroup.zpowers ω := htop ▸ Subgroup.mem_top c
  rw [← mem_powers_iff_mem_zpowers] at hc
  exact hc

theorem apply_omega_ne (hK : Nat.card K = 4) {ω : Kˣ} (hω1 : ω ≠ 1) {φ : K ≃+* K}
    (hφ : φ ≠ 1) : φ (ω : K) ≠ ω := by
  intro he
  apply hφ
  ext x
  change φ x = x
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · obtain ⟨k, hk⟩ := mem_powers_omega hK hω1 (Units.mk0 x hx)
    have hxk : x = (ω : K) ^ k := by
      rw [← Units.val_pow_eq_pow_val, hk, Units.val_mk0]
    rw [hxk, map_pow, he]

end Four

end Torus

section Vectors

variable {K : Type} [Field K] {d : ℕ}

@[expose] def smv (ω : Kˣ) (m : Fin d) : Fin d → Kˣ := fun k => if k = m then ω⁻¹ else ω

@[expose] def epsv (ω : Kˣ) (a b : Fin d) : Fin d → Kˣ :=
  Pi.mulSingle a ω * Pi.mulSingle b ω⁻¹

@[expose] def triv (ω : Kˣ) (a b c : Fin d) : Fin d → Kˣ :=
  Pi.mulSingle a ω * Pi.mulSingle b ω * Pi.mulSingle c ω

theorem epsv_apply_left (ω : Kˣ) {a b : Fin d} (hab : a ≠ b) : epsv ω a b a = ω := by
  simp [epsv, hab]

theorem epsv_apply_right (ω : Kˣ) {a b : Fin d} (hab : a ≠ b) : epsv ω a b b = ω⁻¹ := by
  simp [epsv, Ne.symm hab]

theorem epsv_mul_epsv (ω : Kˣ) (a b c : Fin d) : epsv ω a b * epsv ω b c = epsv ω a c := by
  funext k
  simp only [epsv, Pi.mul_apply, Pi.mulSingle_apply]
  split_ifs <;> simp_all

theorem epsv_inv (ω : Kˣ) (a b : Fin d) : (epsv ω a b)⁻¹ = epsv ω b a := by
  funext k
  simp only [epsv, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply]
  split_ifs <;> simp_all [mul_comm]

theorem triv_apply_left (ω : Kˣ) {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) :
    triv ω a b c a = ω := by
  simp [triv, hab, hac]

theorem epsv_mem (ω : Kˣ) (hω3 : ω ^ 3 = 1) (a b : Fin d) : epsv ω a b ∈ torusThree K d := by
  classical
  refine ⟨fun k => ?_, ?_⟩
  · simp only [epsv, Pi.mul_apply, Pi.mulSingle_apply]
    split_ifs <;> simp [inv_pow, hω3]
  · simp only [epsv, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle',
      mul_inv_cancel]

theorem triv_mem (ω : Kˣ) (hω3 : ω ^ 3 = 1) (a b c : Fin d) : triv ω a b c ∈ torusThree K d := by
  classical
  refine ⟨fun k => ?_, ?_⟩
  · simp only [triv, Pi.mul_apply, Pi.mulSingle_apply]
    split_ifs <;> simp [mul_pow, hω3]
  · simp only [triv, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle',
      Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle', ← hω3, pow_succ, sq]

theorem smv_mem (ω : Kˣ) (hω3 : ω ^ 3 = 1) (m : Fin 5) : smv ω m ∈ torusThree K 5 := by
  refine ⟨fun k => ?_, ?_⟩
  · simp only [smv]
    split_ifs <;> simp [inv_pow, hω3]
  · rw [Fin.prod_univ_five]
    fin_cases m <;> simp only [smv] <;> simp <;> rw [← hω3, pow_succ, sq]

end Vectors

section Five

variable {K : Type} [Field K]

theorem smv_apply_ne (ω : Kˣ) {d : ℕ} {m k : Fin d} (h : k ≠ m) : smv ω m k = ω := by
  simp [smv, h]

theorem exists_ne_ne_five : ∀ i j : Fin 5, ∃ m : Fin 5, m ≠ i ∧ m ≠ j := by decide

theorem omega_facts {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω * ω ≠ 1 ∧ ω ≠ ω⁻¹ ∧ ω⁻¹ ^ 2 = ω ∧ ω⁻¹ * ω⁻¹ = ω ∧ ω⁻¹ * (ω * ω) = ω := by
  have h3 : ω * ω * ω = 1 := by rw [← hω3, pow_succ, sq]
  have hωω : ω * ω ≠ 1 := fun h => hω1 (by rw [h, one_mul] at h3; exact h3)
  refine ⟨hωω, fun h => hωω (by nth_rewrite 2 [h]; exact mul_inv_cancel ω), ?_, ?_, ?_⟩
  · rw [inv_pow, sq, inv_eq_iff_mul_eq_one, h3]
  · rw [← mul_inv, inv_eq_iff_mul_eq_one, h3]
  · rw [inv_mul_eq_iff_eq_mul]

theorem triv_eq_epsv_mul_sq {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {d : ℕ} {a b c : Fin d}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    triv ω a b c = epsv ω a b * epsv ω b c ^ 2 := by
  obtain ⟨-, -, hsq, -, hb⟩ := omega_facts hω3 hω1
  funext k
  simp only [triv, epsv, Pi.mul_apply, Pi.pow_apply, Pi.mulSingle_apply]
  by_cases hka : k = a
  · subst hka
    simp [hab, hac]
  by_cases hkb : k = b
  · subst hkb
    simp [hka, hbc, sq, hb]
  by_cases hkc : k = c
  · subst hkc
    simp [hka, hkb, hsq]
  · simp [hka, hkb, hkc]

theorem triv_eq_epsv_mul_inv {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {d : ℕ} {a b c : Fin d}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    triv ω a b c = epsv ω a b * (epsv ω b c)⁻¹ := by
  obtain ⟨-, -, -, hii, -⟩ := omega_facts hω3 hω1
  funext k
  simp only [triv, epsv, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply]
  by_cases hka : k = a
  · subst hka
    simp [hab, hac]
  by_cases hkb : k = b
  · subst hkb
    simp [hka, hbc, hii]
  by_cases hkc : k = c
  · subst hkc
    simp [hka, hkb]
  · simp [hka, hkb, hkc]

variable [Finite K]

theorem five_dist_triple (hK : Nat.card K = 4) {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {W : Subgroup (Fin 5 → Kˣ)} (hWT : W ≤ torusThree K 5) (hW : 27 ≤ Nat.card W)
    (hsm : ∀ m, smv ω m ∉ W) :
    (∀ i j : Fin 5, i ≠ j → ∃ σ ∈ W, σ i ≠ σ j) ∧
      ∃ a b c : Fin 5, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ triv ω a b c ∈ W := by
  classical
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]
  have hcardT : Nat.card (torusThree K 5) ≤ 3 * Nat.card W := by
    have h : Nat.card (torusThree K 5) ≤ 3 ^ 4 := card_torusThree_le hK3 4
    have h81 : (3 : ℕ) ^ 4 = 3 * 27 := by norm_num
    omega
  have hexp : ∀ x ∈ torusThree K 5, x ^ 3 = 1 := fun x hx => pow_three_of_mem_torusThree hx
  obtain ⟨hωω, hωinv, -, -, -⟩ := omega_facts hω3 hω1
  refine ⟨fun i j hij => ?_, ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨m, hmi, hmj⟩ := exists_ne_ne_five i j
    have hy : epsv ω i j ∉ W := fun h => hωinv (by
      have := hne _ h
      rwa [epsv_apply_left ω hij, epsv_apply_right ω hij] at this)
    rcases div_mem_or_mul_mem hWT hexp hcardT (smv_mem ω hω3 m) (epsv_mem ω hω3 i j) (hsm m) hy
      with h | h
    · have := hne _ h
      simp only [Pi.mul_apply, Pi.inv_apply, smv_apply_ne ω (Ne.symm hmi),
        smv_apply_ne ω (Ne.symm hmj), epsv_apply_left ω hij, epsv_apply_right ω hij, inv_inv,
        mul_inv_cancel] at this
      exact hωω this.symm
    · have := hne _ h
      simp only [Pi.mul_apply, smv_apply_ne ω (Ne.symm hmi), smv_apply_ne ω (Ne.symm hmj),
        epsv_apply_left ω hij, epsv_apply_right ω hij, mul_inv_cancel] at this
      exact hωω this
  · set r : Fin 5 → Fin 5 → Prop := fun a b => a = b ∨ epsv ω a b ∈ W with hr
    have hreq : Equivalence r := by
      refine ⟨fun a => Or.inl rfl, fun {a b} h => ?_, fun {a b c} hab hbc => ?_⟩
      · rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [← epsv_inv]; exact W.inv_mem h)
      · rcases hab with rfl | hab
        · exact hbc
        rcases hbc with rfl | hbc
        · exact Or.inr hab
        exact Or.inr (by rw [← epsv_mul_epsv ω a b c]; exact W.mul_mem hab hbc)
    obtain ⟨a, b, c, hab, hbc, hac, hcase⟩ := exists_triple_of_equivalence r hreq
    refine ⟨a, b, c, hab, hbc, hac, ?_⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [triv_eq_epsv_mul_sq hω3 hω1 hab hbc hac]
      exact W.mul_mem (h1.resolve_left hab) (W.pow_mem (h2.resolve_left hbc) 2)
    · have h1' : epsv ω a b ∉ W := fun h => h1 (Or.inr h)
      have h2' : epsv ω b c ∉ W := fun h => h2 (Or.inr h)
      rcases div_mem_or_mul_mem hWT hexp hcardT (epsv_mem ω hω3 a b) (epsv_mem ω hω3 b c) h1' h2'
        with h | h
      · rw [triv_eq_epsv_mul_inv hω3 hω1 hab hbc hac]
        exact h
      · rw [epsv_mul_epsv] at h
        exact absurd (Or.inr h) h3

end Five

end TableBUR

end CFSG.StandardType
