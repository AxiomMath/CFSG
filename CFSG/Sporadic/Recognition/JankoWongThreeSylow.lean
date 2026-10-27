module

public import CFSG.Sporadic.Recognition.JankoWongThreeLocal

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem fix_of_commute_cube {α : Type*} {σ τ : Perm α} (hσ : σ ^ 3 = 1) {a : α} (ha : σ a ≠ a)
    (hc : τ * σ = σ * τ) (horb : ∃ j : ℕ, τ a = (σ ^ j) a) {m : ℕ} (hm : τ ^ (2 ^ m) = 1) :
    τ a = a := by
  obtain ⟨j, hj⟩ := horb
  have hcomm : ∀ (i k : ℕ), (τ ^ k) ((σ ^ i) a) = (σ ^ i) ((τ ^ k) a) := by
    intro i k
    have hik : τ ^ k * σ ^ i = σ ^ i * τ ^ k := by
      have : Commute τ σ := hc
      exact (this.pow_pow k i).eq
    have := congrArg (fun p : Perm α => p a) hik
    simpa using this
  have hτk : ∀ k : ℕ, (τ ^ k) a = (σ ^ (j * k)) a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_apply, hj, hcomm j k, ih, ← mul_apply, ← pow_add]
      congr 2; ring
  have h1 : (σ ^ (j * 2 ^ m)) a = a := by
    have := hτk (2 ^ m)
    rw [hm] at this
    simpa using this.symm
  have hσa : ∀ n : ℕ, (σ ^ n) a = a → 3 ∣ n := by
    intro n hn
    by_contra hn3
    have hr : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hpow : σ ^ n = σ ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hσ, one_pow, one_mul]
    rw [hpow] at hn
    rcases hr with hr | hr
    · rw [hr] at hn; simp at hn; exact ha hn
    · rw [hr] at hn
      have : σ ((σ ^ 2) a) = σ a := by rw [hn]
      have h3 : (σ ^ 3) a = σ a := by
        have := this
        simpa [pow_succ, mul_apply] using this
      rw [hσ] at h3
      exact ha h3.symm
  have h3j : 3 ∣ j := by
    have := hσa _ h1
    have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨j', rfl⟩ := h3j
  rw [hj, pow_mul, hσ, one_pow]
  rfl


@[expose] def permA3 : Perm (Fin 8) := swap 0 1 * swap 1 2
@[expose] def permB3 : Perm (Fin 8) := swap 3 4 * swap 4 5

theorem permA3_cube : permA3 ^ 3 = 1 := by unfold permA3; decide
theorem permB3_cube : permB3 ^ 3 = 1 := by unfold permB3; decide
theorem permA3_comm_permB3 : permA3 * permB3 = permB3 * permA3 := by
  unfold permA3 permB3; decide

private theorem fix_aux {γ σ : Perm (Fin 8)} (hσ : σ ^ 3 = 1) {a b c : Fin 8}
    (h1 : σ a = b) (h2 : σ b = c) (hab : a ≠ b)
    (hfix : ∀ k, k ≠ a → k ≠ b → k ≠ c → σ k = k)
    (hc : γ * σ = σ * γ) {m : ℕ} (hm : γ ^ (2 ^ m) = 1) : γ a = a := by
  have hcomm : ∀ x, γ (σ x) = σ (γ x) := fun x => by
    have := congrArg (fun p : Perm (Fin 8) => p x) hc
    simpa using this
  have hmem : γ a = a ∨ γ a = b ∨ γ a = c := by
    by_contra hne
    push Not at hne
    obtain ⟨hna, hnb, hnc⟩ := hne
    have hfx := hfix (γ a) hna hnb hnc
    have : γ (σ a) = γ a := by rw [hcomm, hfx]
    rw [h1] at this
    exact hab (γ.injective this).symm
  have horb : ∃ j : ℕ, γ a = (σ ^ j) a := by
    rcases hmem with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h, h1]⟩
    · exact ⟨2, by simp [h, pow_two, h1, h2]⟩
  exact fix_of_commute_cube hσ (by rw [h1]; exact hab.symm) hc horb hm

theorem eq_one_of_commute_permA3_permB3 {γ : Perm (Fin 8)} (hA : γ * permA3 = permA3 * γ)
    (hB : γ * permB3 = permB3 * γ) (hs : sign γ = 1) {m : ℕ} (hm : γ ^ (2 ^ m) = 1) :
    γ = 1 := by
  have hcA : ∀ x, γ (permA3 x) = permA3 (γ x) := fun x => by
    have := congrArg (fun p : Perm (Fin 8) => p x) hA
    simpa using this
  have hcB : ∀ x, γ (permB3 x) = permB3 (γ x) := fun x => by
    have := congrArg (fun p : Perm (Fin 8) => p x) hB
    simpa using this
  have h0 : γ 0 = 0 := fix_aux (σ := permA3) permA3_cube (a := 0) (b := 1) (c := 2)
    (by unfold permA3; decide) (by unfold permA3; decide)
    (by decide) (by unfold permA3; decide) hA hm
  have h3 : γ 3 = 3 := fix_aux (σ := permB3) permB3_cube (a := 3) (b := 4) (c := 5)
    (by unfold permB3; decide) (by unfold permB3; decide)
    (by decide) (by unfold permB3; decide) hB hm
  have h1 : γ 1 = 1 := by
    have := hcA 0
    have e : permA3 0 = 1 := by unfold permA3; decide
    rw [e, h0] at this
    rw [this]; exact e
  have h2 : γ 2 = 2 := by
    have := hcA 1
    have e : permA3 1 = 2 := by unfold permA3; decide
    rw [e, h1] at this
    rw [this]; exact e
  have h4 : γ 4 = 4 := by
    have := hcB 3
    have e : permB3 3 = 4 := by unfold permB3; decide
    rw [e, h3] at this
    rw [this]; exact e
  have h5 : γ 5 = 5 := by
    have := hcB 4
    have e : permB3 4 = 5 := by unfold permB3; decide
    rw [e, h4] at this
    rw [this]; exact e
  have hlow : ∀ x : Fin 8, x.val < 6 → γ x = x := by
    intro x hx
    have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
      fin_cases x <;> simp_all
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have h6 : γ 6 = 6 := by
    have hne : (γ 6).val ≥ 6 := by
      by_contra hlt
      push Not at hlt
      have e := γ.injective (hlow (γ 6) hlt)
      rw [e] at hlt
      exact absurd hlt (by decide)
    have h67 : γ 6 = 6 ∨ γ 6 = 7 := by
      have : (γ 6).val ≤ 7 := by omega
      have h8 : (γ 6).val = 6 ∨ (γ 6).val = 7 := by omega
      rcases h8 with h8 | h8
      · left; exact Fin.ext h8
      · right; exact Fin.ext h8
    rcases h67 with h | h
    · exact h
    · exfalso
      have h7 : γ 7 = 6 := by
        have hne7 : (γ 7).val ≥ 6 := by
          by_contra hlt
          push Not at hlt
          have e := γ.injective (hlow (γ 7) hlt)
          rw [e] at hlt
          exact absurd hlt (by decide)
        have : γ 7 ≠ 7 := fun e => by
          have := γ.injective (h.trans e.symm)
          exact absurd this (by decide)
        have h8 : (γ 7).val = 6 ∨ (γ 7).val = 7 := by omega
        rcases h8 with h8 | h8
        · exact Fin.ext h8
        · exact absurd (Fin.ext h8) this
      have hγ : γ = swap 6 7 := by
        ext x
        by_cases hx : x.val < 6
        · rw [hlow x hx, swap_apply_of_ne_of_ne]
          · intro e; rw [e] at hx; simp at hx
          · intro e; rw [e] at hx; simp at hx
        · have : x = 6 ∨ x = 7 := by
            fin_cases x <;> simp_all
          rcases this with rfl | rfl
          · rw [h]; simp
          · rw [h7]; simp
      rw [hγ, sign_swap (by decide)] at hs
      exact absurd hs (by decide)
  have h7 : γ 7 = 7 := by
    have hne7 : (γ 7).val ≥ 6 := by
      by_contra hlt
      push Not at hlt
      have e := γ.injective (hlow (γ 7) hlt)
      rw [e] at hlt
      exact absurd hlt (by decide)
    have : γ 7 ≠ 6 := fun e => by
      have := γ.injective (h6.trans e.symm)
      exact absurd this (by decide)
    have h8 : (γ 7).val = 6 ∨ (γ 7).val = 7 := by omega
    rcases h8 with h8 | h8
    · exact absurd (Fin.ext h8) this
    · exact Fin.ext h8
  ext x
  fin_cases x <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]


theorem cycleType_permA3 : permA3.cycleType = {3} := by
  unfold permA3
  exact cycleType_type3_of_card (by decide) (by decide)

theorem cycleType_permB3 : permB3.cycleType = {3} := by
  unfold permB3
  exact cycleType_type3_of_card (by decide) (by decide)

theorem cycleType_permA3B3 : (permA3 * permB3).cycleType = {3, 3} := by
  unfold permA3 permB3
  exact cycleType_type33_of_card (by decide) (by decide)

theorem permA3_ne_one : permA3 ≠ 1 := by
  intro e
  have := cycleType_permA3
  rw [e, cycleType_one] at this
  simp at this

theorem permB3_ne_one : permB3 ≠ 1 := by
  intro e
  have := cycleType_permB3
  rw [e, cycleType_one] at this
  simp at this

theorem factorization_three_360 : (360 : ℕ).factorization 3 = 2 := by
  have : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  have h40 : (40 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h40]

namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem exists_std_sylow3 (S : Setup G) :
    ∃ (a b : S.H) (P : Subgroup S.H), S.ρ a = permA3 ∧ S.ρ b = permB3 ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a * b = b * a ∧ IsPGroup 3 P ∧ Nat.card P = 9 ∧ a ∈ P ∧ b ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, ha3⟩ := S.cover.exists_lift_cube_one (p := permA3)
    (sign_of_type3 cycleType_permA3) permA3_cube
  obtain ⟨b, hb, hb3⟩ := S.cover.exists_lift_cube_one (p := permB3)
    (sign_of_type3 cycleType_permB3) permB3_cube
  have hab : a * b = b * a :=
    (S.cover.commute_of_cube ha3 (by rw [ha, hb]; exact permA3_comm_permB3.symm)).symm
  have hcard := S.cover.card_centralizer_type3 ha3 (by rw [ha]; exact cycleType_permA3)
  set C : Subgroup S.H := centralizer ({a} : Set S.H) with hC
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hab.symm
  set a' : C := ⟨a, haC⟩ with ha'
  set b' : C := ⟨b, hbC⟩ with hb'
  have hb'p : IsPGroup 3 ↥(zpowers b') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hb3 (fun e => permB3_ne_one (by rw [← hb, e, map_one]))
  obtain ⟨Q, hQ⟩ := hb'p.exists_le_sylow
  have ha'p : IsPGroup 3 ↥(zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 (fun e => permA3_ne_one (by rw [← ha, e, map_one]))
  have hcenter : zpowers a' ≤ Subgroup.center C := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have : (zpowers a').Normal := Subgroup.normal_of_le_center hcenter
  have haQ : a' ∈ (Q : Subgroup C) := ha'p.le_sylow_of_normal Q (Subgroup.mem_zpowers a')
  have hbQ : b' ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers b')
  refine ⟨a, b, (Q : Subgroup C).map C.subtype, ha, hb, ha3, hb3, hab,
    Q.isPGroup'.map C.subtype, ?_, ⟨a', haQ, rfl⟩, ⟨b', hbQ, rfl⟩⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective, Q.card_eq_multiplicity, hcard,
    factorization_three_360]
  norm_num

end Setup


theorem sylow_conj_mem {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (Q₁ Q₂ : Sylow p K) :
    ∃ g : K, ∀ x : K, x ∈ (Q₂ : Subgroup K) ↔ g⁻¹ * x * g ∈ (Q₁ : Subgroup K) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q₁ Q₂
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

theorem card_le_nine_of_not_dvd {G : Type*} [Group G] [Finite G] (h27 : ¬ 27 ∣ Nat.card G)
    {R : Subgroup G} (hR : IsPGroup 3 R) : Nat.card R ≤ 9 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hdvd : Nat.card R ∣ Nat.card G := Subgroup.card_subgroup_dvd_card R
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k <;> simp at hlt
  exact h27 ((pow_dvd_pow 3 hk3).trans hdvd)

theorem exists_sylow_of_card_nine {G : Type*} [Group G] [Finite G] {C A : Subgroup G}
    (hA : IsPGroup 3 A) (hAC : A ≤ C) (hA9 : Nat.card A = 9)
    (hbound : ∀ R : Subgroup G, IsPGroup 3 R → Nat.card R ≤ 9) :
    ∃ Q : Sylow 3 ↥C, (Q : Subgroup C) = A.subgroupOf C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA' : IsPGroup 3 ↥(A.subgroupOf C) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  have hA'card : Nat.card (A.subgroupOf C) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA9]
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  have hQG : IsPGroup 3 ↥((Q : Subgroup C).map C.subtype) := Q.isPGroup'.map C.subtype
  have := hbound _ hQG
  rw [Subgroup.card_map_of_injective C.subtype_injective] at this
  omega

namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_z_of_two_power_commute (S : Setup G) {a b g : S.H} (ha : S.ρ a = permA3)
    (hb : S.ρ b = permB3) (hga : g * a = a * g) (hgb : g * b = b * g) {m : ℕ}
    (hm : g ^ (2 ^ m) = 1) : g = 1 ∨ g = zIn S.z := by
  have hA : S.ρ g * permA3 = permA3 * S.ρ g := by rw [← ha, ← map_mul, ← map_mul, hga]
  have hB : S.ρ g * permB3 = permB3 * S.ρ g := by rw [← hb, ← map_mul, ← map_mul, hgb]
  have hs := S.cover.sign_rho g
  have hm' : S.ρ g ^ (2 ^ m) = 1 := by rw [← map_pow, hm, map_one]
  exact S.cover.mem_ker_iff.mp (eq_one_of_commute_permA3_permB3 hA hB hs hm')


theorem mem_H_of_commute (S : Setup G) {c u y : G} (hc : c * S.z * c⁻¹ = u) (hy : y * u = u * y) :
    c⁻¹ * y * c ∈ S.H := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc c⁻¹ * y * c * S.z = c⁻¹ * y * (c * S.z * c⁻¹) * c := by group
    _ = c⁻¹ * (y * u) * c := by rw [hc]; group
    _ = c⁻¹ * (u * y) * c := by rw [hy]
    _ = S.z * (c⁻¹ * y * c) := by rw [← hc]; group

theorem exists_abelian_three_group (S : Setup G) {x t : S.H} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htc : t * x = x * t) :
    ∃ X : Subgroup G, IsPGroup 3 X ∧ Nat.card X = 9 ∧ (x : G) ∈ X ∧
      (∀ u ∈ X, ∀ v ∈ X, u * v = v * u) ∧ ∀ u ∈ X, u * (t : G) = (t : G) * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext e)
  have htG2 : (t : G) ^ 2 = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have htG1 : (t : G) ≠ 1 := fun e => ht1 (Subtype.ext e)
  have htGcomm : (t : G) * (x : G) = (x : G) * (t : G) := congrArg Subtype.val htc
  have hcard : Nat.card (centralizer ({(t : G)} : Set G)) = 40320 := by
    have hconj : IsConj (t : G) S.z := S.oneClass _ _ (orderOf_eq_prime htG2 htG1) S.order_z
    rw [card_centralizer_eq_of_isConj hconj]
    exact S.card_H
  have hxC : (x : G) ∈ centralizer ({(t : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htGcomm.symm
  have hxp : IsPGroup 3 ↥(zpowers (⟨(x : G), hxC⟩ : centralizer ({(t : G)} : Set G))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxG3 hx1'
  obtain ⟨X, hX⟩ := hxp.exists_le_sylow
  have hXcard : Nat.card X = 3 ^ 2 := by
    rw [X.card_eq_multiplicity, hcard, factorization_three_40320]
  have hXcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hXcard
  set XG : Subgroup G := (X : Subgroup (centralizer ({(t : G)} : Set G))).map
    (centralizer ({(t : G)} : Set G)).subtype with hXG
  have hxX : (⟨(x : G), hxC⟩ : centralizer ({(t : G)} : Set G)) ∈ (X : Subgroup _) :=
    hX (Subgroup.mem_zpowers _)
  refine ⟨XG, X.isPGroup'.map _, ?_, ⟨_, hxX, rfl⟩, ?_, ?_⟩
  · rw [hXG, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hXcard]; norm_num
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    have h2 := hXcomm.is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩
    exact congrArg (fun w : ↥(X : Subgroup (centralizer ({(t : G)} : Set G))) => (w.1 : G)) h2
  · rintro _ ⟨c, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2


omit [Finite G] in
theorem exists_pow_two_eq_one_of_mem {T : Subgroup G} (hT : IsPGroup 2 T) {y : G} (hy : y ∈ T) :
    ∃ m : ℕ, y ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hy⟩
  refine ⟨m, ?_⟩
  have h1 : (⟨y, hy⟩ : T) ^ (2 ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  exact congrArg Subtype.val h1

theorem card_le_two_of_centralizes (S : Setup G) (h27 : ¬ 27 ∣ Nat.card G)
    {a b : S.H} {P : Subgroup S.H} (ha : S.ρ a = permA3) (hb : S.ρ b = permB3)
    (hP : IsPGroup 3 P) (hP9 : Nat.card P = 9) (haP : a ∈ P) (hbP : b ∈ P)
    {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTP : ∀ y ∈ T, ∀ p ∈ P, y * (p : G) = (p : G) * y) : Nat.card T ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hbot : T = ⊥
  · rw [hbot]; simp
  obtain ⟨u, huT, hu2, hucent⟩ := exists_central_involution hT hbot
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.oneClass S.z u S.order_z hu2)
  have key : ∀ y : G, y * u = u * y → c⁻¹ * y * c ∈ S.H := fun y hy => S.mem_H_of_commute hc hy
  set PG : Subgroup G := P.map S.H.subtype with hPG
  have hPGp : IsPGroup 3 PG := hP.map _
  have hPG9 : Nat.card PG = 9 := by
    rw [hPG, Subgroup.card_map_of_injective S.H.subtype_injective, hP9]
  let cc : G ≃* G := MulAut.conj c⁻¹
  set Q : Subgroup G := PG.map cc.toMonoidHom with hQ
  have hQp : IsPGroup 3 Q := hPGp.map _
  have hQ9 : Nat.card Q = 9 := by
    rw [hQ, Subgroup.card_map_of_injective cc.injective, hPG9]
  have hQH : Q ≤ S.H := by
    rintro _ ⟨_, ⟨p', hp', rfl⟩, rfl⟩
    show c⁻¹ * (p' : G) * c⁻¹⁻¹ ∈ S.H
    rw [inv_inv]
    exact key _ (hTP u huT p' hp').symm
  have hbound : ∀ R : Subgroup G, IsPGroup 3 R → Nat.card R ≤ 9 := fun R hR =>
    card_le_nine_of_not_dvd h27 hR
  have hPGH : PG ≤ S.H := Subgroup.map_subtype_le P
  obtain ⟨Q_P, hQ_P⟩ := exists_sylow_of_card_nine hPGp hPGH hPG9 hbound
  obtain ⟨Q_Q, hQ_Q⟩ := exists_sylow_of_card_nine hQp hQH hQ9 hbound
  obtain ⟨h, hh⟩ := sylow_conj_mem Q_P Q_Q
  have hPmem : ∀ x : S.H, x ∈ P ↔ x ∈ (Q_P : Subgroup S.H) := by
    intro x
    rw [hQ_P, Subgroup.mem_subgroupOf, hPG]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨x', hx', e⟩ => by
      have : x' = x := Subtype.ext e
      rwa [← this]⟩
  have hQmem : ∀ x : S.H, x ∈ (Q_Q : Subgroup S.H) ↔ (x : G) ∈ Q := by
    intro x
    rw [hQ_Q, Subgroup.mem_subgroupOf]
  have hsub : ∀ y ∈ T, y = 1 ∨ y = u := by
    intro y hyT
    obtain ⟨m, hm⟩ := exists_pow_two_eq_one_of_mem hT hyT
    have hyH : c⁻¹ * y * c ∈ S.H := key y (hucent y hyT)
    set y' : S.H := ⟨c⁻¹ * y * c, hyH⟩ with hy'
    have hy'Q : ∀ q ∈ Q, (y' : G) * q = q * y' := by
      rintro _ ⟨_, ⟨p', hp', rfl⟩, rfl⟩
      show c⁻¹ * y * c * (c⁻¹ * (p' : G) * c⁻¹⁻¹) = c⁻¹ * (p' : G) * c⁻¹⁻¹ * (c⁻¹ * y * c)
      rw [inv_inv]
      calc c⁻¹ * y * c * (c⁻¹ * (p' : G) * c) = c⁻¹ * (y * p') * c := by group
        _ = c⁻¹ * (p' * y) * c := by rw [hTP y hyT p' hp']
        _ = c⁻¹ * (p' : G) * c * (c⁻¹ * y * c) := by group
    have hcomm : ∀ p ∈ P, (h⁻¹ * y' * h) * p = p * (h⁻¹ * y' * h) := by
      intro p hp
      have hx : h * p * h⁻¹ ∈ (Q_Q : Subgroup S.H) := by
        rw [hh]
        have e : h⁻¹ * (h * p * h⁻¹) * h = p := by group
        rw [e]; exact (hPmem p).mp hp
      have := hy'Q _ ((hQmem _).mp hx)
      apply Subtype.ext
      have h2 : (y' : G) * ((h * p * h⁻¹ : S.H) : G) = ((h * p * h⁻¹ : S.H) : G) * y' := this
      calc ((h⁻¹ * y' * h : S.H) : G) * (p : G)
          = ((h⁻¹ : S.H) : G) * ((y' : G) * ((h * p * h⁻¹ : S.H) : G)) * (h : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = ((h⁻¹ : S.H) : G) * (((h * p * h⁻¹ : S.H) : G) * y') * (h : G) := by rw [h2]
        _ = (p : G) * ((h⁻¹ * y' * h : S.H) : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have hg : (h⁻¹ * y' * h) ^ (2 ^ m) = 1 := by
      have : (h⁻¹ * y' * h) ^ (2 ^ m) = h⁻¹ * y' ^ (2 ^ m) * h := by
        simpa using conj_pow (a := h⁻¹) (b := y') (i := 2 ^ m)
      rw [this]
      have : y' ^ (2 ^ m) = 1 := by
        apply Subtype.ext
        show (c⁻¹ * y * c) ^ (2 ^ m) = 1
        have e : (c⁻¹ * y * c) ^ (2 ^ m) = c⁻¹ * y ^ (2 ^ m) * c := by
          simpa using conj_pow (a := c⁻¹) (b := y) (i := 2 ^ m)
        rw [e, hm]; simp
      rw [this]; simp
    have hga : (h⁻¹ * y' * h) * a = a * (h⁻¹ * y' * h) := hcomm a haP
    have hgb : (h⁻¹ * y' * h) * b = b * (h⁻¹ * y' * h) := hcomm b hbP
    rcases S.eq_one_or_eq_z_of_two_power_commute ha hb hga hgb hg with h1 | h1
    · left
      have : y' = 1 := by
        have := congrArg (fun w => h * w * h⁻¹) h1
        simpa [mul_assoc] using this
      have h2 : c⁻¹ * y * c = 1 := congrArg Subtype.val this
      calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · right
      have h3 : y' = h * zIn S.z * h⁻¹ := by
        have := congrArg (fun w => h * w * h⁻¹) h1
        simpa [mul_assoc] using this
      have h4 : (y' : G) = S.z := by
        rw [h3]
        have hz : (h : G) * S.z = S.z * (h : G) := Subgroup.mem_centralizer_singleton_iff.mp h.2
        show (h : G) * S.z * (h : G)⁻¹ = S.z
        rw [hz]; group
      have h5 : c⁻¹ * y * c = S.z := h4
      calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
        _ = u := by rw [h5, hc]
  calc Nat.card T = (T : Set G).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ({1, u} : Set G).ncard := Set.ncard_le_ncard (fun y hy => by
        rcases hsub y hy with rfl | rfl <;> simp) (Set.toFinite _)
    _ ≤ 2 := by
        refine (Set.ncard_insert_le 1 {u}).trans ?_
        simp


omit [Finite G] in
theorem mem_zpowers_involution {g x : G} (hg : g ^ 2 = 1) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left; rw [zpow_mul, zpow_two, ← pow_two, hg, one_zpow]
  · right; rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hg, one_zpow, one_mul, zpow_one]

theorem exists_sylow_of_card_two {K A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hA2 : Nat.card A = 2)
    (hbound : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ K → Nat.card R ≤ 2) :
    ∃ Q : Sylow 2 ↥K, (Q : Subgroup K) = A.subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 ↥(A.subgroupOf K) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hA'card : Nat.card (A.subgroupOf K) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA2]
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  have hQG : IsPGroup 2 ↥((Q : Subgroup K).map K.subtype) := Q.isPGroup'.map K.subtype
  have hQK : (Q : Subgroup K).map K.subtype ≤ K := by
    rintro _ ⟨c, -, rfl⟩; exact c.2
  have := hbound _ hQG hQK
  rw [Subgroup.card_map_of_injective K.subtype_injective] at this
  omega

theorem exists_conj_centralizing (S : Setup G) (h27 : ¬ 27 ∣ Nat.card G)
    {a b : S.H} {P : Subgroup S.H} (ha : S.ρ a = permA3) (hb : S.ρ b = permB3)
    (hP : IsPGroup 3 P) (hP9 : Nat.card P = 9) (haP : a ∈ P) (hbP : b ∈ P)
    {t' : G} (ht'2 : t' ^ 2 = 1) (ht'1 : t' ≠ 1)
    (hcomm : ∀ p ∈ P, (p : G) * t' = t' * (p : G)) :
    ∃ d : G, (∀ p ∈ P, (p : G) * d = d * (p : G)) ∧ d * t' * d⁻¹ = S.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set PG : Subgroup G := P.map S.H.subtype with hPG
  set K : Subgroup G := centralizer (PG : Set G) with hK
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have hzK : S.z ∈ K := by
    rw [hK, Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp p.2
  have ht'K : t' ∈ K := by
    rw [hK, Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    exact hcomm p hp
  have hbound : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ K → Nat.card R ≤ 2 := by
    intro R hR hRK
    exact S.card_le_two_of_centralizes h27 ha hb hP hP9 haP hbP hR (fun y hy p hp =>
      (Subgroup.mem_centralizer_iff.mp (hRK hy) _ ⟨p, hp, rfl⟩).symm)
  have hcard2 : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → Nat.card (zpowers g) = 2 := fun g hg2 hg1 => by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hg2 hg1
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_of_card_two (K := K) (isPGroup_two_zpowers ht'2)
    (Subgroup.zpowers_le.mpr ht'K) (hcard2 t' ht'2 ht'1) hbound
  obtain ⟨Q₂, hQ₂⟩ := exists_sylow_of_card_two (K := K) (isPGroup_two_zpowers hz2)
    (Subgroup.zpowers_le.mpr hzK) (hcard2 S.z hz2 hz1) hbound
  obtain ⟨g, hg⟩ := sylow_conj_mem Q₁ Q₂
  have hzmem : (⟨S.z, hzK⟩ : K) ∈ (Q₂ : Subgroup K) := by
    rw [hQ₂, Subgroup.mem_subgroupOf]; exact Subgroup.mem_zpowers _
  have h1 := (hg _).mp hzmem
  rw [hQ₁, Subgroup.mem_subgroupOf] at h1
  have h2 : (g : G)⁻¹ * S.z * (g : G) = 1 ∨ (g : G)⁻¹ * S.z * (g : G) = t' :=
    mem_zpowers_involution ht'2 h1
  have h3 : (g : G)⁻¹ * S.z * (g : G) ≠ 1 := fun e => hz1 (by
    have : S.z = (g : G) * ((g : G)⁻¹ * S.z * (g : G)) * (g : G)⁻¹ := by group
    rw [this, e]; group)
  have h4 : (g : G)⁻¹ * S.z * (g : G) = t' := h2.resolve_left h3
  refine ⟨(g : G), ?_, ?_⟩
  · intro p hp
    exact Subgroup.mem_centralizer_iff.mp g.2 _ ⟨p, hp, rfl⟩
  · rw [← h4]; group


theorem exists_conj_to_z (S : Setup G) (h27 : ¬ 27 ∣ Nat.card G)
    {a b : S.H} {P : Subgroup S.H} (ha : S.ρ a = permA3) (hb : S.ρ b = permB3)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hP : IsPGroup 3 P) (hP9 : Nat.card P = 9) (haP : a ∈ P) (hbP : b ∈ P)
    {t : S.H} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htc : t * (a * b) = (a * b) * t) :
    ∃ e : G, e * ((a * b : S.H) : G) = ((a * b : S.H) : G) * e ∧ e * S.z * e⁻¹ = (t : G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : S.H := a * b with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, Commute.mul_pow hab, ha3, hb3, one_mul]
  have hxty : (S.ρ x).cycleType = {3, 3} := by
    rw [hx, map_mul, ha, hb]; exact cycleType_permA3B3
  have hx1 : x ≠ 1 := fun e => by
    rw [e, map_one, cycleType_one] at hxty
    simp at hxty
  have hPcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P) (by
    rw [hP9]; norm_num)
  have hxP : x ∈ P := P.mul_mem haP hbP
  have hPx : ∀ p ∈ P, p * x = x * p := fun p hp => by
    have := hPcomm.is_comm.comm ⟨p, hp⟩ ⟨x, hxP⟩
    exact congrArg Subtype.val this
  obtain ⟨XG, hXp, hX9, hxX, hXab, hXt⟩ := S.exists_abelian_three_group hx3 hx1 ht2 ht1 htc
  set xG : G := (x : G) with hxG
  set C : Subgroup G := centralizer ({xG} : Set G) with hC
  set PG : Subgroup G := P.map S.H.subtype with hPG
  have hPGp : IsPGroup 3 PG := hP.map _
  have hPG9 : Nat.card PG = 9 := by
    rw [hPG, Subgroup.card_map_of_injective S.H.subtype_injective, hP9]
  have hPGC : PG ≤ C := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hPx p hp)
  have hXC : XG ≤ C := fun u hu => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hXab u hu xG hxX
  have hbound : ∀ R : Subgroup G, IsPGroup 3 R → Nat.card R ≤ 9 := fun R hR =>
    card_le_nine_of_not_dvd h27 hR
  obtain ⟨Q_P, hQ_P⟩ := exists_sylow_of_card_nine hPGp hPGC hPG9 hbound
  obtain ⟨Q_X, hQ_X⟩ := exists_sylow_of_card_nine hXp hXC hX9 hbound
  obtain ⟨g, hg⟩ := sylow_conj_mem Q_P Q_X
  set c : G := (g : G) with hc
  have hcC : c * xG = xG * c := Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hcinv : c⁻¹ * xG = xG * c⁻¹ := by
    calc c⁻¹ * xG = c⁻¹ * (xG * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * xG) * c⁻¹ := by rw [hcC]
      _ = xG * c⁻¹ := by group
  have hconjP : ∀ p ∈ PG, c * p * c⁻¹ ∈ XG := by
    intro p hp
    have hpC : p ∈ C := hPGC hp
    have h1 : (⟨c * p * c⁻¹, by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have hpx := Subgroup.mem_centralizer_singleton_iff.mp hpC
      calc c * p * c⁻¹ * xG = c * p * (c⁻¹ * xG) := by group
        _ = c * p * (xG * c⁻¹) := by rw [hcinv]
        _ = c * (p * xG) * c⁻¹ := by group
        _ = c * (xG * p) * c⁻¹ := by rw [hpx]
        _ = xG * (c * p * c⁻¹) := by
            calc c * (xG * p) * c⁻¹ = (c * xG) * p * c⁻¹ := by group
              _ = (xG * c) * p * c⁻¹ := by rw [hcC]
              _ = xG * (c * p * c⁻¹) := by group⟩ : C) ∈ (Q_X : Subgroup C) := by
      rw [hg, hQ_P, Subgroup.mem_subgroupOf]
      have e : (g : G)⁻¹ * (c * p * c⁻¹) * (g : G) = p := by rw [hc]; group
      show (g : G)⁻¹ * (c * p * c⁻¹) * (g : G) ∈ PG
      rw [e]; exact hp
    rw [hQ_X, Subgroup.mem_subgroupOf] at h1
    exact h1
  set tG : G := (t : G) with htG
  have htG2 : tG ^ 2 = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have htG1 : tG ≠ 1 := fun e => ht1 (Subtype.ext e)
  set t' : G := c⁻¹ * tG * c with ht'
  have ht'2 : t' ^ 2 = 1 := by
    have : t' ^ 2 = c⁻¹ * tG ^ 2 * c := by
      rw [ht', pow_two, pow_two]; simp [mul_assoc]
    rw [this, htG2]; simp
  have ht'1 : t' ≠ 1 := fun e => htG1 (by
    have : tG = c * t' * c⁻¹ := by rw [ht']; group
    rw [this, e]; group)
  have hcommt : ∀ p ∈ P, (p : G) * t' = t' * (p : G) := by
    intro p hp
    have hpPG : (p : G) ∈ PG := ⟨p, hp, rfl⟩
    have h1 := hXt (c * p * c⁻¹) (hconjP _ hpPG)
    calc (p : G) * (c⁻¹ * tG * c) = c⁻¹ * ((c * p * c⁻¹) * tG) * c := by group
      _ = c⁻¹ * (tG * (c * p * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * tG * c) * p := by group
  obtain ⟨d, hdP, hdz⟩ := S.exists_conj_centralizing h27 ha hb hP hP9 haP hbP ht'2 ht'1 hcommt
  have hdx : d * xG = xG * d := (hdP x hxP).symm
  have hdinv : d⁻¹ * xG = xG * d⁻¹ := by
    calc d⁻¹ * xG = d⁻¹ * (xG * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * xG) * d⁻¹ := by rw [hdx]
      _ = xG * d⁻¹ := by group
  refine ⟨c * d⁻¹, ?_, ?_⟩
  · calc c * d⁻¹ * xG = c * (d⁻¹ * xG) := by group
      _ = c * (xG * d⁻¹) := by rw [hdinv]
      _ = (c * xG) * d⁻¹ := by group
      _ = (xG * c) * d⁻¹ := by rw [hcC]
      _ = xG * (c * d⁻¹) := by group
  · calc c * d⁻¹ * S.z * (c * d⁻¹)⁻¹ = c * (d⁻¹ * S.z * d) * c⁻¹ := by group
      _ = c * t' * c⁻¹ := by
          rw [← hdz]; congr 2; group
      _ = tG := by rw [ht']; group

end Setup

end CFSG.Sporadic.Recognition.JankoWong
