module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19S
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19NDec
public import CFSG.GH74.M12.HypGroup
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace L619

open CFSG.LieType.BorelTits CFSG.Quasithin

theorem exists_pow_prime_pow_lift {P K : Type*} [Group P] [Finite P] [Group K] (ψ : P →* K)
    (hψ : Function.Surjective ψ) {p : ℕ} (hp : p.Prime) {k : K} {j : ℕ} (hk : k ^ p ^ j = 1) :
    ∃ x : P, ψ x = k ∧ ∃ a : ℕ, x ^ p ^ a = 1 := by
  obtain ⟨x₀, rfl⟩ := hψ k
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact ⟨1, by simpa using hk.symm, 0, by simp⟩
  have hn : orderOf x₀ ≠ 0 := (isOfFinOrder_of_finite x₀).orderOf_pos.ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : Nat.Coprime m (p ^ j) := Nat.Coprime.pow_right _
    ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)))
  have h1 : 1 < p ^ j := Nat.one_lt_pow hj.ne' hp.one_lt
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  refine ⟨x₀ ^ (m * u), ?_, a, ?_⟩
  · rw [map_pow, pow_eq_pow_mod (m * u) hk, hu, pow_one]
  · rw [← pow_mul, show m * u * p ^ a = orderOf x₀ * u by rw [hnm]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]

@[expose] def threePartTop (K : Type*) [Group K] : Subgroup K :=
  Subgroup.closure {k | ∃ j : ℕ, k ^ 3 ^ j = 1}

section ThreeCompOf

variable {I P : Subgroup G} {Kt : Type*} [Group Kt] [Finite Kt] (ψ : ↥P →* Kt)

omit [Finite G] [Finite Kt] in
theorem psi_mem_threePartTop {x : G} (hx : x ∈ threePart P) :
    ψ ⟨x, threePart_le P hx⟩ ∈ threePartTop Kt := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxP, k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨x, hxP⟩ : ↥P) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    simp only [this, map_one]
  | one =>
    show ψ 1 ∈ threePartTop Kt
    rw [map_one]
    exact (threePartTop Kt).one_mem
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, threePart_le P (Subgroup.mul_mem _ hx hy)⟩ : ↥P) =
        ⟨x, threePart_le P hx⟩ * ⟨y, threePart_le P hy⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
    have e : (⟨x⁻¹, threePart_le P (Subgroup.inv_mem _ hx)⟩ : ↥P) =
        (⟨x, threePart_le P hx⟩ : ↥P)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ ihx

theorem exists_threePart_lift (hψ : Function.Surjective ψ) {k : Kt} {j : ℕ} (hk : k ^ 3 ^ j = 1) :
    ∃ x : G, ∃ hx : x ∈ threePart P, ψ ⟨x, threePart_le P hx⟩ = k ∧ ∃ a : ℕ, x ^ 3 ^ a = 1 := by
  obtain ⟨x, hxk, a, ha⟩ := exists_pow_prime_pow_lift ψ hψ Nat.prime_three hk
  have ha' : (x : G) ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  exact ⟨x, mem_threePart x.2 ha', hxk, a, ha'⟩

omit [Finite G] in
theorem eq_one_of_two_three {X : Type*} [Group X] {S : Subgroup X} (hS : IsPGroup 2 S) {x : X}
    (hx : x ∈ S) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  obtain ⟨b, hb⟩ := hS ⟨x, hx⟩
  have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
  have hcop : Nat.Coprime (3 ^ k) (2 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
  have : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem threeComp_of (hAI : threePart P ≤ I) (hIP : I ≤ Subgroup.normalizer (P : Set G))
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hsimple : ∀ N : Subgroup Kt, N ≤ threePartTop Kt →
      threePartTop Kt ≤ Subgroup.normalizer (N : Set Kt) → N = ⊥ ∨ N = threePartTop Kt)
    (h9 : ¬ 9 ∣ Nat.card Kt) (h3 : 3 ∣ Nat.card Kt) :
    ThreeComp I (threePart P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := threePart P with hA
  have hAP : A ≤ P := threePart_le P
  refine ⟨hAI, hIP.trans (normalizer_le_normalizer_threePart P), ?_, ?_, ?_, ?_⟩
  · exact Subgroup.closure_mono fun x hx => ⟨mem_threePart hx.1 hx.2.choose_spec, hx.2⟩
  · intro N hNA hAN
    set Nψ : Subgroup Kt := (N.subgroupOf P).map ψ with hNψ
    have hmemN : ∀ n (hn : n ∈ N), ψ ⟨n, hAP (hNA hn)⟩ ∈ Nψ := fun n hn =>
      ⟨⟨n, hAP (hNA hn)⟩, hn, rfl⟩
    have hNψle : Nψ ≤ threePartTop Kt := by
      rintro _ ⟨m, hm, rfl⟩
      exact psi_mem_threePartTop ψ (hNA hm)
    have hconj : ∀ k ∈ threePartTop Kt, ∀ m ∈ Nψ, k * m * k⁻¹ ∈ Nψ := by
      intro k hk m hm
      obtain ⟨j, hj⟩ : ∃ x : G, ∃ hx : x ∈ A, ψ ⟨x, hAP hx⟩ = k := by
        induction hk using Subgroup.closure_induction with
        | mem k hk =>
          obtain ⟨j, hj⟩ := hk
          obtain ⟨x, hx, hxk, -⟩ := exists_threePart_lift ψ hψ hj
          exact ⟨x, hx, hxk⟩
        | one => exact ⟨1, A.one_mem, map_one ψ⟩
        | mul k₁ k₂ _ _ ih₁ ih₂ =>
          obtain ⟨x₁, hx₁, rfl⟩ := ih₁
          obtain ⟨x₂, hx₂, rfl⟩ := ih₂
          exact ⟨x₁ * x₂, A.mul_mem hx₁ hx₂, by rw [← map_mul]; rfl⟩
        | inv k _ ih =>
          obtain ⟨x, hx, rfl⟩ := ih
          exact ⟨x⁻¹, A.inv_mem hx, by rw [← map_inv]; rfl⟩
      obtain ⟨hjA, rfl⟩ := hj
      obtain ⟨n, hn, rfl⟩ := hm
      have hn' : (n : G) ∈ N := hn
      have hc : (j : G) * n * j⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hAN hjA) n).mp hn'
      refine ⟨⟨(j : G) * n * j⁻¹, hAP (hNA hc)⟩, hc, ?_⟩
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    have hnormψ : threePartTop Kt ≤ Subgroup.normalizer (Nψ : Set Kt) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · exact hconj k hk m
      · intro hm
        have := hconj k⁻¹ (Subgroup.inv_mem _ hk) _ hm
        have e : k⁻¹ * (k * m * k⁻¹) * k⁻¹⁻¹ = m := by group
        rwa [e] at this
    rcases hsimple Nψ hNψle hnormψ with hbot | htop
    ·
      left
      have hle : N.subgroupOf P ≤ ψ.ker := by
        intro n hn
        rw [MonoidHom.mem_ker]
        have : ψ n ∈ Nψ := ⟨n, hn, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at this
      have h2 : IsPGroup 2 ↥(N.subgroupOf P) := hker.to_le hle
      have h2' : IsPGroup 2 N :=
        h2.of_equiv (Subgroup.subgroupOfEquivOfLe (hNA.trans hAP))
      exact le_pCoreOf_of_le_normalizer 2 hNA hAN h2'
    ·
      right
      refine le_antisymm hNA ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hxP, k, hk⟩
      have hxA : x ∈ A := mem_threePart hxP hk
      have hψx : ψ ⟨x, hxP⟩ ∈ Nψ := htop ▸ psi_mem_threePartTop ψ hxA
      obtain ⟨n, hn, hnx⟩ := hψx
      set O : Subgroup G := (ψ.ker.map P.subtype) ⊓ A with hO
      have hO2 : IsPGroup 2 O := (hker.map P.subtype).to_le inf_le_left
      have hON : O ≤ Subgroup.normalizer (N : Set G) := inf_le_right.trans hAN
      have hxNO : x ∈ N ⊔ O := by
        have hn' : (n : G) ∈ N := hn
        have hmem : (n : G)⁻¹ * x ∈ O := by
          refine ⟨⟨(n : ↥P)⁻¹ * ⟨x, hxP⟩, ?_, rfl⟩, A.mul_mem (A.inv_mem (hNA hn')) hxA⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
        have e : x = (n : G) * ((n : G)⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn') (Subgroup.mem_sup_right hmem)
      exact mem_of_pow_three_eq_one hO2 hON hxNO hk
  ·
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hk3 : k ^ 3 ^ 1 = 1 := by rw [pow_one, ← hk, pow_orderOf_eq_one]
    obtain ⟨x, hxA, hxk, a, ha⟩ := exists_threePart_lift ψ hψ hk3
    have hx1 : x ≠ 1 := by
      rintro rfl
      have : k = 1 := by rw [← hxk]; exact map_one ψ
      rw [this, orderOf_one] at hk
      omega
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hc
      exact hx1 hc
    refine ⟨x ^ 3 ^ (c - 1), A.pow_mem hxA _, ?_⟩
    have hdvd : 3 ^ (c - 1) ∣ orderOf x := hc ▸ pow_dvd_pow 3 (Nat.sub_le c 1)
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hc,
      Nat.pow_div (Nat.sub_le c 1) (by norm_num), Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hc0),
      pow_one]
  ·
    intro R hRA hR3
    set R' := R.subgroupOf P with hR'
    have hinj : Function.Injective (ψ.comp R'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro r hr
      rw [Subgroup.mem_bot]
      have hr1 : ψ (r : ↥P) = 1 := hr
      obtain ⟨a, ha⟩ := hR3 ⟨(r : G), r.2⟩
      have ha' : ((r : ↥P) : G) ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
      have : (r : ↥P) = 1 := eq_one_of_two_three hker hr1 (k := a)
        (Subtype.ext (by simpa using ha'))
      exact Subtype.ext this
    have hcard : Nat.card R = Nat.card R' :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hRA.trans hAP)).toEquiv).symm
    have hdvd : Nat.card R' ∣ Nat.card Kt := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hR3
    rw [hcard] at hb
    rw [hb] at hdvd
    rw [hcard, hb]
    by_contra hlt
    push Not at hlt
    have h2 : 2 ≤ b := by
      by_contra h
      push Not at h
      interval_cases b <;> norm_num at hlt
    exact h9 ((pow_dvd_pow 3 h2).trans hdvd)

theorem exists_preimage_threePartTop (hψ : Function.Surjective ψ) {k : Kt}
    (hk : k ∈ threePartTop Kt) : ∃ x : G, ∃ hx : x ∈ threePart P, ψ ⟨x, threePart_le P hx⟩ = k := by
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
    obtain ⟨j, hj⟩ := hk
    obtain ⟨x, hx, hxk, -⟩ := exists_threePart_lift ψ hψ hj
    exact ⟨x, hx, hxk⟩
  | one => exact ⟨1, (threePart P).one_mem, map_one ψ⟩
  | mul k₁ k₂ _ _ ih₁ ih₂ =>
    obtain ⟨x₁, hx₁, rfl⟩ := ih₁
    obtain ⟨x₂, hx₂, rfl⟩ := ih₂
    exact ⟨x₁ * x₂, (threePart P).mul_mem hx₁ hx₂, by rw [← map_mul]; rfl⟩
  | inv k _ ih =>
    obtain ⟨x, hx, rfl⟩ := ih
    exact ⟨x⁻¹, (threePart P).inv_mem hx, by rw [← map_inv]; rfl⟩

theorem exists_commutator_not_mem (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center Kt = ⊥) (h3 : 3 ∣ Nat.card Kt) {J : Subgroup G}
    (hO : ∀ x (hx : x ∈ P), x ∈ pCoreOf 2 J → ψ ⟨x, hx⟩ = 1) :
    ∃ e ∈ P, ∃ a ∈ threePart P, e * a * e⁻¹ * a⁻¹ ∉ pCoreOf 2 J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hk3 : k ^ 3 ^ 1 = 1 := by rw [pow_one, ← hk, pow_orderOf_eq_one]
  obtain ⟨a, haA, hak, -⟩ := exists_threePart_lift ψ hψ hk3
  have hk1 : k ∉ Subgroup.center Kt := by
    rw [hZ, Subgroup.mem_bot]
    rintro rfl
    rw [orderOf_one] at hk
    omega
  rw [Subgroup.mem_center_iff] at hk1
  push Not at hk1
  obtain ⟨g, hg⟩ := hk1
  obtain ⟨e, rfl⟩ := hψ g
  have haP := threePart_le P haA
  refine ⟨e, e.2, a, haA, fun hmem => hg ?_⟩
  have hP : (e : G) * a * (e : G)⁻¹ * a⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem e.2 haP) (P.inv_mem e.2)) (P.inv_mem haP)
  have h1 := hO _ hP hmem
  have e1 : (⟨(e : G) * a * (e : G)⁻¹ * a⁻¹, hP⟩ : ↥P) =
      e * ⟨a, haP⟩ * e⁻¹ * (⟨a, haP⟩ : ↥P)⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hak] at h1
  have : ψ e * k * (ψ e)⁻¹ = k := by
    calc ψ e * k * (ψ e)⁻¹ = ψ e * k * (ψ e)⁻¹ * k⁻¹ * k := by group
      _ = k := by rw [h1, one_mul]
  calc ψ e * k = ψ e * k * (ψ e)⁻¹ * ψ e := by group
    _ = k * ψ e := by rw [this]

omit [Finite G] in
theorem threePartTop_normal (Kt : Type*) [Group Kt] : (threePartTop Kt).Normal := by
  refine ⟨fun k hk g => ?_⟩
  have key : threePartTop Kt ≤ (threePartTop Kt).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨j, hj⟩
    refine Subgroup.subset_closure ⟨j, ?_⟩
    show (g * x * g⁻¹) ^ 3 ^ j = 1
    rw [conj_pow, hj, mul_one, mul_inv_cancel]
  exact key hk

theorem le_threePart_sup (hψ : Function.Surjective ψ) {S₂ : Subgroup G} (_hS₂P : S₂ ≤ P)
    (hkerS : ψ.ker.map P.subtype ≤ S₂)
    (htop : threePartTop Kt ⊔ (S₂.subgroupOf P).map ψ = ⊤) : P ≤ threePart P ⊔ S₂ := by
  have := threePartTop_normal Kt
  intro x hxP
  have hx : ψ ⟨x, hxP⟩ ∈ ((threePartTop Kt ⊔ (S₂.subgroupOf P).map ψ : Subgroup Kt) : Set Kt) := by
    rw [htop]; trivial
  rw [Subgroup.normal_mul] at hx
  obtain ⟨t, ht, s, hs, hts⟩ := hx
  beta_reduce at hts
  obtain ⟨a, haA, rfl⟩ := exists_preimage_threePartTop ψ hψ ht
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  have haP := threePart_le P haA
  have hκ : (⟨a, haP⟩ * s₀ : ↥P)⁻¹ * ⟨x, hxP⟩ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hts, inv_mul_cancel]
  have hκS : ((⟨a, haP⟩ * s₀ : ↥P)⁻¹ * ⟨x, hxP⟩ : ↥P) ∈ S₂.subgroupOf P :=
    hkerS ⟨_, hκ, rfl⟩
  have e : x = a * ((s₀ : G) * (((⟨a, haP⟩ * s₀ : ↥P)⁻¹ * ⟨x, hxP⟩ : ↥P) : G)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA)
    (Subgroup.mem_sup_right (S₂.mul_mem hs₀ hκS))

theorem isPGroup_ker_sup {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) (ψ₁ : ↥(P ⊔ S) →* Kt)
    (hcomp : ∀ x : ↥P, ψ₁ (Subgroup.inclusion le_sup_left x) = ψ x) : IsPGroup 2 ψ₁.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : ψ₁.range = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨x, rfl⟩ := hψ k
    exact ⟨_, hcomp x⟩
  have h1 := Subgroup.card_ker_mul_card_range ψ₁
  rw [hr, Subgroup.card_top] at h1
  have h2 := Subgroup.card_ker_mul_card_range ψ
  rw [ψ.range_eq_top_of_surjective hψ, Subgroup.card_top] at h2
  have h3 : P.relIndex (S ⊔ P) = P.relIndex S := A4.relIndex_sup_eq_of_le_normalizer' hSP
  have h4 : P.relIndex (S ⊔ P) * Nat.card ↥(P ⊓ (S ⊔ P)) = Nat.card ↥(S ⊔ P) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr le_sup_right, h3, sup_comm] at h4
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hS
  have h5 : P.relIndex S ∣ 2 ^ m := by
    rw [← hm]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h5
  obtain ⟨d, hd⟩ := (IsPGroup.iff_card).mp hker
  have hK : 0 < Nat.card Kt := Nat.card_pos
  apply IsPGroup.of_card (n := c + d)
  rw [← h1, ← h2, hc, hd] at h4
  exact Nat.eq_of_mul_eq_mul_right hK
    (h4.symm.trans (by ring : 2 ^ c * (2 ^ d * Nat.card Kt) = 2 ^ (c + d) * Nat.card Kt))

end ThreeCompOf

@[expose] def cyc3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cyc3_pow : cyc3 ^ 3 ^ 1 = 1 := by decide

theorem sign_eq_one_of_three {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : ℕ} (h : σ ^ 3 ^ j = 1) :
    Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ 3 ^ j = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exfalso
    have : Odd (3 ^ j) := Odd.pow (by decide)
    rw [this.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem threePartTop_le_alternating (n : ℕ) :
    threePartTop (Equiv.Perm (Fin n)) ≤ alternatingGroup (Fin n) :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hj⟩ => Equiv.Perm.mem_alternatingGroup.mpr
    (sign_eq_one_of_three hj)

theorem card_threePartTop_three : Nat.card (threePartTop (Equiv.Perm (Fin 3))) = 3 := by
  have h1 : Nat.card (threePartTop (Equiv.Perm (Fin 3))) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (threePartTop_le_alternating 3)
    rw [nat_card_alternatingGroup, Nat.card_fin] at this
    simpa [Nat.factorial] using this
  have h2 : cyc3 ∈ threePartTop (Equiv.Perm (Fin 3)) := Subgroup.subset_closure ⟨1, cyc3_pow⟩
  have h3 : Nat.card (threePartTop (Equiv.Perm (Fin 3))) ≠ 1 := by
    intro h
    have := Subgroup.eq_bot_of_card_eq _ h
    rw [this, Subgroup.mem_bot] at h2
    exact absurd h2 (by decide)
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact absurd h h3
  · exact h

theorem center_perm_three : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  revert g
  decide


theorem card_GL_two_two : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem nonempty_gl2_mulEquiv_perm3' :
    Nonempty (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)) := by
  let ua : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
  let ub : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩
  have hab : ua * ub ≠ ub * ua := fun h => absurd (congrArg Units.val h) (by decide)
  exact CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six card_GL_two_two ua ub hab

theorem not_sq_dvd_of_small {N r : ℕ} (hN : N = 6 ∨ N = 120 ∨ N = 168) (hr : r.Prime)
    (hr2 : r ≠ 2) : ¬ r ^ 2 ∣ N := by
  intro h
  have hpos : 0 < N := by omega
  have hle : r ^ 2 ≤ N := Nat.le_of_dvd hpos h
  have hr13 : r ≤ 12 := by
    by_contra hc
    push Not at hc
    have : 13 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hc 2
    omega
  interval_cases r <;> simp_all (config := { decide := true }) <;> omega

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem eq_bot_or_eq_threePartTop_three {N : Subgroup (Equiv.Perm (Fin 3))}
    (hN : N ≤ threePartTop (Equiv.Perm (Fin 3))) :
    N = ⊥ ∨ N = threePartTop (Equiv.Perm (Fin 3)) := by
  have h1 : Nat.card N ∣ 3 := by
    have := Subgroup.card_dvd_of_le hN
    rwa [card_threePartTop_three] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq N h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hN (by rw [h, card_threePartTop_three]))

theorem isSylowTwoOf_map_surj {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) (hρ : Function.Surjective ρ) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ⊤ := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨le_top, hS2.map ρ, ?_⟩
  rw [show (((S.subgroupOf H).map ρ).subgroupOf ⊤).index = ((S.subgroupOf H).map ρ).index from
    Subgroup.relIndex_top_right _]
  exact fun hd => hS.2.2 (hd.trans (Subgroup.index_map_dvd _ hρ))

theorem threePartTop_sup_eq_top_three {R : Subgroup (Equiv.Perm (Fin 3))} (hR : IsSylowTwoOf R ⊤) :
    threePartTop (Equiv.Perm (Fin 3)) ⊔ R = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : 2 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR.2.1
    have hidx := R.index_mul_card
    have hi : ¬ 2 ∣ R.index := by
      have := hR.2.2
      rwa [show (R.subgroupOf ⊤).index = R.index from Subgroup.relIndex_top_right R] at this
    rw [card_perm_three, hk] at hidx
    rcases k with _ | k
    · rw [pow_zero, mul_one] at hidx
      exact absurd (hidx ▸ (by norm_num : 2 ∣ 6)) hi
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  apply Subgroup.eq_top_of_card_eq
  rw [card_perm_three]
  have h1 : 3 ∣ Nat.card ↥(threePartTop (Equiv.Perm (Fin 3)) ⊔ R) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : threePartTop (Equiv.Perm (Fin 3)) ≤ _ ⊔ R)
    rwa [card_threePartTop_three] at this
  have h2 : 2 ∣ Nat.card ↥(threePartTop (Equiv.Perm (Fin 3)) ⊔ R) :=
    hR2.trans (Subgroup.card_dvd_of_le le_sup_right)
  have h3 : Nat.card ↥(threePartTop (Equiv.Perm (Fin 3)) ⊔ R) ∣ 6 := by
    rw [← card_perm_three]
    exact Subgroup.card_subgroup_dvd_card _
  exact Nat.dvd_antisymm h3 (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h1)

section ActOn

variable {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z X : Subgroup G)

@[expose] noncomputable def actOn {Q : Subgroup G} (hQ : Q ≤ normWZX W Z X)
    (hK : ∀ q : ↥Q, act0 hW Z X (Subgroup.inclusion hQ q) ∈ img0 hW Z X) :
    ↥Q →* ↥(img0 hW Z X) :=
  ((act0 hW Z X).comp (Subgroup.inclusion hQ)).codRestrict _ hK

omit [Finite G] in
theorem actOn_surjective (hX : X ≤ normWZX W Z X) :
    Function.Surjective (actOn hW Z X hX fun x => act0_mem_img0 hW Z X x.2) := by
  rintro ⟨k, hk⟩
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hk
  rw [Subgroup.mem_subgroupOf] at hg
  exact ⟨⟨(g : G), hg⟩, rfl⟩

end ActOn

end L619

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem parabolic_of_gl2 (h : Hyp6116 G T M L V n) (h432 : Stmt4_3_2)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    (hND : L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks)
    (hK : Nonempty (↥(Ks 0) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2))) :
    ∃ P₁ : Subgroup G, P₁ ≤ ch619I T L V ∧ T' ≤ Subgroup.normalizer (P₁ : Set G) ∧
      D' ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (T' ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  set S' := T' ⊓ I with hS'
  intro Ks hdec hND hK
  have hK0 : Ks 0 = K := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  rw [hK0] at hK
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := L619.nonempty_gl2_mulEquiv_perm3'
  set eK : ↥K ≃* Equiv.Perm (Fin 3) := e₁.trans e₂ with heK
  have hcardK : Nat.card K = 6 := by rw [Nat.card_congr eK.toEquiv, L619.card_perm_three]
  have hPN := c.conjClosure_E_le_normWZX hY
  set φ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hφ
  have hφs : Function.Surjective φ := L619.actOn_surjective hW _ P hPN
  set ψ : ↥P →* Equiv.Perm (Fin 3) := eK.toMonoidHom.comp φ with hψ
  have hψs : Function.Surjective ψ := eK.surjective.comp hφs
  have hψ1 : ∀ x : ↥P, ψ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ Q : Sylow p ↥K, IsCyclic Q := fun p hp hp2 Q =>
    CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd
      (by rw [hcardK]; exact L619.not_sq_dvd_of_small (Or.inl rfl) hp.out hp2) Q
  have hPK2 : P ⊓ ch619K2 T L V z ≤ pCoreOf 2 P := c.inf_K2_le_pCoreOf h h432 hz hY hW hcyc
  have hker : IsPGroup 2 ψ.ker := by
    have hle : ψ.ker ≤ (pCoreOf 2 P).subgroupOf P := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).symm).to_le hle
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hA := L619.threeComp_of ψ ((L619.threePart_le P).trans hPI) hIP hψs hker
    (fun N hN _ => L619.eq_bot_or_eq_threePartTop_three hN)
    (by rw [L619.card_perm_three]; decide) (by rw [L619.card_perm_three]; decide)
  have hO : ∀ x (hx : x ∈ P), x ∈ pCoreOf 2 I → ψ ⟨x, hx⟩ = 1 := fun x hx hxO =>
    (hψ1 ⟨x, hx⟩).mpr (Cfg619.pCoreOf_I_le_K2 h h432 z hxO)
  have hwit := L619.exists_commutator_not_mem ψ hψs L619.center_perm_three
    (by rw [L619.card_perm_three]; decide) hO
  have hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ L619.threePart P :=
    fun x hx k hk => L619.mem_threePart hx hk
  have hDA : D' ≤ Subgroup.normalizer (L619.threePart P : Set G) := fun d hdD =>
    mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hd.rank_I hA hPI hIP hP3
      hwit (hd.D'_le_I hdD) (hd.pow_three_eq_one hdD)).le
  have hS'P : IsSylowTwoOf (S' ⊓ P) P := A4.isSylowTwoOf_inf_normal hd.sylow_S' hPI hIP
  have hkerS : ψ.ker.map P.subtype ≤ S' ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hS'P (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
  have htop := L619.threePartTop_sup_eq_top_three (L619.isSylowTwoOf_map_surj hS'P ψ hψs)
  have hPA : P ≤ L619.threePart P ⊔ (S' ⊓ P) :=
    L619.le_threePart_sup ψ hψs inf_le_right hkerS htop
  have heq : L619.threePart P ⊔ S' = P ⊔ S' :=
    le_antisymm (sup_le_sup_right (L619.threePart_le P) _)
      (sup_le (hPA.trans (sup_le_sup_left inf_le_left _)) le_sup_right)
  have hP₁I : P ⊔ S' ≤ I := sup_le hPI inf_le_right
  refine ⟨P ⊔ S', hP₁I, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact L619.mem_normalizer_sup
      (le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right ht : t ∈ I ⊔ T'))
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hd.T'_le_I ht⟩)
  · rw [← heq]
    intro d hdD
    exact L619.mem_normalizer_sup (hDA hdD) (hd.D'_le_S' hdD)
  · intro hle
    exact c.not_le_M h h432 ((conjClosure_mono le_rfl hY.I_le).trans (le_sup_left.trans hle))
  · have heqS : T' ⊓ (P ⊔ S') = S' :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans hP₁I)) (le_inf inf_le_left le_sup_right)
    rw [heqS]
    exact F7.isSylowTwoOf_mono_right hd.sylow_S' le_sup_right hP₁I
  · have hP₁N : P ⊔ S' ≤ L619.normWZX (ch619W T L V z) (ch6ZS T L V) P :=
      hP₁I.trans (hY.I_le.trans (Cfg619.Y_le_normWZX hY))
    let ψ₁ : ↥(P ⊔ S') →* Equiv.Perm (Fin 3) :=
      eK.toMonoidHom.comp (L619.actOn hW _ P hP₁N fun q =>
        L619.act0_mem_img0_of_normDec hW _ P hdec hND _)
    have hcomp : ∀ x : ↥P, ψ₁ (Subgroup.inclusion le_sup_left x) = ψ x := fun x => rfl
    have hψ₁s : Function.Surjective ψ₁ := fun k => by
      obtain ⟨x, rfl⟩ := hψs k
      exact ⟨_, hcomp x⟩
    exact nonempty_quot_perm3_of_surjective ψ₁ hψ₁s
      (L619.isPGroup_ker_sup ψ hd.sylow_S'.2.1 (inf_le_right.trans hIP) hψs hker ψ₁ hcomp)

end Dat619

end CFSG.Quasithin.H13
