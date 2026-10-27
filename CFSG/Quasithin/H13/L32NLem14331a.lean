module

public import CFSG.Quasithin.H13.L32NLem14330c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

namespace L14331

variable {G : Type} [Group G] [Finite G]

theorem mem_of_cube_mem {N K : Subgroup G} (hN : ¬ 3 ∣ Nat.card N) {c : G}
    (hc : c ∈ N) (hc3 : c ^ 3 ∈ K) : c ∈ K := by
  have hdvd : orderOf c ∣ Nat.card N := N.orderOf_dvd_natCard hc
  have hcop : Nat.Coprime 3 (orderOf c) := Nat.Coprime.coprime_dvd_right hdvd
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  rcases Nat.lt_or_ge 1 (orderOf c) with h1 | h1
  · obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e : c = (c ^ 3) ^ m := by
      rw [← pow_mul, ← pow_mod_orderOf, hm.2, pow_one]
    rw [e]
    exact K.pow_mem hc3 m
  · have h1' : orderOf c = 1 := le_antisymm h1 (orderOf_pos c)
    rw [orderOf_eq_one_iff.mp h1']
    exact K.one_mem

omit [Finite G] in
theorem eq_one_of_three_pow {x : G} {k : ℕ} (hx : x ^ (3 ^ k) = 1) {n : ℕ}
    (hn : ¬ 3 ∣ n) (hxn : orderOf x ∣ n) : x = 1 := by
  have hcop : Nat.Coprime (3 ^ k) n :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx) hxn)

omit [Finite G] in
theorem exists_zpow_of_mem_sup {s₁ s₂ : G} (h12 : s₁ * s₂ = s₂ * s₁) {x : G}
    (hx : x ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) : ∃ i j : ℤ, x = s₂ ^ i * s₁ ^ j := by
  have hcomm : Subgroup.zpowers s₁ ≤ Subgroup.normalizer (Subgroup.zpowers s₂ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute s₁ s₂ from h12) k).eq).symm
  obtain ⟨y, hy, w, hw, rfl⟩ := L14328.exists_mul_of_mem_sup hcomm
    (by rw [sup_comm]; exact hx)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨i, j, rfl⟩

omit [Finite G] in
theorem comm_sup {s₁ s₂ : G} (h12 : s₁ * s₂ = s₂ * s₁) :
    ∀ x ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂,
      ∀ y ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, j, rfl⟩ := exists_zpow_of_mem_sup h12 hx
  obtain ⟨k, m, rfl⟩ := exists_zpow_of_mem_sup h12 hy
  have c12 : Commute s₁ s₂ := h12
  have h1 : Commute (s₁ ^ j) (s₂ ^ k) := Commute.zpow_zpow c12 j k
  have h2 : Commute (s₂ ^ i) (s₂ ^ k) := Commute.zpow_zpow_self s₂ i k
  have h3 : Commute (s₁ ^ j) (s₁ ^ m) := Commute.zpow_zpow_self s₁ j m
  have h4 : Commute (s₂ ^ i) (s₁ ^ m) := (Commute.zpow_zpow c12 m i).symm
  calc s₂ ^ i * s₁ ^ j * (s₂ ^ k * s₁ ^ m) = s₂ ^ i * (s₁ ^ j * s₂ ^ k) * s₁ ^ m := by group
    _ = s₂ ^ i * (s₂ ^ k * s₁ ^ j) * s₁ ^ m := by rw [h1.eq]
    _ = (s₂ ^ i * s₂ ^ k) * (s₁ ^ j * s₁ ^ m) := by group
    _ = (s₂ ^ k * s₂ ^ i) * (s₁ ^ m * s₁ ^ j) := by rw [h2.eq, h3.eq]
    _ = s₂ ^ k * (s₂ ^ i * s₁ ^ m) * s₁ ^ j := by group
    _ = s₂ ^ k * (s₁ ^ m * s₂ ^ i) * s₁ ^ j := by rw [h4.eq]
    _ = s₂ ^ k * s₁ ^ m * (s₂ ^ i * s₁ ^ j) := by group

omit [Finite G] in
theorem zpow_pow_three {t : G} (ht : t ^ 3 = 1) (k : ℤ) : (t ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

omit [Finite G] in
theorem pow_three_sup {s₁ s₂ : G} (h₁ : orderOf s₁ = 3) (h₂ : orderOf s₂ = 3)
    (h12 : s₁ * s₂ = s₂ * s₁) :
    ∀ x ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := exists_zpow_of_mem_sup h12 hx
  have hc : Commute (s₂ ^ i) (s₁ ^ j) :=
    (Commute.zpow_zpow (show Commute s₁ s₂ from h12) j i).symm
  have e1 : s₁ ^ 3 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one s₁
  have e2 : s₂ ^ 3 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one s₂
  rw [hc.mul_pow, zpow_pow_three e2, zpow_pow_three e1, one_mul]

omit [Finite G] in
theorem not_mem_zpowers_of_three {x y : G} (hx : orderOf x = 3) (h0 : y ≠ 1) (h1 : y ≠ x)
    (h2 : y ≠ x ^ 2) : y ∉ Subgroup.zpowers x := by
  intro hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have e : x ^ k = x ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hx]
    rfl
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [e] at h0 h1 h2
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> rw [h] at h0 h1 h2
  · exact h0 (zpow_zero x)
  · exact h1 (zpow_one x)
  · exact h2 (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast])

theorem card_e9 {s₁ s₂ : G} (h₁ : orderOf s₁ = 3) (h₂ : orderOf s₂ = 3)
    (h12 : s₁ * s₂ = s₂ * s₁) (h21 : s₂ ∉ Subgroup.zpowers s₁) :
    Nat.card ↥(Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) = 9 := by
  have hcomm : Subgroup.zpowers s₁ ≤ Subgroup.normalizer (Subgroup.zpowers s₂ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute s₁ s₂ from h12) k).eq).symm
  have hinf : Subgroup.zpowers s₁ ⊓ Subgroup.zpowers s₂ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers s₁ ⊓ Subgroup.zpowers s₂) ∣ 3 := by
      rw [← h₂, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers s₁ ⊓ Subgroup.zpowers s₂ = Subgroup.zpowers s₂ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, h₂])
      exact h21 ((heq ▸ inf_le_left : Subgroup.zpowers s₂ ≤ _) (Subgroup.mem_zpowers s₂))
  have h := L32NSet14.card_sup_mul_card_inf hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, h₁, h₂] at h
  exact h

theorem exists_lift {X Q : Type} [Group X] [Finite X] [Group Q] (f : X →* Q)
    (hk : ¬ 3 ∣ Nat.card f.ker) {E : Subgroup Q} (hE : E ≤ f.range) (hE3 : IsPGroup 3 E) :
    ∃ S : Subgroup X, S.map f = E ∧ S ⊓ f.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup X := E.comap f with hY
  set f' : ↥Y →* ↥E := (f.comp Y.subtype).codRestrict E fun y => y.2 with hf'
  have hsurj : Function.Surjective f' := by
    rintro ⟨e, he⟩
    obtain ⟨x, hx⟩ := hE he
    exact ⟨⟨x, show f x ∈ E by rw [hx]; exact he⟩, Subtype.ext hx⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Y) := inferInstance
  set P' : Sylow 3 ↥E := P.mapSurjective hsurj with hP'
  have hP'top : (P' : Subgroup ↥E) = ⊤ := by
    exact (P'.is_maximal' (hE3.to_subgroup ⊤) le_top).symm
  have hmap : (P : Subgroup ↥Y).map f' = ⊤ := by
    rw [← hP'top, hP', Sylow.coe_mapSurjective]
  refine ⟨(P : Subgroup ↥Y).map Y.subtype, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨x, ⟨y, -, rfl⟩, rfl⟩
      exact y.2
    · intro hq
      have : (⟨q, hq⟩ : ↥E) ∈ (P : Subgroup ↥Y).map f' := by rw [hmap]; exact Subgroup.mem_top _
      obtain ⟨y, hyP, hy⟩ := this
      exact ⟨y, ⟨y, hyP, rfl⟩, congrArg Subtype.val hy⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨y, hyP, rfl⟩, hxk⟩
    obtain ⟨k, hk3⟩ := P.isPGroup' ⟨y, hyP⟩
    have hy3 : (y : X) ^ (3 ^ k) = 1 := by
      simpa using congrArg (fun z : ↥(P : Subgroup ↥Y) => ((z : ↥Y) : X)) hk3
    have hdvd : orderOf (y : X) ∣ Nat.card f.ker := f.ker.orderOf_dvd_natCard hxk
    exact Subgroup.mem_bot.mpr (show (y : X) = 1 from eq_one_of_three_pow hy3 hk hdvd)

theorem exists_lift_e9 {X Q : Type} [Group X] [Finite X] [Group Q] [Finite Q] (f : X →* Q)
    (hk : ¬ 3 ∣ Nat.card f.ker) {s₁ s₂ : Q} (hs₁ : s₁ ∈ f.range) (hs₂ : s₂ ∈ f.range)
    (h₁ : orderOf s₁ = 3) (h₂ : orderOf s₂ = 3) (h12 : s₁ * s₂ = s₂ * s₁)
    (h21 : s₂ ∉ Subgroup.zpowers s₁) :
    ∃ S : Subgroup X, Nat.card S = 9 ∧ (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      (∀ x ∈ S, x ^ 3 = 1) ∧ ∀ x ∈ S, f x = 1 → x = 1 := by
  set E : Subgroup Q := Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂ with hE
  have hE9 : Nat.card E = 9 := card_e9 h₁ h₂ h12 h21
  have hEr : E ≤ f.range := sup_le ((Subgroup.zpowers_le).mpr hs₁) ((Subgroup.zpowers_le).mpr hs₂)
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨S, hSE, hSk⟩ := exists_lift f hk hEr hE3
  have hinj : ∀ x ∈ S, f x = 1 → x = 1 := fun x hx h1 => by
    have : x ∈ S ⊓ f.ker := ⟨hx, h1⟩
    rwa [hSk, Subgroup.mem_bot] at this
  have hinj' : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := fun x hx y hy h => by
    have := hinj (x⁻¹ * y) (S.mul_mem (S.inv_mem hx) hy) (by rw [map_mul, map_inv, h,
      inv_mul_cancel])
    calc x = x * (x⁻¹ * y) := by rw [this, mul_one]
      _ = y := by group
  have hfE : ∀ x ∈ S, f x ∈ E := fun x hx => hSE ▸ Subgroup.mem_map_of_mem f hx
  refine ⟨S, ?_, fun x hx y hy => ?_, fun x hx => ?_, hinj⟩
  · have h1 := Subgroup.card_ker_mul_card_range (f.comp S.subtype)
    have hker : (f.comp S.subtype).ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (Subtype.ext (hinj x x.2 hx))
    rw [hker, Subgroup.card_bot, one_mul, MonoidHom.range_comp, Subgroup.range_subtype, hSE,
      hE9] at h1
    exact h1.symm
  · refine hinj' _ (S.mul_mem hx hy) _ (S.mul_mem hy hx) ?_
    rw [map_mul, map_mul]
    exact comm_sup h12 _ (hfE x hx) _ (hfE y hy)
  · refine hinj _ (S.pow_mem hx 3) ?_
    rw [map_pow]
    exact pow_three_sup h₁ h₂ h12 _ (hfE x hx)

theorem exists_e27 {H K N S : Subgroup G} (hKH : K ≤ H) (hNH : N ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hKN : ¬ 3 ∣ Nat.card ↥(K ⊓ N)) (hSK : S ≤ K) (hS9 : Nat.card S = 9)
    (hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS3 : ∀ x ∈ S, x ^ 3 = 1) (hSN : S ⊓ N = ⊥)
    (h3N : 3 ∣ Nat.card N) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSNn : S ≤ Subgroup.normalizer (N : Set G) := (hSK.trans hKH).trans hHN
  set X : Subgroup G := S ⊔ N with hX
  have hXcard : Nat.card X = 9 * Nat.card N := by
    have h := L32NSet14.card_sup_mul_card_inf hSNn
    rw [hSN, Subgroup.card_bot, mul_one, hS9] at h
    exact h
  have hS3' : IsPGroup 3 ↥(S.subgroupOf X) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : S ≤ X)).toEquiv, hS9]
    norm_num
  obtain ⟨Q, hSQ⟩ := hS3'.exists_le_sylow
  set Q' : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hQ'
  have hQ'X : Q' ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hSQ' : S ≤ Q' := fun s hs =>
    ⟨⟨s, (le_sup_left : S ≤ X) hs⟩, hSQ (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  have hQ'3 : IsPGroup 3 ↥Q' := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨y, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(Q : Subgroup ↥X) => ((z : ↥X) : G)) hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [SubmonoidClass.coe_pow, ← hyx]
    exact this
  have h27 : 27 ∣ Nat.card Q' := by
    have hX27 : 3 ^ 3 ∣ Nat.card X := by
      rw [hXcard]
      exact Nat.mul_dvd_mul (by norm_num : 3 ^ 2 ∣ 9) h3N
    have hQ := Q.pow_dvd_card_of_pow_dvd_card hX27
    rw [hQ', Subgroup.card_map_of_injective X.subtype_injective]
    simpa using hQ
  have hQ'N : Q' ≤ Subgroup.normalizer (N : Set G) :=
    hQ'X.trans (sup_le hSNn (Subgroup.le_normalizer))
  have hcard := L32NSet14.card_sup_mul_card_inf hQ'N
  have hle : Nat.card ↥(Q' ⊔ N) ≤ Nat.card X :=
    Subgroup.card_le_of_le (sup_le hQ'X le_sup_right)
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hQpos : 27 ≤ Nat.card Q' := Nat.le_of_dvd Nat.card_pos h27
  have hint : 1 < Nat.card ↥(Q' ⊓ N) := by
    by_contra hc
    push Not at hc
    have h1 : Nat.card ↥(Q' ⊔ N) * Nat.card ↥(Q' ⊓ N) ≤ 9 * Nat.card N := by
      calc Nat.card ↥(Q' ⊔ N) * Nat.card ↥(Q' ⊓ N) ≤ Nat.card X * 1 :=
            Nat.mul_le_mul hle hc
        _ = 9 * Nat.card N := by rw [mul_one, hXcard]
    rw [hcard] at h1
    have : 27 * Nat.card N ≤ 9 * Nat.card N := (Nat.mul_le_mul_right _ hQpos).trans h1
    omega
  have h3int : 3 ∣ Nat.card ↥(Q' ⊓ N) := by
    have hp : IsPGroup 3 ↥(Q' ⊓ N) := hQ'3.to_le inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hn] at hint ⊢
    rcases n with _ | n
    · simp at hint
    · exact dvd_pow_self 3 (Nat.succ_ne_zero n)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3int
  set c : G := (y : G) with hcy
  have hcQ : c ∈ Q' := (Subgroup.mem_inf.mp y.2).1
  have hcN : c ∈ N := (Subgroup.mem_inf.mp y.2).2
  have hc3 : orderOf c = 3 := by rw [hcy, Subgroup.orderOf_coe]; exact hy
  have hcH : c ∈ H := hNH hcN
  have hcS : ∀ s ∈ S, s * c = c * s := by
    intro s hs
    set d := s * c * s⁻¹ * c⁻¹ with hd
    have hdK : d ∈ K := by
      rw [hd, show s * c * s⁻¹ * c⁻¹ = s * (c * s⁻¹ * c⁻¹) by group]
      exact K.mul_mem (hSK hs) ((Subgroup.mem_normalizer_iff.mp (hHK hcH) _).mp
        (K.inv_mem (hSK hs)))
    have hdN : d ∈ N :=
      N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSNn hs) c).mp hcN) (N.inv_mem hcN)
    have hdQ : d ∈ Q' :=
      Q'.mul_mem (Q'.mul_mem (Q'.mul_mem (hSQ' hs) hcQ) (Q'.inv_mem (hSQ' hs))) (Q'.inv_mem hcQ)
    obtain ⟨k, hk⟩ := hQ'3 ⟨d, hdQ⟩
    have hd3 : d ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf d ∣ Nat.card ↥(K ⊓ N) := (K ⊓ N).orderOf_dvd_natCard ⟨hdK, hdN⟩
    have hd1 := eq_one_of_three_pow hd3 hKN hdvd
    calc s * c = s * c * s⁻¹ * c⁻¹ * (c * s) := by group
      _ = c * s := by rw [← hd, hd1, one_mul]
  have hcSn : Subgroup.zpowers c ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    exact (hcS s hs)
  have hSc : S ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : x ∈ N := (Subgroup.zpowers_le.mpr hcN) hx.2
    have : x ∈ S ⊓ N := ⟨hx.1, hxN⟩
    rwa [hSN] at this
  refine ⟨Subgroup.zpowers c ⊔ S, sup_le ((Subgroup.zpowers_le).mpr hcH) (hSK.trans hKH),
    ?_, ?_⟩
  ·
    have hgen : ∀ x ∈ Subgroup.zpowers c ⊔ S, ∃ i : ℤ, ∃ s ∈ S, x = c ^ i * s := by
      intro x hx
      obtain ⟨y, hy, w, hw, rfl⟩ := L14328.exists_mul_of_mem_sup hcSn
        (by rw [sup_comm]; exact hx)
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ⟨i, y, hy,
        (Commute.zpow_left (Commute.symm (show Commute y c from hcS y hy)) i).eq.symm⟩
    have hcomm : ∀ x ∈ Subgroup.zpowers c ⊔ S, ∀ y ∈ Subgroup.zpowers c ⊔ S, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, s, hs, rfl⟩ := hgen x hx
      obtain ⟨j, t, ht, rfl⟩ := hgen y hy
      have h1 : Commute (c ^ i) t := Commute.zpow_left (hcS t ht).symm i
      have h2 : Commute s (c ^ j) := Commute.zpow_right (hcS s hs) j
      have h3 : Commute s t := hScomm s hs t ht
      have h4 : Commute (c ^ i) (c ^ j) := Commute.zpow_zpow_self c i j
      calc c ^ i * s * (c ^ j * t) = c ^ i * (s * c ^ j) * t := by group
        _ = c ^ i * (c ^ j * s) * t := by rw [h2.eq]
        _ = c ^ j * c ^ i * (s * t) := by rw [← mul_assoc (c ^ i), h4.eq]; group
        _ = c ^ j * c ^ i * (t * s) := by rw [h3.eq]
        _ = c ^ j * (c ^ i * t) * s := by group
        _ = c ^ j * (t * c ^ i) * s := by rw [h1.eq]
        _ = c ^ j * t * (c ^ i * s) := by group
    refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
    obtain ⟨i, s, hs, rfl⟩ := hgen x hx
    have h1 : Commute (c ^ i) s := Commute.zpow_left (hcS s hs).symm i
    have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    rw [h1.mul_pow, zpow_pow_three hc3', one_mul, hS3 s hs]
  · have h := L32NSet14.card_sup_mul_card_inf hcSn
    rw [inf_comm, hSc, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3, hS9] at h
    rw [h]
    norm_num

end L14331

end CFSG.Quasithin.H13
