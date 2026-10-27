module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26c
public import CFSG.Quasithin.Vol2.Ch12Sec6L26n
public import CFSG.Quasithin.Vol2.Ch12Sec6L26o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace S126C

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem conj_unique (hZ : Subgroup.center ↥K = ⊥) {k k' : ↥K}
    (h : MulAut.conj k = MulAut.conj k') : k = k' := by
  have h1 : MulAut.conj (k⁻¹ * k') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := mem_center_of_conj_eq_one h1
  rw [hZ, Subgroup.mem_bot] at h2
  rw [← inv_mul_eq_one]
  exact h2

theorem center_eq_bot_of_card {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hc : Nat.card X = 660) : Subgroup.center X = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hc]; norm_num)
    have hxc : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
    have hN : (Subgroup.zpowers x).Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hyc := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hxc hy) g
      have : g * y * g⁻¹ = y := by rw [hyc]; group
      rw [this]
      exact hy
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
    · rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have h2 := congrArg (fun H : Subgroup X => Nat.card H) h1
      simp only [Nat.card_zpowers, hx, Subgroup.card_top, hc] at h2
      omega

theorem card_le_three_of_isPGroup {X : Type} [Group X] (hc : Nat.card X = 660) {S : Subgroup X}
    (hS : IsPGroup 3 S) : Nat.card S ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨m, hm⟩ := hS.exists_card_eq
  have hd := Subgroup.card_subgroup_dvd_card S
  rw [hm, hc] at hd
  rw [hm]
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · exfalso
    have : 9 ∣ 660 := (pow_dvd_pow 3 (show 2 ≤ m + 2 by omega)).trans hd
    norm_num at this

section L211

variable [Finite Q]

theorem exists_inner_three (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K) {p : Q}
    (hpN : p ∈ Subgroup.normalizer (K : Set Q)) (hp3 : p ^ 3 = 1) :
    ∃ k : ↥K, k ^ 3 = 1 ∧ ∀ x ∈ K, p * x * p⁻¹ = (k : Q) * x * (k : Q)⁻¹ := by
  obtain ⟨⟨hcard, hs⟩, d1, -, -, -, -, -⟩ := hF ↥K hK
  have hZ := center_eq_bot_of_card hs hcard
  set α := K.normalizerMonoidHom ⟨p, hpN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨p, hpN⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hp3)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := d1 α (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα3))
  refine ⟨k, ?_, fun x hx => ?_⟩
  · have h1 : MulAut.conj (k ^ 3) = 1 := by rw [map_pow, hk, hα3]
    have := mem_center_of_conj_eq_one h1
    rwa [hZ, Subgroup.mem_bot] at this
  · have h1 := congrArg (fun β : MulAut ↥K => ((β ⟨x, hx⟩ : ↥K) : Q)) hk
    simp only [MulAut.conj_apply] at h1
    rw [conjK_apply] at h1
    simpa using h1.symm

omit [Finite Q] in
theorem inner_comm (hZ : Subgroup.center ↥K = ⊥) {p q : Q} (hpq : p * q = q * p) {k k' : ↥K}
    (hk : ∀ x ∈ K, p * x * p⁻¹ = (k : Q) * x * (k : Q)⁻¹)
    (hk' : ∀ x ∈ K, q * x * q⁻¹ = (k' : Q) * x * (k' : Q)⁻¹) : k * k' = k' * k := by
  apply conj_unique hZ
  refine MulEquiv.ext fun x => Subtype.ext ?_
  have hqx : q * x * q⁻¹ ∈ K := by
    rw [hk' x x.2]; exact K.mul_mem (K.mul_mem k'.2 x.2) (K.inv_mem k'.2)
  have hpx : p * x * p⁻¹ ∈ K := by
    rw [hk x x.2]; exact K.mul_mem (K.mul_mem k.2 x.2) (K.inv_mem k.2)
  have e1 : ((k : Q) * k') * x * ((k : Q) * k')⁻¹ = (p * q) * x * (p * q)⁻¹ := by
    calc ((k : Q) * k') * x * ((k : Q) * k')⁻¹ = k * ((k' : Q) * x * (k' : Q)⁻¹) * (k : Q)⁻¹ := by
          group
      _ = k * (q * x * q⁻¹) * (k : Q)⁻¹ := by rw [hk' x x.2]
      _ = p * (q * x * q⁻¹) * p⁻¹ := by rw [hk _ hqx]
      _ = (p * q) * x * (p * q)⁻¹ := by group
  have e2 : ((k' : Q) * k) * x * ((k' : Q) * k)⁻¹ = (q * p) * x * (q * p)⁻¹ := by
    calc ((k' : Q) * k) * x * ((k' : Q) * k)⁻¹ = k' * ((k : Q) * x * (k : Q)⁻¹) * (k' : Q)⁻¹ := by
          group
      _ = k' * (p * x * p⁻¹) * (k' : Q)⁻¹ := by rw [hk x x.2]
      _ = q * (p * x * p⁻¹) * q⁻¹ := by rw [hk' _ hpx]
      _ = (q * p) * x * (q * p)⁻¹ := by group
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e1, e2, hpq]

theorem mem_zpowers_of_comm_three (hcard : Nat.card ↥K = 660) {a b : ↥K} (ha : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) : b ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hb1 : b = 1
  · rw [hb1]; exact Subgroup.one_mem _
  have hpa : IsPGroup 3 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ha ha1, pow_one])
  have hpb : IsPGroup 3 ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hb hb1, pow_one])
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set ↥K) := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (a ^ n) b := (Commute.zpow_left hab n)
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [show a ^ n * b ^ m * (a ^ n)⁻¹ = b ^ m by rw [(hc.zpow_right m).eq]; group]
      exact Subgroup.zpow_mem_zpowers b m
    · intro hy
      have : y = (a ^ n)⁻¹ * (a ^ n * y * (a ^ n)⁻¹) * a ^ n := by group
      rw [this]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hm, show (a ^ n)⁻¹ * b ^ m * a ^ n = b ^ m by
        rw [mul_assoc, ← (hc.zpow_right m).eq]; group]
      exact Subgroup.zpow_mem_zpowers b m
  have hsup := IsPGroup.to_sup_of_normal_right' hpa hpb hnorm
  have hle := card_le_three_of_isPGroup hcard hsup
  have ha3 : orderOf a = 3 := orderOf_eq_prime ha ha1
  have heq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, ha3]; exact hle)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem exists_mem_inf_K (hsq : CFSG.IsStronglyQuasithin Q) (hF : FactL211Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsPSL 2 11 1 ↥K) : ∃ x ∈ P, x ∈ K ∧ x ≠ 1 := by
  classical
  obtain ⟨⟨hcard, hs⟩, -, -, -, -, -, -⟩ := hF ↥K hK
  have hZ := center_eq_bot_of_card hs hcard
  by_contra hPK
  push Not at hPK
  have hPN : ∀ p ∈ P, p ∈ Subgroup.normalizer (K : Set Q) := fun p hp => hc.L_norm (hc.P_le hp)
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := fun p hp => hc.P_elem.2 p hp
  by_cases hcen : ∀ p ∈ P, ∀ y ∈ K, p * y = y * p
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (by rw [hcard]; norm_num)
    have hy3 : (y : Q) ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    have hy1 : (y : Q) ≠ 1 := fun h => by
      rw [show y = 1 from Subtype.ext h, orderOf_one] at hy
      exact absurd hy (by norm_num)
    exact false_of_e27 hsq hc.P_elem hc.P_card hy3 (fun h => hy1 (hPK _ h y.2))
      fun e he => (hcen e he y y.2).symm
  · push Not at hcen
    obtain ⟨p, hp, y, hy, hpy⟩ := hcen
    obtain ⟨k, hk3, hk⟩ := exists_inner_three hF hK (hPN p hp) (hP3 p hp)
    have hk1 : (k : Q) ≠ 1 := by
      intro h
      apply hpy
      have := hk y hy
      rw [h, one_mul, inv_one, mul_one] at this
      calc p * y = p * y * p⁻¹ * p := by group
        _ = y * p := by rw [this]
    have hk3' : (k : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3
    have hkP : ∀ q ∈ P, (k : Q) * q = q * k := by
      intro q hq
      obtain ⟨k', hk'3, hk'⟩ := exists_inner_three hF hK (hPN q hq) (hP3 q hq)
      have hpq : p * q = q * p := hc.P_elem.1.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩ |> congrArg Subtype.val
      have hkk' := inner_comm hZ hpq hk hk'
      have hmem := mem_zpowers_of_comm_three hcard hk3 (fun h => hk1 (congrArg Subtype.val h))
        hk'3 hkk'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 := hk' k k.2
      rw [← hn] at h1
      have h2 : ((k ^ n : ↥K) : Q) * k * ((k ^ n : ↥K) : Q)⁻¹ = k := by
        have hcm : Commute ((k : Q) ^ n) (k : Q) := Commute.zpow_left (Commute.refl _) n
        rw [Subgroup.coe_zpow, hcm.eq, mul_inv_cancel_right]
      rw [h2] at h1
      calc (k : Q) * q = (q * k * q⁻¹) * q := by rw [h1]
        _ = q * k := by group
    exact false_of_e27 hsq hc.P_elem hc.P_card hk3' (fun h => hk1 (hPK _ h k.2)) hkP

theorem exists_mem_inf_cent (hF : FactL211Loc12626) (hc : Conf12626 K L P T v)
    (hK : IsPSL 2 11 1 ↥K) {xK : Q} (hxP : xK ∈ P) (hxK : xK ∈ K) (hx1 : xK ≠ 1) :
    ∃ c ∈ P, c ∈ Subgroup.centralizer (K : Set Q) ∧ c ≠ 1 := by
  classical
  obtain ⟨⟨hcard, hs⟩, -, -, -, -, -, -⟩ := hF ↥K hK
  have hZ := center_eq_bot_of_card hs hcard
  have hPN : ∀ p ∈ P, p ∈ Subgroup.normalizer (K : Set Q) := fun p hp => hc.L_norm (hc.P_le hp)
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := fun p hp => hc.P_elem.2 p hp
  have hlt : Subgroup.zpowers xK < P := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr hxP) fun h => ?_
    have h1 := hc.P_card
    rw [← h, Nat.card_zpowers, orderOf_eq_prime (hP3 xK hxP) hx1] at h1
    omega
  obtain ⟨p, hp, hpx⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨k, hk3, hk⟩ := exists_inner_three hF hK (hPN p hp) (hP3 p hp)
  have hkx : ∀ y ∈ K, xK * y * xK⁻¹ = ((⟨xK, hxK⟩ : ↥K) : Q) * y * ((⟨xK, hxK⟩ : ↥K) : Q)⁻¹ :=
    fun y _ => rfl
  have hpq : p * xK = xK * p :=
    congrArg Subtype.val (hc.P_elem.1.is_comm.comm ⟨p, hp⟩ ⟨xK, hxP⟩)
  have hcomm := inner_comm hZ hpq hk hkx
  have hx3 : (⟨xK, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hP3 xK hxP)
  have hmem := mem_zpowers_of_comm_three hcard hx3 (fun h => hx1 (congrArg Subtype.val h)) hk3
    hcomm.symm
  have hkP : (k : Q) ∈ P := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hn, Subgroup.coe_zpow]
    exact P.zpow_mem hxP n
  refine ⟨(k : Q)⁻¹ * p, P.mul_mem (P.inv_mem hkP) hp, ?_, fun h => hpx ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hk y hy
    calc y * ((k : Q)⁻¹ * p) = (k : Q)⁻¹ * ((k : Q) * y * (k : Q)⁻¹) * p := by group
      _ = (k : Q)⁻¹ * (p * y * p⁻¹) * p := by rw [h1]
      _ = (k : Q)⁻¹ * p * y := by group
  · have : p = k := by
      calc p = (k : Q) * ((k : Q)⁻¹ * p) := by group
        _ = k := by rw [h, mul_one]
    rw [this]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hn, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers xK n

theorem exists_inv_L211 (hF : FactL211Loc12626) (hc : Conf12626 K L P T v)
    (hK : IsPSL 2 11 1 ↥K) {xK : Q} (hxP : xK ∈ P) (hxK : xK ∈ K) (hx1 : xK ≠ 1) :
    ∃ k₀ : ↥K, k₀ ^ 2 = 1 ∧ k₀ ≠ 1 ∧ ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹ := by
  classical
  obtain ⟨⟨hcard, hs⟩, -, d2, -, -, -, -⟩ := hF ↥K hK
  have hZ := center_eq_bot_of_card hs hcard
  set α := K.normalizerMonoidHom ⟨v, hc.v_norm⟩ with hα
  have hfix : α ⟨xK, hxK⟩ = ⟨xK, hxK⟩ := by
    apply Subtype.ext
    rw [hα, conjK_apply, hc.L_cent xK (hc.P_le hxP)]
    group
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hc.v_norm⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hc.v_sq)
    rw [this, map_one]
  have hx3 : orderOf (⟨xK, hxK⟩ : ↥K) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hc.P_elem.2 xK hxP))
      (fun h => hx1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := d2 α hα2 ⟨_, hx3, hfix⟩
  refine ⟨k, ?_, fun h1 => ?_, fun x hx => ?_⟩
  · have h1 : MulAut.conj (k ^ 2) = 1 := by rw [map_pow, hk, hα2]
    have := mem_center_of_conj_eq_one h1
    rwa [hZ, Subgroup.mem_bot] at this
  · rw [h1, map_one] at hk
    obtain ⟨x, hxK', hx⟩ := hc.v_nc
    apply hx
    have h2 := congrArg (fun β : MulAut ↥K => ((β ⟨x, hxK'⟩ : ↥K) : Q)) hk
    simp only [MulAut.one_apply] at h2
    rw [hα, conjK_apply] at h2
    calc v * x = v * x * v⁻¹ * v := by group
      _ = x * v := by rw [← h2]
  · have h2 := congrArg (fun β : MulAut ↥K => ((β ⟨x, hx⟩ : ↥K) : Q)) hk
    simp only [MulAut.conj_apply] at h2
    rw [hα, conjK_apply] at h2
    simpa using h2.symm

theorem orderOf_conj' {X : Type} [Group X] (g x : X) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) x
  simpa [MulAut.conj_apply] using this

theorem T_le_normalizer_L211 (hF : FactL211Loc12626) (hc : Conf12626 K L P T v)
    (hK : IsPSL 2 11 1 ↥K) {k₀ : ↥K} (hk₀2 : k₀ ^ 2 = 1) (hk₀1 : k₀ ≠ 1)
    (hk₀ : ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹) :
    T ≤ Subgroup.normalizer (K : Set Q) := by
  classical
  obtain ⟨⟨hcard, hs⟩, -, -, d3, -, -, -⟩ := hF ↥K hK
  have hinv : ∀ n : ℕ, (n = 3 ∨ n = 5) → ∃ x : ↥K, orderOf x = n ∧ k₀ * x * k₀⁻¹ = x⁻¹ := by
    intro n hn
    have : Fact n.Prime := ⟨by rcases hn with rfl | rfl <;> norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) n (by
      rw [hcard]; rcases hn with rfl | rfl <;> norm_num)
    obtain ⟨g, hg⟩ := d3 k₀ y hk₀2 hk₀1 (by rcases hn with rfl | rfl <;> simp [hy])
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have := orderOf_conj' g⁻¹ y
      rw [inv_inv] at this
      rw [this, hy]
    · calc k₀ * (g⁻¹ * y * g) * k₀⁻¹ = g⁻¹ * ((g * k₀ * g⁻¹) * y * (g * k₀ * g⁻¹)⁻¹) * g := by
            group
        _ = g⁻¹ * y⁻¹ * g := by rw [hg]
        _ = (g⁻¹ * y * g)⁻¹ := by group
  obtain ⟨x5, hx5o, hx5⟩ := hinv 5 (Or.inr rfl)
  obtain ⟨y3, hy3o, hy3⟩ := hinv 3 (Or.inl rfl)
  intro t ht
  have htv : t * v = v * t := (hc.v_central t ht).symm
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hc.comp
  rcases CFSG.LocalCores.distinct_components_commute hc.comp hK' with heq | hcomm
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [heq]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by simpa [MulAut.conj_apply] using hyx
      rwa [← this]
  · exfalso
    obtain ⟨a, ha⟩ : ∃ a : Q, a = (x5 : Q) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Q, b = t * (y3 : Q) * t⁻¹ := ⟨_, rfl⟩
    have hbK : b ∈ K.map (MulAut.conj t).toMonoidHom := ⟨y3, y3.2, by rw [hb]; rfl⟩
    have hab : a * b = b * a := by
      have h1 : ⁅a, b⁆ ∈ ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator (ha ▸ x5.2) hbK
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hva : v * a * v⁻¹ = a⁻¹ := by
      rw [ha, hk₀ _ x5.2]
      simpa using congrArg Subtype.val hx5
    have hvb : v * b * v⁻¹ = b⁻¹ := by
      have h1 : v * (y3 : Q) * v⁻¹ = (y3 : Q)⁻¹ := by
        rw [hk₀ _ y3.2]
        simpa using congrArg Subtype.val hy3
      have htv' : v * t = t * v := htv.symm
      calc v * b * v⁻¹ = (v * t) * y3 * (v * t)⁻¹ := by rw [hb]; group
        _ = t * (v * y3 * v⁻¹) * t⁻¹ := by rw [htv']; group
        _ = b⁻¹ := by rw [h1, hb]; group
    have hcab : Commute a b := hab
    have hz : v * (a * b) * v⁻¹ = (a * b)⁻¹ := by
      rw [show v * (a * b) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) by group, hva, hvb, mul_inv_rev]
      exact (Commute.inv_inv hcab).eq
    have hao : orderOf a = 5 := by rw [ha, Subgroup.orderOf_coe, hx5o]
    have hbo : orderOf b = 3 := by rw [hb, orderOf_conj', Subgroup.orderOf_coe, hy3o]
    have ha5 : a ^ 5 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
    have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
    have hz15 : (a * b) ^ 15 = 1 := by
      rw [hcab.mul_pow, show 15 = 5 * 3 from rfl, pow_mul, ha5, one_pow, one_mul,
        show 5 * 3 = 3 * 5 from rfl, pow_mul, hb3, one_pow]
    have hodd : Odd (orderOf (a * b)) := Odd.of_dvd_nat (by decide)
      (orderOf_dvd_of_pow_eq_one hz15)
    rcases hc.inv (a * b) hodd hz with h3 | h5
    · rw [hcab.mul_pow, hb3, mul_one] at h3
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hao] at this
      norm_num at this
    · rw [hcab.mul_pow, ha5, one_mul] at h5
      have := orderOf_dvd_of_pow_eq_one h5
      rw [hbo] at this
      norm_num at this

theorem mem_normalizer_PK (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K) {k₀ : ↥K}
    (hk₀2 : k₀ ^ 2 = 1) (hk₀1 : k₀ ≠ 1)
    (hk₀ : ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹) {xK : Q} (hxK : xK ∈ K)
    (hxo : orderOf xK = 3) (hxv : xK * v = v * xK) {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q)) (hgv : g * v = v * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers xK : Subgroup Q) : Set Q) := by
  obtain ⟨-, -, -, -, -, -, d6⟩ := hF ↥K hK
  have hcomm : ∀ y (hy : y ∈ K), y * v = v * y → (⟨y, hy⟩ : ↥K) * k₀ = k₀ * ⟨y, hy⟩ := by
    intro y hy hyv
    apply Subtype.ext
    have h1 := hk₀ y hy
    have h2 : v * y * v⁻¹ = y := by rw [← hyv]; group
    rw [h2] at h1
    show y * (k₀ : Q) = k₀ * y
    calc y * (k₀ : Q) = (k₀ : Q) * y * (k₀ : Q)⁻¹ * k₀ := by rw [← h1]
      _ = k₀ * y := by group
  have hkey : ∀ h : Q, h ∈ Subgroup.normalizer (K : Set Q) → h * v = v * h →
      h * xK * h⁻¹ ∈ Subgroup.zpowers xK := by
    intro h hhK hhv
    have hyK : h * xK * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hhK xK).mp hxK
    have hhv' : h⁻¹ * v = v * h⁻¹ := by
      calc h⁻¹ * v = h⁻¹ * (v * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * v) * h⁻¹ := by rw [hhv]
        _ = v * h⁻¹ := by group
    have hyv : h * xK * h⁻¹ * v = v * (h * xK * h⁻¹) := by
      calc h * xK * h⁻¹ * v = h * xK * (h⁻¹ * v) := by group
        _ = h * xK * (v * h⁻¹) := by rw [hhv']
        _ = h * (xK * v) * h⁻¹ := by group
        _ = h * (v * xK) * h⁻¹ := by rw [hxv]
        _ = (h * v) * xK * h⁻¹ := by group
        _ = (v * h) * xK * h⁻¹ := by rw [hhv]
        _ = v * (h * xK * h⁻¹) := by group
    have hxo' : orderOf (⟨xK, hxK⟩ : ↥K) = 3 := by rw [Subgroup.orderOf_mk, hxo]
    have hyo' : orderOf (⟨h * xK * h⁻¹, hyK⟩ : ↥K) = 3 := by
      rw [Subgroup.orderOf_mk, orderOf_conj', hxo]
    have hmem := d6 k₀ ⟨xK, hxK⟩ ⟨_, hyK⟩ hk₀2 hk₀1 hxo' hyo' (hcomm xK hxK hxv)
      (hcomm _ hyK hyv)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have this : xK ^ n = h * xK * h⁻¹ := by simpa using congrArg Subtype.val hn
    rw [← this]
    exact Subgroup.zpow_mem_zpowers xK n
  have hgv' : g⁻¹ * v = v * g⁻¹ := by
    calc g⁻¹ * v = g⁻¹ * (v * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * v) * g⁻¹ := by rw [hgv]
      _ = v * g⁻¹ := by group
  refine mem_normalizer_of_forall (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hkey g hgK hgv) n
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 := hkey g⁻¹ (Subgroup.inv_mem _ hgK) hgv'
    have e : g⁻¹ * xK ^ n * g = (g⁻¹ * xK * g⁻¹⁻¹) ^ n := by rw [conj_zpow, inv_inv]
    rw [e]
    exact Subgroup.zpow_mem _ h1 n

omit [Finite Q] in
theorem comm_k₀ {k₀ : ↥K} (hk₀ : ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹) {y : Q}
    (hy : y ∈ K) (hyv : y * v = v * y) : (⟨y, hy⟩ : ↥K) * k₀ = k₀ * ⟨y, hy⟩ := by
  apply Subtype.ext
  have h1 := hk₀ y hy
  have h2 : v * y * v⁻¹ = y := by rw [← hyv]; group
  rw [h2] at h1
  show y * (k₀ : Q) = k₀ * y
  calc y * (k₀ : Q) = (k₀ : Q) * y * (k₀ : Q)⁻¹ * k₀ := by rw [← h1]
    _ = k₀ * y := by group

theorem comm_eq_bot_L211 (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K) {k₀ : ↥K}
    (hk₀2 : k₀ ^ 2 = 1) (hk₀1 : k₀ ≠ 1)
    (hk₀ : ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹) {xK : Q} (hxK : xK ∈ K)
    (hxo : orderOf xK = 3) (hxv : xK * v = v * xK) {Y : Subgroup Q} (hY2 : IsPGroup 2 Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set Q)) (hYv : ∀ y ∈ Y, y * v = v * y)
    (hxY : xK ∈ Subgroup.normalizer (Y : Set Q)) :
    ⁅Y, Subgroup.zpowers xK⁆ = ⊥ := by
  obtain ⟨-, -, -, -, -, d5, -⟩ := hF ↥K hK
  have hXN : Subgroup.zpowers xK ≤ Subgroup.normalizer (Y : Set Q) :=
    Subgroup.zpowers_le.mpr hxY
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers xK)) (Nat.card Y) := by
    rw [Nat.card_zpowers, hxo]
    obtain ⟨n, hn⟩ := hY2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hidem := S126Cop.comm_comm_eq hXN hcop
  set Z := ⁅Y, Subgroup.zpowers xK⁆ with hZ
  have hZY : Z ≤ Y := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXN
  have hZK : Z ≤ K := by
    rw [hZ, Subgroup.commutator_le]
    intro y hy a ha
    have ha' : a ∈ K := (Subgroup.zpowers_le.mpr hxK) ha
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYK hy) _).mp ha') (K.inv_mem ha')
  have hZv : Z ≤ Subgroup.centralizer ({v} : Set Q) := by
    rw [hZ, Subgroup.commutator_le]
    intro y hy a ha
    have hav : a ∈ Subgroup.centralizer ({v} : Set Q) := by
      refine (Subgroup.zpowers_le.mpr ?_) ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxv
    have hyv : y ∈ Subgroup.centralizer ({v} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hYv y hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyv hav)
      (Subgroup.inv_mem _ hyv)) (Subgroup.inv_mem _ hav)
  have hxo' : orderOf (⟨xK, hxK⟩ : ↥K) = 3 := by rw [Subgroup.orderOf_mk, hxo]
  have hY2' : IsPGroup 2 ↥(Z.subgroupOf K) := by
    intro z
    obtain ⟨n, hn⟩ := hY2 ⟨(z : Q), hZY (Subgroup.mem_subgroupOf.mp z.2)⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hYk : Z.subgroupOf K ≤ Subgroup.centralizer {k₀} := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzv : (z : Q) * v = v * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (hZv (Subgroup.mem_subgroupOf.mp hz))
    exact comm_k₀ hk₀ z.2 hzv
  have hxN : (⟨xK, hxK⟩ : ↥K) ∈ Subgroup.normalizer ((Z.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    have hxZ : xK ∈ Subgroup.normalizer (Z : Set Q) :=
      Subgroup.normalizer_commutator_ge_right Y (Subgroup.zpowers xK) (Subgroup.mem_zpowers xK)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxZ (z : Q))
  have hC := d5 k₀ ⟨xK, hxK⟩ hk₀2 hk₀1 hxo' (comm_k₀ hk₀ hxK hxv) (Z.subgroupOf K) hY2' hYk hxN
  have hZc : Z ≤ Subgroup.centralizer (Subgroup.zpowers xK : Set Q) := by
    intro z hz
    have h1 := hC (Subgroup.mem_subgroupOf.mpr (show ((⟨z, hZK hz⟩ : ↥K) : Q) ∈ Z from hz))
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h2 : z * xK = xK * z := by simpa using congrArg Subtype.val h1
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right h2 n).eq).symm
  rw [← hidem]
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZc

theorem exists_conj_inv (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K) {k₀ : ↥K}
    (hk₀2 : k₀ ^ 2 = 1) (hk₀1 : k₀ ≠ 1)
    (hk₀ : ∀ x ∈ K, v * x * v⁻¹ = (k₀ : Q) * x * (k₀ : Q)⁻¹) {xK : Q} (hxK : xK ∈ K)
    (hxo : orderOf xK = 3) :
    ∃ g ∈ K, (g * v * g⁻¹) * xK * (g * v * g⁻¹)⁻¹ = xK⁻¹ := by
  obtain ⟨-, -, -, d3, -, -, -⟩ := hF ↥K hK
  have hxo' : orderOf (⟨xK, hxK⟩ : ↥K) = 3 := by rw [Subgroup.orderOf_mk, hxo]
  obtain ⟨g, hg⟩ := d3 k₀ ⟨xK, hxK⟩ hk₀2 hk₀1 (Or.inl hxo')
  refine ⟨g, g.2, ?_⟩
  have hg' : ((g : Q) * k₀ * (g : Q)⁻¹) * xK * ((g : Q) * k₀ * (g : Q)⁻¹)⁻¹ = xK⁻¹ := by
    simpa using congrArg Subtype.val hg
  have hgx : (g : Q)⁻¹ * xK * g ∈ K := K.mul_mem (K.mul_mem (K.inv_mem g.2) hxK) g.2
  have h1 := hk₀ _ hgx
  calc ((g : Q) * v * (g : Q)⁻¹) * xK * ((g : Q) * v * (g : Q)⁻¹)⁻¹ =
      (g : Q) * (v * ((g : Q)⁻¹ * xK * g) * v⁻¹) * (g : Q)⁻¹ := by group
    _ = (g : Q) * ((k₀ : Q) * ((g : Q)⁻¹ * xK * g) * (k₀ : Q)⁻¹) * (g : Q)⁻¹ := by rw [h1]
    _ = ((g : Q) * k₀ * (g : Q)⁻¹) * xK * ((g : Q) * k₀ * (g : Q)⁻¹)⁻¹ := by group
    _ = xK⁻¹ := hg'

theorem le_comm_zpowers (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K)
    (hvN : v ∈ Subgroup.normalizer (K : Set Q)) (hnc : ∃ k ∈ K, v * k ≠ k * v) :
    K ≤ ⁅K, Subgroup.zpowers v⁆ := by
  obtain ⟨⟨-, hs⟩, -, -, -, -, -, -⟩ := hF ↥K hK
  have hle : ⁅K, Subgroup.zpowers v⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk a ha
    have haN : a ∈ Subgroup.normalizer (K : Set Q) := (Subgroup.zpowers_le.mpr hvN) ha
    rw [commutatorElement_def]
    have h1 : a * k⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haN _).mp (K.inv_mem hk)
    have e : k * a * k⁻¹ * a⁻¹ = k * (a * k⁻¹ * a⁻¹) := by group
    rw [e]
    exact K.mul_mem hk h1
  have hn : (⁅K, Subgroup.zpowers v⁆.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (A3.le_normalizer_commutator_left K _ g.2) _).mp hx
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅K, Subgroup.zpowers v⁆.subgroupOf K) with
    h | h
  · exfalso
    obtain ⟨k, hk, hvk⟩ := hnc
    have h1 : ⁅k, v⁆ ∈ ⁅K, Subgroup.zpowers v⁆ :=
      Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers v)
    have h2 : (⟨⁅k, v⁆, hle h1⟩ : ↥K) ∈ ⁅K, Subgroup.zpowers v⁆.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr h1
    rw [h, Subgroup.mem_bot] at h2
    have h3 : ⁅k, v⁆ = 1 := congrArg Subtype.val h2
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact hvk h3.symm
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ ⁅K, Subgroup.zpowers v⁆.subgroupOf K := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem perfect_L211 (hF : FactL211Loc12626) (hK : IsPSL 2 11 1 ↥K) : ⁅K, K⁆ = K := by
  obtain ⟨⟨hcard, hs⟩, -, -, -, -, -, -⟩ := hF ↥K hK
  have hZ := center_eq_bot_of_card hs hcard
  have hle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have hn : (⁅K, K⁆.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (A3.le_normalizer_commutator_left K K g.2) _).mp hx
  have := hs
  refine le_antisymm hle ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅K, K⁆.subgroupOf K) with h | h
  · exfalso
    have hab : ∀ a b : ↥K, a * b = b * a := fun a b => by
      have h1 : ⁅(a : Q), (b : Q)⁆ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator a.2 b.2
      have h2 : (⟨_, hle h1⟩ : ↥K) ∈ ⁅K, K⁆.subgroupOf K := Subgroup.mem_subgroupOf.mpr h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : ⁅(a : Q), (b : Q)⁆ = 1 := congrArg Subtype.val h2
      rw [commutatorElement_eq_one_iff_mul_comm] at h3
      exact Subtype.ext h3
    have htop : Subgroup.center ↥K = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hab g z
    rw [hZ] at htop
    have h1 := congrArg (fun H : Subgroup ↥K => Nat.card H) htop
    simp only [Subgroup.card_bot, Subgroup.card_top, hcard] at h1
    omega
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ ⁅K, K⁆.subgroupOf K := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end L211

end S126C

end CFSG.Quasithin.H13
