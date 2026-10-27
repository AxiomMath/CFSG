module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Grp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section Subgroups

theorem isElemAbelian_mono_829 {X : Type} [Group X] (p : ℕ) {A B : Subgroup X} (hAB : A ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p A := by
  have hcomm : ∀ a b : A, (a : X) * (b : X) = (b : X) * (a : X) := fun a b =>
    congrArg Subtype.val (isMulCommutative_iff.mp hB.1 ⟨a.1, hAB a.2⟩ ⟨b.1, hAB b.2⟩)
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun z hz => hB.2 z (hAB hz)⟩

theorem isElemAbelian_map {X Y : Type} [Group X] [Group Y] (p : ℕ) (f : X →* Y) {E : Subgroup X}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    have hxy : x * y = y * x := congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨x, hx⟩ ⟨y, hy⟩)
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
    rw [← hxz, ← map_pow, hE.2 x hx, map_one]

end Subgroups

section Rank

theorem exists_elemAb9_of_two_le_pRank {X : Type} [Group X] [Finite X]
    (h : 2 ≤ pRank 3 (⊤ : Subgroup X)) : ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold pRank at h
  have hbot : IsElemAbelian 3 (⊥ : Subgroup X) := by
    have h1 : ∀ a : (⊥ : Subgroup X), (a : X) = 1 := fun a => Subgroup.mem_bot.mp a.2
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · show (a : X) * (b : X) = (b : X) * (a : X)
      rw [h1 a, h1 b]
    · rw [Subgroup.mem_bot.mp hx, one_pow]
  have hne : {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    have h1 : 3 ^ k ≤ Nat.card X := by
      rw [← hE']
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.lt_pow_self (by norm_num)).le h1
  obtain ⟨E₀, -, hE₀, hcard₀⟩ := Nat.sSup_mem hne hbdd
  have hdvd : 3 ^ 2 ∣ Nat.card E₀ := by
    rw [hcard₀]
    exact pow_dvd_pow 3 h
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₀) 3 (n := 2) hdvd
  refine ⟨S.map E₀.subtype, ?_, ?_⟩
  · exact isElemAbelian_mono_829 3 (Subgroup.map_subtype_le S) hE₀
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hS]
    norm_num

end Rank

section Commuting

theorem exists_elemAb9_of_commuting {Q : Type} [Group Q] [Finite Q] (x y : Q)
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hxy : x * y = y * x)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxpow : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hypow : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hC : Commute x y := hxy
  have hCxy : ∀ i j : ℕ, Commute (x ^ i) (y ^ j) := fun i j => hC.pow_pow i j
  have hyx : ∀ j k : ℕ, y ^ j * x ^ k = x ^ k * y ^ j := fun j k => ((hC.symm).pow_pow j k).eq
  have hmul : ∀ a b a' b' : ℕ, x ^ a * y ^ b * (x ^ a' * y ^ b') = x ^ (a + a') * y ^ (b + b') := by
    intro a b a' b'
    calc x ^ a * y ^ b * (x ^ a' * y ^ b') = x ^ a * (y ^ b * x ^ a') * y ^ b' := by
          simp only [mul_assoc]
      _ = x ^ a * (x ^ a' * y ^ b) * y ^ b' := by rw [hyx b a']
      _ = x ^ (a + a') * y ^ (b + b') := by
          rw [pow_add, pow_add]
          simp only [mul_assoc]
  let E : Subgroup Q :=
    { carrier := {g | ∃ i j : ℕ, g = x ^ i * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        exact ⟨i + k, j + l, hmul i j k l⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [hmul i j (2 * i) (2 * j)]
        rw [show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring, pow_mul, pow_mul,
          hxpow, hypow, one_pow, one_pow, one_mul] }
  have hEmem : ∀ g : Q, g ∈ E ↔ ∃ i j : ℕ, g = x ^ i * y ^ j := fun g => Iff.rfl
  have hEc : IsMulCommutative ↥E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, j, hij⟩ := (hEmem _).mp a.2
    obtain ⟨k, l, hkl⟩ := (hEmem _).mp b.2
    show (a : Q) * (b : Q) = (b : Q) * (a : Q)
    rw [hij, hkl]
    have h1 : Commute (x ^ i * y ^ j) (x ^ k) :=
      Commute.mul_left ((Commute.refl x).pow_pow i k) (hC.symm.pow_pow j k)
    have h2 : Commute (x ^ i * y ^ j) (y ^ l) :=
      Commute.mul_left (hCxy i l) ((Commute.refl y).pow_pow j l)
    exact (Commute.mul_right h1 h2).eq
  have hEexp : ∀ g ∈ E, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨i, j, rfl⟩ := (hEmem _).mp hg
    have hxi : (x ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxpow, one_pow]
    have hyj : (y ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hypow, one_pow]
    rw [(hCxy i j).mul_pow, hxi, hyj, one_mul]
  have hxmod : ∀ i : ℕ, x ^ i = x ^ (i % 3) := fun i => by
    conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hxpow, one_pow, one_mul]
  have hymod : ∀ j : ℕ, y ^ j = y ^ (j % 3) := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hypow, one_pow, one_mul]
  have hkey : ∀ a b c d : ℕ, c ≤ 3 → d ≤ 3 → x ^ a * y ^ b = x ^ c * y ^ d →
      3 ∣ a + (3 - c) ∧ 3 ∣ b + (3 - d) := by
    intro a b c d hc hd h
    apply hind
    have hxc : x ^ c * x ^ (3 - c) = 1 := by rw [← pow_add, Nat.add_sub_cancel' hc, hxpow]
    have hyd : y ^ d * y ^ (3 - d) = 1 := by rw [← pow_add, Nat.add_sub_cancel' hd, hypow]
    have hxy3 : x ^ 3 * y ^ 3 = 1 := by rw [hxpow, hypow, one_mul]
    calc x ^ (a + (3 - c)) * y ^ (b + (3 - d))
        = x ^ a * y ^ b * (x ^ (3 - c) * y ^ (3 - d)) := (hmul a b (3 - c) (3 - d)).symm
      _ = x ^ c * y ^ d * (x ^ (3 - c) * y ^ (3 - d)) := by rw [h]
      _ = x ^ (c + (3 - c)) * y ^ (d + (3 - d)) := hmul c d (3 - c) (3 - d)
      _ = x ^ 3 * y ^ 3 := by rw [Nat.add_sub_cancel' hc, Nat.add_sub_cancel' hd]
      _ = 1 := hxy3
  let f : Fin 3 × Fin 3 → ↥E := fun p =>
    ⟨x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ), (hEmem _).mpr ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : x ^ (a : ℕ) * y ^ (b : ℕ) = x ^ (c : ℕ) * y ^ (d : ℕ) := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := hkey _ _ _ _ (by omega) (by omega) h'
      have hac : (a : ℕ) = (c : ℕ) := by have := a.2; have := c.2; omega
      have hbd : (b : ℕ) = (d : ℕ) := by have := b.2; have := d.2; omega
      rw [Fin.ext_iff.mpr hac, Fin.ext_iff.mpr hbd]
    · rintro ⟨g, hg⟩
      obtain ⟨i, j, rfl⟩ := (hEmem _).mp hg
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show x ^ (i % 3) * y ^ (j % 3) = x ^ i * y ^ j
      rw [← hxmod, ← hymod]
  refine ⟨E, ⟨hEc, hEexp⟩, ?_⟩
  have := Nat.card_eq_of_bijective f hf
  rw [Nat.card_prod] at this
  simpa using this.symm

end Commuting

section TwoGroup

theorem eq_one_of_mem_three_two {X : Type} [Group X] {A B : Subgroup X} {n : ℕ}
    (hA : Nat.card A ∣ 3 ^ n) (hB : IsPGroup 2 B) {g : X} (hgA : g ∈ A) (hgB : g ∈ B) :
    g = 1 := by
  have h1 : orderOf g ∣ 3 ^ n := by
    have h := orderOf_dvd_natCard (⟨g, hgA⟩ : A)
    rw [← Subgroup.orderOf_coe] at h
    exact h.trans hA
  obtain ⟨k, hk⟩ := hB ⟨g, hgB⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (3 ^ n) (2 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have h3 : orderOf g ∣ Nat.gcd (3 ^ n) (2 ^ k) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end TwoGroup

section Top

theorem isElemAbelian_top_of {V : Type} [Group V] (hc : ∀ a b : V, a * b = b * a)
    (hp : ∀ a : V, a ^ 3 = 1) : IsElemAbelian 3 (⊤ : Subgroup V) :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 b.1)⟩⟩, fun z _ => hp z⟩

end Top

section QuotientMeet

theorem exists_elemAb9_of_quotient_meet {X : Type} [Group X] [Finite X]
    (Y K' D : Subgroup X) [hYn : Y.Normal] (hD : IsPGroup 2 D)
    (hYK : ∀ y ∈ Y, ∀ k ∈ K', y * k * y⁻¹ * k⁻¹ ∈ D)
    (E : Subgroup (X ⧸ Y)) (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEK : ∀ e ∈ E, ∃ k ∈ K', (k : X ⧸ Y) = e) :
    ∃ F : Subgroup X, F ≤ K' ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup X := E.comap (QuotientGroup.mk' Y) ⊓ K' with hPdef
  set N : Subgroup X := Y ⊓ K' with hNdef
  have hPmem : ∀ x : X, x ∈ P ↔ ((x : X ⧸ Y) ∈ E ∧ x ∈ K') := fun x => Iff.rfl
  have hPK : P ≤ K' := inf_le_right
  have hNP : N ≤ P := by
    intro x hx
    obtain ⟨hxY, hxK⟩ := hx
    exact (hPmem x).mpr ⟨by rw [(QuotientGroup.eq_one_iff x).mpr hxY]; exact E.one_mem, hxK⟩
  have hNn : (N.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnY, hnK⟩ := hn
    exact ⟨hYn.conj_mem _ hnY g, K'.mul_mem (K'.mul_mem (hPK g.2) hnK) (K'.inv_mem (hPK g.2))⟩
  haveI := hNn
  let φ : ↥P →* X ⧸ Y := (QuotientGroup.mk' Y).comp P.subtype
  have hφr : φ.range = E := by
    ext e
    constructor
    · rintro ⟨p, rfl⟩
      exact ((hPmem p).mp p.2).1
    · intro he
      obtain ⟨k, hkK, hke⟩ := hEK e he
      have hkP : k ∈ P := (hPmem k).mpr ⟨by rw [hke]; exact he, hkK⟩
      exact ⟨⟨k, hkP⟩, hke⟩
  have hφk : φ.ker.map P.subtype = N := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' : ((p : X) : X ⧸ Y) = 1 := hp
      exact ⟨(QuotientGroup.eq_one_iff _).mp hp', hPK p.2⟩
    · rintro ⟨hxY, hxK⟩
      have hxP : x ∈ P := hNP ⟨hxY, hxK⟩
      exact ⟨⟨x, hxP⟩, (QuotientGroup.eq_one_iff x).mpr hxY, rfl⟩
  have hkerc : Nat.card φ.ker = Nat.card N := by
    rw [← hφk, Subgroup.card_map_of_injective P.subtype_injective]
  have hPcard : Nat.card P = 9 * Nat.card N := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkerc, hφr, hE9] at h
    omega
  have hN₁card : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hN₁index : (N.subgroupOf P).index = 9 := by
    have h := Subgroup.card_mul_index (N.subgroupOf P)
    rw [hN₁card, hPcard] at h
    have hNpos : 0 < Nat.card N := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hNpos
    rw [h]
    ring
  have hPpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm3, hPm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hPpos 3 (by norm_num)
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 3 (n := a) ⟨m, hPm⟩
  have hSindex : S.index = m := by
    have h := Subgroup.card_mul_index S
    rw [hS, hPm] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have htop : S ⊔ (N.subgroupOf P) = ⊤ := by
    have h1 : (S ⊔ N.subgroupOf P).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (S ⊔ N.subgroupOf P).index ∣ (N.subgroupOf P).index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [hSindex] at h1
    rw [hN₁index] at h2
    have hcop : Nat.Coprime m 9 := by
      have : Nat.Coprime m (3 ^ 2) :=
        Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
      simpa using this
    have h3 : (S ⊔ N.subgroupOf P).index = 1 := by
      have := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    exact Subgroup.index_eq_one.mp h3
  set S' : Subgroup X := S.map P.subtype with hS'def
  have hS'P : S' ≤ P := Subgroup.map_subtype_le S
  have hS'K : S' ≤ K' := hS'P.trans hPK
  have hS'card : Nat.card S' = 3 ^ a := by
    rw [hS'def, Subgroup.card_map_of_injective P.subtype_injective, hS]
  have hmkS : ∀ x ∈ S', ((x : X) : X ⧸ Y) ∈ E := fun x hx => ((hPmem x).mp (hS'P hx)).1
  let fS : ↥S' →* ↥E :=
    { toFun := fun s => ⟨((s : X) : X ⧸ Y), hmkS s s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [QuotientGroup.mk_mul]) }
  have hfSsurj : Function.Surjective fS := by
    intro e
    obtain ⟨k, hkK, hke⟩ := hEK e.1 e.2
    have hkP : k ∈ P := (hPmem k).mpr ⟨by rw [hke]; exact e.2, hkK⟩
    obtain ⟨s, hs, n, hn, hsn⟩ := Subgroup.mem_sup_of_normal_right.mp
      (show (⟨k, hkP⟩ : ↥P) ∈ S ⊔ N.subgroupOf P by rw [htop]; exact Subgroup.mem_top _)
    have hsX : ((s : P) : X) ∈ S' := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    refine ⟨⟨(s : P), hsX⟩, Subtype.ext ?_⟩
    show ((((s : P) : X)) : X ⧸ Y) = e.1
    have hnY : ((n : P) : X) ∈ Y := ((Subgroup.mem_subgroupOf).mp hn).1
    have hkn : ((s : P) : X) * ((n : P) : X) = k := by
      have := congrArg Subtype.val hsn
      simpa using this
    rw [← hke, ← hkn, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hnY, mul_one]
  have hcenS : ∀ z ∈ fS.ker, ∀ c : ↥S', c * z = z * c := by
    intro z hz c
    have hz1 : ((z : X) : X ⧸ Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    have hzY : (z : X) ∈ Y := (QuotientGroup.eq_one_iff _).mp hz1
    have hg := hYK (z : X) hzY (c : X) (hS'K c.2)
    have hgS : (z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹ ∈ S' :=
      S'.mul_mem (S'.mul_mem (S'.mul_mem z.2 c.2) (S'.inv_mem z.2)) (S'.inv_mem c.2)
    have hg1 : (z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹ = 1 :=
      eq_one_of_mem_three_two (by rw [hS'card]) hD hgS hg
    apply Subtype.ext
    show (c : X) * (z : X) = (z : X) * (c : X)
    calc (c : X) * (z : X) = ((z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹)⁻¹ * ((z : X) * (c : X)) := by
          group
      _ = (z : X) * (c : X) := by rw [hg1, inv_one, one_mul]
  have hPker : IsPGroup 3 fS.ker := by
    apply IsPGroup.of_card_dvd_pow (n := a)
    rw [← hS'card]
    exact Subgroup.card_subgroup_dvd_card _
  have hVtop : IsElemAbelian 3 (⊤ : Subgroup ↥E) := by
    refine isElemAbelian_top_of (fun u v => ?_) (fun u => ?_)
    · exact Subtype.ext (congrArg Subtype.val
        (isMulCommutative_iff.mp hE.1 ⟨u.1, u.2⟩ ⟨v.1, v.2⟩))
    · exact Subtype.ext (by simpa using hE.2 u.1 u.2)
  obtain ⟨F₀, hF₀, hF₀c⟩ := exists_elemAb9_of_central_kernel ↥E hVtop (by simpa using hE9)
    (Nat.card ↥S') ↥S' fS rfl hfSsurj hcenS hPker
  refine ⟨F₀.map S'.subtype, ?_, isElemAbelian_map 3 S'.subtype hF₀, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hS'K y.2
  · rw [Subgroup.card_map_of_injective S'.subtype_injective, hF₀c]

end QuotientMeet

end CFSG.Quasithin.H13
