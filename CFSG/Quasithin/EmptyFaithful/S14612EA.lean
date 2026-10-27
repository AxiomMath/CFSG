module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.EmptyFaithful.S151cDich

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section PStr

variable {V : Type} [CommGroup V] [Finite V]

structure PStr14612 (X Tb P : Subgroup (MulAut V)) (p : ℕ) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  prime : p.Prime
  odd : p ≠ 2
  syl : Tb ∈ sylow2Of X
  P_le : P ≤ X
  normal : NormalIn X P
  pgrp : IsPGroup p P
  ne_bot : P ≠ ⊥
  eq : X = P ⊔ Tb
  minimal : ∀ N : Subgroup (MulAut V), N ≤ P → NormalIn X N → N = ⊥ ∨ N = P
  card_ne : Nat.card P ≠ p
  o2 : pCoreOf 2 X = ⊥
  sqtk : IsQuotientOfSQTKTC ↥X
  qhat : qhatOf X ≤ 2

namespace PStr14612

variable {X Tb P : Subgroup (MulAut V)} {p : ℕ}

theorem tb_le (h : PStr14612 X Tb P p) : Tb ≤ X := h.syl.1

theorem tb_two (h : PStr14612 X Tb P p) : IsPGroup 2 Tb := h.syl.2.1

theorem tb_le_normalizer (h : PStr14612 X Tb P p) : Tb ≤ Subgroup.normalizer (P : Set (MulAut V)) :=
  fun _ hx => h.normal.le_normalizer (h.tb_le hx)

theorem exists_pow_mem (h : PStr14612 X Tb P p) {x : MulAut V} (hx : x ∈ X) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ P := by
  have hx' : x ∈ ((P ⊔ Tb : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.eq]
    exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Tb h.tb_le_normalizer] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := h.tb_two ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (h.tb_le_normalizer hb) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem odd_mem (h : PStr14612 X Tb P p) {x : MulAut V} (hx : x ∈ X) (ho : Odd (orderOf x)) :
    x ∈ P := by
  obtain ⟨k, hk⟩ := h.exists_pow_mem hx
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := (Nat.coprime_two_left.mpr ho).pow_left k
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_mul (h : PStr14612 X Tb P p) {g : MulAut V} (hg : g ∈ X) :
    ∃ a ∈ P, ∃ t ∈ Tb, g = a * t := by
  let S : Subgroup (MulAut V) :=
    { carrier := {g | ∃ a ∈ P, ∃ t ∈ Tb, g = a * t}
      one_mem' := ⟨1, P.one_mem, 1, Tb.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, t, ht, rfl⟩ ⟨a', ha', t', ht', rfl⟩
        have h1 : t * a' * t⁻¹ ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (h.tb_le_normalizer ht) a').mp ha'
          exact this
        refine ⟨a * (t * a' * t⁻¹), P.mul_mem ha h1, t * t', Tb.mul_mem ht ht', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, t, ht, rfl⟩
        have h1 : t⁻¹ * a⁻¹ * t ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (h.tb_le_normalizer (Tb.inv_mem ht)) a⁻¹).mp
            (P.inv_mem ha)
          simpa using this
        refine ⟨t⁻¹ * a⁻¹ * t, h1, t⁻¹, Tb.inv_mem ht, ?_⟩
        group }
  have hPS : P ≤ S := fun a ha => ⟨a, ha, 1, Tb.one_mem, by simp⟩
  have hTS : Tb ≤ S := fun t ht => ⟨1, P.one_mem, t, ht, by simp⟩
  have : X ≤ S := by
    rw [h.eq]
    exact sup_le hPS hTS
  exact this hg

theorem abelian (h : PStr14612 X Tb P p) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr h.ne_bot
  have hZ := IsPGroup.center_nontrivial (p := p) h.pgrp
  let Zc : Subgroup (MulAut V) := (Subgroup.center ↥P).map P.subtype
  have hZP : Zc ≤ P := fun z hz => by
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2
  have hZn : NormalIn X Zc := by
    intro x hx z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hxz : x * (z' : MulAut V) * x⁻¹ ∈ P := h.normal x hx _ z'.2
    refine ⟨⟨x * (z' : MulAut V) * x⁻¹, hxz⟩, ?_, rfl⟩
    have hz'' : z' ∈ Subgroup.center ↥P := hz'
    show _ ∈ Subgroup.center ↥P
    rw [Subgroup.mem_center_iff] at hz'' ⊢
    intro q
    have hw : x⁻¹ * (q : MulAut V) * x ∈ P := by
      have := h.normal x⁻¹ (X.inv_mem hx) _ q.2
      simpa using this
    have hc := hz'' ⟨x⁻¹ * (q : MulAut V) * x, hw⟩
    have hc' : x⁻¹ * (q : MulAut V) * x * (z' : MulAut V) = (z' : MulAut V) * (x⁻¹ * (q : MulAut V) * x) :=
      congrArg Subtype.val hc
    apply Subtype.ext
    show (q : MulAut V) * (x * (z' : MulAut V) * x⁻¹) = x * (z' : MulAut V) * x⁻¹ * (q : MulAut V)
    calc (q : MulAut V) * (x * (z' : MulAut V) * x⁻¹)
        = x * ((x⁻¹ * (q : MulAut V) * x) * (z' : MulAut V)) * x⁻¹ := by group
      _ = x * ((z' : MulAut V) * (x⁻¹ * (q : MulAut V) * x)) * x⁻¹ := by rw [hc']
      _ = x * (z' : MulAut V) * x⁻¹ * (q : MulAut V) := by group
  have hZne : Zc ≠ ⊥ := by
    intro hbot
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
    have : (z : ↥P) ∈ Subgroup.center ↥P := z.2
    have hmem : ((z : ↥P) : MulAut V) ∈ Zc := ⟨z, z.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hmem
  have hZeq : Zc = P := (h.minimal Zc hZP hZn).resolve_left hZne
  intro a ha b hb
  have haZ : a ∈ Zc := hZeq ▸ ha
  obtain ⟨a', ha', rfl⟩ := haZ
  have := (Subgroup.mem_center_iff.mp ha') ⟨b, hb⟩
  exact (congrArg Subtype.val this).symm

theorem exists_not_commute (h : PStr14612 X Tb P p) : ∃ t ∈ Tb, ∃ a ∈ P, t * a ≠ a * t := by
  by_contra hcon
  push Not at hcon
  have : Fact p.Prime := ⟨h.prime⟩
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr h.ne_bot
  have hdvd : p ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp h.pgrp
    rw [hn]
    refine dvd_pow_self p ?_
    rintro rfl
    have : Nat.card P = 1 := by simpa using hn
    exact (Subgroup.card_eq_one.not.mpr h.ne_bot) this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hdvd
  set N : Subgroup (MulAut V) := Subgroup.zpowers (x : MulAut V) with hN
  have hNP : N ≤ P := Subgroup.zpowers_le.mpr x.2
  have hNn : NormalIn X N := by
    intro g hg y hy
    have hcent : g ∈ Subgroup.centralizer (N : Set (MulAut V)) := by
      have hP : P ≤ Subgroup.centralizer (N : Set (MulAut V)) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact (h.abelian a ha n (hNP hn)).symm
      have hT : Tb ≤ Subgroup.centralizer (N : Set (MulAut V)) := by
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact (hcon t ht n (hNP hn)).symm
      have : P ⊔ Tb ≤ Subgroup.centralizer (N : Set (MulAut V)) := sup_le hP hT
      rw [← h.eq] at this
      exact this hg
    have := Subgroup.mem_centralizer_iff.mp hcent y hy
    rw [show g * y * g⁻¹ = y by rw [← this]; group]
    exact hy
  rcases h.minimal N hNP hNn with h0 | h1
  · have : (x : MulAut V) ∈ N := Subgroup.mem_zpowers _
    rw [h0, Subgroup.mem_bot] at this
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    exact (Nat.Prime.one_lt h.prime).ne' hx.symm |>.elim
  · apply h.card_ne
    have : Nat.card N = p := by
      rw [hN, Nat.card_zpowers]
      have : orderOf (x : MulAut V) = orderOf x := Subgroup.orderOf_coe x
      rw [this, hx]
    rw [← this, h1]

theorem nine_le_card (h : PStr14612 X Tb P p) : 9 ≤ Nat.card P := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp h.pgrp
  have hp3 : 3 ≤ p := by
    have h2 := h.prime.two_le
    have h3 := h.odd
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card P = 1 := by simpa using hn
    exact h.ne_bot (Subgroup.card_eq_one.mp this)
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact h.card_ne (by simpa using hn)
  have hn2 : 2 ≤ n := by omega
  rw [hn]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    _ ≤ p ^ n := Nat.pow_le_pow_right h.prime.pos hn2

theorem not_le_tb (h : PStr14612 X Tb P p) : ¬ X ≤ Tb := by
  intro hXT
  have hPT : P ≤ Tb := h.P_le.trans hXT
  apply h.ne_bot
  refine (Subgroup.eq_bot_iff_forall P).2 fun x hx => ?_
  obtain ⟨a, ha⟩ := h.tb_two ⟨x, hPT hx⟩
  obtain ⟨b, hb⟩ := h.pgrp ⟨x, hx⟩
  have ha' : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : x ^ p ^ b = 1 := congrArg Subtype.val hb
  have h1 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have h2 : orderOf x ∣ p ^ b := orderOf_dvd_of_pow_eq_one hb'
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    ((Nat.coprime_primes Nat.prime_two h.prime).mpr (Ne.symm h.odd)).pow a b
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem solvable (h : PStr14612 X Tb P p) : Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (P.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.P_le).mpr h.normal.le_normalizer
  have h1 : Group.IsSolvable ↥(P.subgroupOf X) :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subtype.ext (h.abelian _ (Subgroup.mem_subgroupOf.mp a.2) _
        (Subgroup.mem_subgroupOf.mp b.2)))
  have hq : IsPGroup 2 (↥X ⧸ P.subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := h.exists_pow_mem y.2
      exact ⟨k, by
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))⟩
  have h2 : Group.IsSolvable (↥X ⧸ P.subgroupOf X) := by
    have : Group.IsNilpotent (↥X ⧸ P.subgroupOf X) := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (P.subgroupOf X).subtype (QuotientGroup.mk' (P.subgroupOf X))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_rat (h : PStr14612 X Tb P p) : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ 2 := by
  have hne : qhatOf X ≠ ⊤ := ne_top_of_le_ne_top (by simp) h.qhat
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨r, hr.symm, ?_⟩
  have := h.qhat
  rw [← hr] at this
  have h2 : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := by simpa using this
  exact WithTop.coe_le_coe.mp h2

theorem Jhat_ne_bot (h : PStr14612 X Tb P p) : Jhat X ≠ ⊥ := by
  obtain ⟨r, hr, hr2⟩ := h.exists_rat
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  have hAJ : A ≤ Jhat X := le_Jhat hA
  obtain ⟨r', -, -, ⟨hA2, -⟩, -⟩ := hA
  intro hJ
  have : A ≤ ⊥ := hJ ▸ hAJ
  exact hA2.1.ne_bot (le_bot_iff.mp this)

theorem P_le_Jhat (h : PStr14612 X Tb P p) : P ≤ Jhat X := by
  have hJne := h.Jhat_ne_bot
  have hJn : NormalIn X (Jhat X) := fun x hx k hk => Jhat_conj_mem hx hk
  set N : Subgroup (MulAut V) := Jhat X ⊓ P with hN
  have hNP : N ≤ P := inf_le_right
  have hNn : NormalIn X N := fun x hx k hk => ⟨hJn x hx k hk.1, h.normal x hx k hk.2⟩
  rcases h.minimal N hNP hNn with h0 | h1
  · exfalso
    have hno : ∀ y ∈ Jhat X, Odd (orderOf y) → y = 1 := by
      intro y hy ho
      have hyP : y ∈ P := h.odd_mem (Jhat_le X hy) ho
      have : y ∈ N := ⟨hy, hyP⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this
    have h2 : IsPGroup 2 (Jhat X) := by
      refine isPGroup_two_of_forall fun x hx => ?_
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      have hyx : x ^ 2 ^ k ∈ Jhat X := (Jhat X).pow_mem hx _
      have hyo : Odd (orderOf (x ^ 2 ^ k)) := by
        have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
        rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left,
          Nat.mul_div_cancel_left _ (by positivity)]
        exact hm
      exact ⟨k, hno _ hyx hyo⟩
    have : Jhat X ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (Jhat_le X) hJn.le_normalizer h2
    rw [h.o2, le_bot_iff] at this
    exact hJne this
  · rw [← h1]
    exact inf_le_left

theorem fixV_Jhat (h : PStr14612 X Tb P p) (hfix : fixV P = ⊥) : fixV (Jhat X) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
  have : v ∈ fixV P := fun a ha => hv a (h.P_le_Jhat ha)
  rw [hfix] at this
  exact this

theorem setting (h : PStr14612 X Tb P p) (hfix : fixV P = ⊥)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤) :
    Setting151c X Tb Tb where
  sq := h.sq
  solv := h.solvable
  o2 := h.o2
  sqtk := h.sqtk
  qhat := h.qhat
  syl := h.syl
  gen := hgen
  xc_le := h.tb_le
  tb_le := le_rfl
  xc_ne := h.not_le_tb
  hU := by
    intro Z₁ hZ₁ hne g hg
    obtain ⟨a, ha, t, ht, rfl⟩ := h.exists_mul hg.1
    have htZ : ∀ z ∈ Z₁, t z = z := fun z hz => hZ₁ hz t ht
    have haC : a ∈ centSub Z₁ := by
      intro z hz
      have h1 := hg.2 z hz
      have e : (a * t) z = a (t z) := rfl
      rw [e, htZ z hz] at h1
      exact h1
    set N : Subgroup (MulAut V) := P ⊓ centSub Z₁ with hN
    have hNn : NormalIn X N := by
      intro x hx k hk
      obtain ⟨a', ha', t', ht', rfl⟩ := h.exists_mul hx
      have hktP : t' * k * t'⁻¹ ∈ P := h.normal t' (h.tb_le ht') k hk.1
      have e : a' * t' * k * (a' * t')⁻¹ = t' * k * t'⁻¹ := by
        have hc := h.abelian a' ha' _ hktP
        calc a' * t' * k * (a' * t')⁻¹ = a' * (t' * k * t'⁻¹) * a'⁻¹ := by group
          _ = (t' * k * t'⁻¹) * a' * a'⁻¹ := by rw [hc]
          _ = t' * k * t'⁻¹ := by group
      rw [e]
      refine ⟨hktP, ?_⟩
      intro z hz
      have ht'z : t' z = z := hZ₁ hz t' ht'
      have ht'z' : t'⁻¹ z = z := by
        have := congrArg (fun y => t'⁻¹ y) ht'z
        simpa using this.symm
      have e2 : (t' * k * t'⁻¹) z = t' (k (t'⁻¹ z)) := rfl
      rw [e2, ht'z', hk.2 z hz, ht'z]
    rcases h.minimal N inf_le_left hNn with h0 | h1
    · have : a ∈ N := ⟨ha, haC⟩
      rw [h0, Subgroup.mem_bot] at this
      subst this
      simpa using ht
    · exfalso
      obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hPC : P ≤ centSub Z₁ := by
        intro b hb
        have : b ∈ N := by rw [h1]; exact hb
        exact this.2
      have hzP : (z : V) ∈ fixV P := fun b hb => hPC hb z z.2
      rw [hfix] at hzP
      exact hz1 (Subtype.ext hzP)
  star := by
    intro W hWne hWinv hWgen
    have hW1 : W ≤ fixV Tb := by
      refine hWgen.trans ((Subgroup.closure_le (fixV Tb : Subgroup V)).2 ?_)
      rintro x ⟨g, hg, z, hz, rfl⟩
      rw [hz.1 g hg]
      exact hz.1
    have hNn : NormalIn X (P ⊓ centSub W) := by
      intro x hx k hk
      obtain ⟨a', ha', t', ht', rfl⟩ := h.exists_mul hx
      have hktP : t' * k * t'⁻¹ ∈ P := h.normal t' (h.tb_le ht') k hk.1
      have e : a' * t' * k * (a' * t')⁻¹ = t' * k * t'⁻¹ := by
        have hc := h.abelian a' ha' _ hktP
        calc a' * t' * k * (a' * t')⁻¹ = a' * (t' * k * t'⁻¹) * a'⁻¹ := by group
          _ = (t' * k * t'⁻¹) * a' * a'⁻¹ := by rw [hc]
          _ = t' * k * t'⁻¹ := by group
      rw [e]
      refine ⟨hktP, ?_⟩
      intro w hw
      have ht'w : t' w = w := hW1 hw t' ht'
      have ht'w' : t'⁻¹ w = w := by
        have := congrArg (fun y => t'⁻¹ y) ht'w
        simpa using this.symm
      have e2 : (t' * k * t'⁻¹) w = t' (k (t'⁻¹ w)) := rfl
      rw [e2, ht'w', hk.2 w hw, ht'w]
    rcases h.minimal _ inf_le_left hNn with h0 | h1
    · obtain ⟨t, ht, a, ha, hta⟩ := h.exists_not_commute
      have hc : t * a * t⁻¹ * a⁻¹ ∈ P ⊓ centSub W := by
        refine ⟨?_, ?_⟩
        · exact P.mul_mem (h.normal t (h.tb_le ht) a ha) (P.inv_mem ha)
        · intro w hw
          have haw : a⁻¹ w ∈ W := hWinv a⁻¹ (X.inv_mem (h.P_le ha)) w hw
          have e : (t * a * t⁻¹ * a⁻¹) w = t (a (t⁻¹ (a⁻¹ w))) := rfl
          have h1' : t⁻¹ (a⁻¹ w) = a⁻¹ w := by
            have := congrArg (fun y => t⁻¹ y) (hW1 haw t ht)
            simpa using this.symm
          rw [e, h1']
          have e3 : a (a⁻¹ w) = w := by simp
          rw [e3]
          exact hW1 hw t ht
      rw [h0, Subgroup.mem_bot] at hc
      apply hta
      calc t * a = (t * a * t⁻¹ * a⁻¹) * (a * t) := by group
        _ = a * t := by rw [hc]; group
    · obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
      have hPC : P ≤ centSub W := by
        intro b hb
        have : b ∈ P ⊓ centSub W := by rw [h1]; exact hb
        exact this.2
      have hwP : (w : V) ∈ fixV P := fun b hb => hPC hb w w.2
      rw [hfix] at hwP
      exact hw1 (Subtype.ext hwP)
  central := by
    intro c hc j hj
    have : Fact p.Prime := ⟨h.prime⟩
    have hPF : P ≤ fittingOf (Jhat X) :=
      le_fittingOf_of_normal_nilpotent h.P_le_Jhat
        (fun x hx n hn => h.normal x (Jhat_le X hx) n hn) h.pgrp.isNilpotent
    have hcP : c ∈ fixV P := fun a ha => hc a (hPF ha)
    rw [hfix] at hcP
    have hc1 : c = 1 := hcP
    rw [hc1, map_one]

theorem card_eq_pow (h : PStr14612 X Tb P p) : ∃ n : ℕ, Nat.card P = p ^ n := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact (IsPGroup.iff_card (p := p)).mp h.pgrp

theorem odd_card (h : PStr14612 X Tb P p) : Odd (Nat.card P) := by
  obtain ⟨n, hn⟩ := h.card_eq_pow
  rw [hn]
  exact Odd.pow ((h.prime.eq_two_or_odd'.resolve_left h.odd))

theorem oTwoUpper_eq (h : PStr14612 X Tb P p) : oTwoUpper X = P := by
  apply le_antisymm
  · refine (Subgroup.closure_le P).2 ?_
    rintro x ⟨hx, ho⟩
    exact h.odd_mem hx ho
  · intro x hx
    refine mem_oTwoUpper_of_odd (h.P_le hx) ?_
    have : Fact p.Prime := ⟨h.prime⟩
    obtain ⟨b, hb⟩ := h.pgrp ⟨x, hx⟩
    have hb' : x ^ p ^ b = 1 := congrArg Subtype.val hb
    exact Odd.of_dvd_nat (Odd.pow (h.prime.eq_two_or_odd'.resolve_left h.odd))
      (orderOf_dvd_of_pow_eq_one hb')

theorem prime_eq_of_orderOf (h : PStr14612 X Tb P p) {x : MulAut V} (hx : x ∈ X) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hxq : orderOf x = q) : q = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hodd : Odd (orderOf x) := by rw [hxq]; exact hq.eq_two_or_odd'.resolve_left hq2
  have hxP : x ∈ P := h.odd_mem hx hodd
  obtain ⟨b, hb⟩ := h.pgrp ⟨x, hxP⟩
  have hb' : x ^ p ^ b = 1 := congrArg Subtype.val hb
  have hd : q ∣ p ^ b := hxq ▸ orderOf_dvd_of_pow_eq_one hb'
  exact (Nat.prime_dvd_prime_iff_eq hq h.prime).mp (hq.dvd_of_dvd_pow hd)

end PStr14612

structure Blocks14612 (X Tb P : Subgroup (MulAut V)) (p : ℕ) (L₁ L₂ : Subgroup (MulAut V)) :
    Prop where
  le₁ : L₁ ≤ X
  le₂ : L₂ ≤ X
  dih₁ : Nonempty (↥L₁ ≃* DihedralGroup p)
  dih₂ : Nonempty (↥L₂ ≃* DihedralGroup p)
  inf : L₁ ⊓ L₂ = ⊥
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  ne : L₂ ≠ L₁
  P_le : P ≤ L₁ ⊔ L₂
  swap : ∃ t ∈ Tb, conjBy t L₁ = L₂
  orb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂
  cinf : commV L₁ ⊓ commV L₂ = ⊥
  csup : commV L₁ ⊔ commV L₂ = ⊤
  fix₁ : commV L₁ ≤ fixV L₂
  fix₂ : commV L₂ ≤ fixV L₁
  rk_eq : rk (commV L₂) = rk (commV L₁)
  rank : (p = 5 → rk (commV L₁) = 4) ∧ (p = 3 → rk (commV L₁) = 2 ∨ rk (commV L₁) = 4)

end PStr

end CFSG.Quasithin
