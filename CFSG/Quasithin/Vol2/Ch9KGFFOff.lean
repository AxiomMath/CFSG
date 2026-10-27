module

public import CFSG.Quasithin.Background.B5CompB
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Offender

variable {V : Type} [CommGroup V] [Finite V]

theorem commutator_eq_bot_of_pGroup (hV : ∀ v : V, v ^ 2 = 1) {X A P : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut V))) :
    ⁅P, A⁆ = ⊥ := by
  by_contra hYne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 ↥A := hA.2.2.1.isPGroup
  set Y := ⁅P, A⁆ with hYdef
  have hYX : Y ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hAP
  have hYp : IsPGroup p ↥Y := hPp.to_le hYX
  have hAnY : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := fun a ha y hy => conj_mem_commutator ha hy
  have hAY : A ≤ Subgroup.normalizer (Y : Set (MulAut V)) := le_normalizer_of_conj hAnY
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥P) := by
    obtain ⟨a, ha⟩ := hA2.exists_card_eq
    obtain ⟨b, hb⟩ := hPp.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  have hYA : ⁅Y, A⁆ ≠ ⊥ := fun h =>
    hYne (CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot P A
      hAP hcop h)
  set G₀ := Y ⊔ A with hG₀def
  have hG₀n : ∀ x ∈ G₀, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    obtain ⟨y', hy', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAY).1 hx
    have e : y' * a * y * (y' * a)⁻¹ = y' * (a * y * a⁻¹) * y'⁻¹ := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hy' (hAnY a ha y hy)) (Y.inv_mem hy')
  have hYodd : ∀ y ∈ Y, Odd (orderOf y) := fun y hy => B55.odd_orderOf_of_isPGroup_odd hp2 hYp hy
  set Q := pCoreOf 2 G₀ with hQdef
  have hQcommY : ∀ q ∈ Q, ∀ y ∈ Y, q * y = y * q :=
    B1Red.pCoreOf_commute_of_odd_normal le_sup_left hG₀n hYodd
  have hker : G₀ ⊓ centSub (fixV Q) = Q :=
    B1Red.kernel_eq_pCoreOf hV (D := Y)
      (fun x hx ho => B1Red.mem_of_odd_orderOf_of_mem_sup hA2 hAY hx ho)
      (fun x hx q hq => (hQcommY q hq x hx).symm)
  set W := fixV Q with hWdef
  have hst : G₀ ≤ stabSub W := B1Red.le_stabSub_fixV_pCoreOf G₀
  have hO2b : pCoreOf 2 (autSub G₀ W) = ⊥ := B1Red.pCoreOf_autSub_eq_bot hker
  have hAnc : ¬ A ≤ centSub W := by
    intro hle
    have hAQ : A ≤ Q := by
      intro a ha
      have : a ∈ G₀ ⊓ centSub W := ⟨Subgroup.mem_sup_right ha, hle ha⟩
      rw [hker] at this
      exact this
    apply hYA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy a ha
    show ⁅y, a⁆ ∈ (⊥ : Subgroup (MulAut V))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hQcommY a (hAQ ha) y hy).symm
  have hAoff : IsFFStarOffender (autSub G₀ W) (autSub A W) :=
    B1Red.isFFStarOffender_autSub ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
      (fun a ha w hw => (hst (Subgroup.mem_sup_right ha) w).2 hw) hAnc
  have hG₀solv : Group.IsSolvable ↥G₀ :=
    have := hYp.isNilpotent
    have := hA2.isNilpotent
    B1Red.isSolvable_sup_of_isSolvable_of_le_normalizer hAY
  have hbsolv : Group.IsSolvable ↥(autSub G₀ W) := by
    rw [B1Red.autSub_eq_range hst]
    exact Group.isSolvable_of_surjective
      ((resHom W).comp (Subgroup.inclusion hst)).rangeRestrict_surjective
  have hFF : IsFFModule (autSub G₀ W) := isFFModule_of_offender hAoff
  have h6 := B55.pow_six_eq_one_of_mem_ffJ (B1.sq_eq_one_sub hV W) hbsolv
    (normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO2b) hFF
  obtain ⟨y, hy, a, ha, hya⟩ : ∃ y ∈ Y, ∃ a ∈ A, ⁅y, a⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hYA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy a ha
    exact Subgroup.mem_bot.2 (hcon y hy a ha)
  have hyG₀ : y ∈ G₀ := Subgroup.mem_sup_left hy
  have haG₀ : a ∈ G₀ := Subgroup.mem_sup_right ha
  have hcY : ⁅y, a⁆ ∈ Y := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ Y := hAnY a ha y⁻¹ (Y.inv_mem hy)
    have : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Y.mul_mem hy h1
  have hcG₀ : ⁅y, a⁆ ∈ G₀ := Subgroup.mem_sup_left hcY
  have hJ_c : resHom W (⟨⁅y, a⁆, hst hcG₀⟩ : stabSub W) ∈ ffJ (autSub G₀ W) := by
    have h1 : resHom W (⟨a, hst haG₀⟩ : stabSub W) ∈ ffJ (autSub G₀ W) :=
      B6.le_ffJ hAoff (mem_autSub.2 ⟨⟨a, hst haG₀⟩, ha, rfl⟩)
    have hysG : resHom W (⟨y, hst hyG₀⟩ : stabSub W) ∈ autSub G₀ W :=
      mem_autSub.2 ⟨⟨y, hst hyG₀⟩, hyG₀, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ (autSub G₀ W) hysG)
      (resHom W (⟨a, hst haG₀⟩ : stabSub W))).1 h1
    have hEq : (⟨⁅y, a⁆, hst hcG₀⟩ : stabSub W) =
        (⟨y, hst hyG₀⟩ : stabSub W) * ⟨a, hst haG₀⟩ * (⟨y, hst hyG₀⟩ : stabSub W)⁻¹ *
          (⟨a, hst haG₀⟩ : stabSub W)⁻¹ := Subtype.ext rfl
    rw [hEq]
    simp only [map_mul, map_inv]
    exact (ffJ _).mul_mem h2 ((ffJ _).inv_mem h1)
  have hc6W : ⁅y, a⁆ ^ 6 ∈ centSub W := by
    intro w hw
    have h1 : resHom W ((⟨⁅y, a⁆, hst hcG₀⟩ : stabSub W) ^ 6) = 1 := by
      rw [map_pow]
      exact h6 _ hJ_c
    have h2 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) h1
    simpa [resHom_apply] using h2
  have hc6Q : ⁅y, a⁆ ^ 6 ∈ Q := by
    rw [← hker]
    exact ⟨G₀.pow_mem hcG₀ 6, hc6W⟩
  have hc6Y : ⁅y, a⁆ ^ 6 ∈ Y := Y.pow_mem hcY 6
  have hc6one : ⁅y, a⁆ ^ 6 = 1 := by
    have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hc6Q⟩
    exact B19Aux.eq_one_of_odd_orderOf_of_pow (hYodd _ hc6Y) (congrArg Subtype.val hk)
  obtain ⟨i, hi⟩ := hYp ⟨⁅y, a⁆, hcY⟩
  have hpi : ⁅y, a⁆ ^ p ^ i = 1 := congrArg Subtype.val hi
  have hnd : ¬ p ∣ 6 := by
    intro hd
    have hd' : p ∣ 2 * 3 := hd
    rcases (Nat.Prime.dvd_mul hp.out).1 hd' with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h)
  have hcop6 : Nat.Coprime 6 (p ^ i) :=
    Nat.Coprime.pow_right i ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd))
  have hdvd : orderOf ⁅y, a⁆ ∣ Nat.gcd 6 (p ^ i) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc6one) (orderOf_dvd_of_pow_eq_one hpi)
  rw [hcop6.gcd_eq_one] at hdvd
  exact hya (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd))

theorem commutator_eq_bot_of_nilpotent (hV : ∀ v : V, v ^ 2 = 1) {X A R : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hRn : Group.IsNilpotent ↥R) (hRodd : Odd (Nat.card ↥R))
    (hR3 : ¬ 3 ∣ Nat.card ↥R) (hAR : A ≤ Subgroup.normalizer (R : Set (MulAut V))) :
    ⁅R, A⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  set C : Subgroup ↥R := (Subgroup.centralizer (A : Set (MulAut V))).subgroupOf R with hC
  suffices hCt : C = ⊤ by
    intro r hr
    have h : (⟨r, hr⟩ : ↥R) ∈ C := hCt ▸ Subgroup.mem_top _
    exact h
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hp⟩
  have hpR : p ∣ Nat.card ↥R := hpd.trans (Subgroup.index_dvd_card C)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr hpR)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hR3 hpR
  obtain ⟨P⟩ : Nonempty (Sylow p ↥R) := inferInstance
  have h14 : Group.IsNilpotent ↥R → ∀ (q : ℕ), Fact (Nat.Prime q) → ∀ (Q : Sylow q ↥R),
      (Q : Subgroup ↥R).Normal := (Group.isNilpotent_of_finite_tfae.out 1 4).mp
  have hPn : (P : Subgroup ↥R).Normal := h14 hRn p ⟨hp⟩ P
  set P' : Subgroup (MulAut V) := (P : Subgroup ↥R).map R.subtype with hP'
  have hP'p : IsPGroup p ↥P' := P.isPGroup'.map _
  have hAP' : A ≤ Subgroup.normalizer (P' : Set (MulAut V)) := by
    refine le_normalizer_of_conj fun a ha x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have hyR : a * (y : MulAut V) * a⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hAR ha) y).mp y.2
    set z : ↥R := ⟨_, hyR⟩ with hz
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
    have hk' : y ^ p ^ k = 1 := congrArg Subtype.val hk
    have hzk : z ^ p ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hz, conj_pow]
      have : (y : MulAut V) ^ p ^ k = 1 := by
        rw [← Subgroup.coe_pow, hk', Subgroup.coe_one]
      rw [this, mul_one, mul_inv_cancel]
    have hzp : IsPGroup p ↥(Subgroup.zpowers z) := by
      rintro ⟨g, hg⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hzk, one_zpow]
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    have hQP : Q = P := by
      have := Sylow.unique_of_normal P hPn
      exact Subsingleton.elim _ _
    exact ⟨z, hQP ▸ hQ (Subgroup.mem_zpowers z), rfl⟩
  have hc := commutator_eq_bot_of_pGroup hV hA hp2 hp3 hP'p hAP'
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  have hPC : (P : Subgroup ↥R) ≤ C := fun x hx => hc ⟨x, hx, rfl⟩
  exact P.not_dvd_index (hpd.trans (Subgroup.index_dvd_of_le hPC))

end Offender

section Perfect

variable {G : Type*} [Group G]

theorem commute_of_sq_eq_one {K R : Subgroup G} {a : G} (ha : a ^ 2 = 1)
    (hR : Odd (Nat.card ↥R)) (haR : ∀ r ∈ R, a * r = r * a)
    (hK : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ R) : ∀ k ∈ K, a * k = k * a := by
  intro k hk
  set c := a * k * a⁻¹ * k⁻¹ with hc
  have hcR : c ∈ R := hK k hk
  have h1 : a * k * a⁻¹ = c * k := by rw [hc]; group
  have ha' : a * a = 1 := by rw [← sq]; exact ha
  have hcc : c * c = 1 := by
    have h3 : a * (a * k * a⁻¹) * a⁻¹ = c * (c * k) := by
      have e : a * (c * k) * a⁻¹ = (a * c * a⁻¹) * (a * k * a⁻¹) := by group
      have hac : a * c * a⁻¹ = c := by rw [haR c hcR]; group
      rw [h1, e, hac, h1]
    have h4 : a * (a * k * a⁻¹) * a⁻¹ = k := by
      calc a * (a * k * a⁻¹) * a⁻¹ = (a * a) * k * (a * a)⁻¹ := by group
        _ = k := by rw [ha']; group
    rw [h4] at h3
    calc c * c = c * (c * k) * k⁻¹ := by group
      _ = 1 := by rw [← h3]; group
  have hco : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hcc)
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hR (Subgroup.orderOf_dvd_natCard R hcR)
  have hc1 : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hco with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [hc1, one_mul] at h1
  calc a * k = a * k * a⁻¹ * a := by group
    _ = k * a := by rw [h1]

theorem eq_one_of_perfect {K Q : Type*} [Group K] [Group Q] (hK : Group.IsPerfect K)
    (g : K →* Q) (hg : ∀ x y, g x * g y = g y * g x) (x : K) : g x = 1 := by
  have hle : commutator K ≤ g.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hg a b
  rw [Group.isPerfect_def] at hK
  rw [hK] at hle
  exact hle (Subgroup.mem_top x)

theorem comm_mem_ker_of_central {K : Subgroup G} {Q : Type*} [Group Q] {a : G}
    (hperf : ⁅K, K⁆ = K) (haK : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (f : ↥K →* Q)
    (hcen : ∀ (k : G) (hk : k ∈ K),
      f ⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩ ∈ Subgroup.center Q) :
    ∀ (k : G) (hk : k ∈ K), f ⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩ = 1 := by
  set α : ↥K →* ↥K :=
    { toFun := fun k => ⟨a * k * a⁻¹, haK k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) } with hα
  have hval : ∀ (k : G) (hk : k ∈ K),
      f ⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩ =
        f (α ⟨k, hk⟩) * (f ⟨k, hk⟩)⁻¹ := by
    intro k hk
    rw [← map_inv, ← map_mul]
    rfl
  have hc : ∀ x : ↥K, f (α x) * (f x)⁻¹ ∈ Subgroup.center Q := by
    rintro ⟨k, hk⟩
    rw [← hval k hk]
    exact hcen k hk
  set g : ↥K →* Q :=
    { toFun := fun x => f (α x) * (f x)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hy := Subgroup.mem_center_iff.mp (hc y)
        simp only [map_mul, mul_inv_rev]
        calc f (α x) * f (α y) * ((f y)⁻¹ * (f x)⁻¹)
            = (f (α x) * (f (α y) * (f y)⁻¹)) * (f x)⁻¹ := by group
          _ = ((f (α y) * (f y)⁻¹) * f (α x)) * (f x)⁻¹ := by rw [hy (f (α x))]
          _ = (f (α y) * (f y)⁻¹) * (f (α x) * (f x)⁻¹) := by group
          _ = f (α x) * (f x)⁻¹ * (f (α y) * (f y)⁻¹) := (hy _).symm } with hg
  have hperf' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  intro k hk
  rw [hval k hk]
  exact eq_one_of_perfect hperf' g (fun x y => Subgroup.mem_center_iff.mp (hc y) (g x)) ⟨k, hk⟩

end Perfect

section Dichotomy

variable {G : Type*} [Group G]

private theorem map_conj_eq_of_mem {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj y).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hy h).1 hh
  · intro hx
    refine ⟨y⁻¹ * x * y, (Subgroup.mem_normalizer_iff.1 hy _).2 ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · simp [MulAut.conj_apply, mul_assoc]

private theorem mem_normalizer_of_map_eq {H : Subgroup G} {y : G}
    (h : H.map (MulAut.conj y).toMonoidHom = H) : y ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ ∈ H.map (MulAut.conj y).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', he⟩ := hx
    have : x' = x := by simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : y ∈ Subgroup.normalizer (H₂ : Set G)) :
    y ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) :=
  mem_normalizer_of_map_eq (by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem h₁, map_conj_eq_of_mem h₂])

theorem le_normalizer_of_commute {J R : Subgroup G} (hJR : ∀ j ∈ J, ∀ r ∈ R, j * r = r * j) :
    R ≤ Subgroup.normalizer (J : Set G) := fun r hr =>
  Subgroup.mem_normalizer_iff.mpr fun x => by
    constructor
    · intro hx
      have e : r * x * r⁻¹ = x := by rw [← hJR x hx r hr]; group
      rwa [e]
    · intro hx
      have h := hJR _ hx r hr
      have e : x = r * x * r⁻¹ := by
        calc x = r⁻¹ * ((r * x * r⁻¹) * r) := by group
          _ = r⁻¹ * (r * (r * x * r⁻¹)) := by rw [h]
          _ = r * x * r⁻¹ := by group
      rw [e]
      exact hx

theorem le_of_le_sup_of_perfect {K J R : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hJR : ∀ j ∈ J, ∀ r ∈ R, j * r = r * j) (hR : Group.IsSolvable ↥R) (hK : K ≤ J ⊔ R) :
    K ≤ J := by
  set H := J ⊔ R with hH
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_commute hJR
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := sup_le (Subgroup.le_normalizer) hRJ
  set N : Subgroup ↥H := J.subgroupOf H with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHJ
  set φ := QuotientGroup.mk' N with hφ
  set ρ : ↥R →* ↥H ⧸ N := φ.comp (Subgroup.inclusion le_sup_right) with hρ
  have hρs : Function.Surjective ρ := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨j, hj, r, hr, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hRJ).1 hh
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [hρ, MonoidHom.comp_apply, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show (⟨r, _⟩ : ↥H)⁻¹ * ⟨j * r, hh⟩ ∈ N
    rw [hN, Subgroup.mem_subgroupOf]
    show (r : G)⁻¹ * (j * r) ∈ J
    have e : (r : G)⁻¹ * (j * r) = j := by rw [hJR j hj r hr]; group
    rw [e]
    exact hj
  have hsol : Group.IsSolvable (↥H ⧸ N) := Group.isSolvable_of_surjective hρs
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have hK'map : K'.map H.subtype = K := by
    rw [hK', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK]
  have hK'perf : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hK'map, hperf]
  set M := K'.map φ with hM
  have hMperf : ⁅M, M⁆ = M := by rw [hM, ← Subgroup.map_commutator, hK'perf]
  have hMbot : M = ⊥ := by
    by_contra hne
    have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hne
    have : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMperf
    exact Group.IsPerfect.not_isSolvable ↥M (subgroup_solvable_of_solvable M)
  intro k hk
  have hk' : (⟨k, hK hk⟩ : ↥H) ∈ K' := hk
  have h1 : φ ⟨k, hK hk⟩ ∈ M := ⟨_, hk', rfl⟩
  rw [hMbot, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem isQuasisimple_of_central {K R : Subgroup G} {Q : Type*} [Group Q] (hperf : ⁅K, K⁆ = K)
    (hRc : ∀ r ∈ R, ∀ k ∈ K, r * k = k * r) (hQ : CFSG.IsQuasisimple Q) (f : ↥K →* Q)
    (hf : Function.Surjective f) (hker : f.ker = R.subgroupOf K) : CFSG.IsQuasisimple ↥K := by
  have hperf' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  set S : Subgroup ↥K := (Subgroup.center Q).comap f with hS
  have hSn : S.Normal := (Subgroup.center Q).normal_of_characteristic.comap f
  have hkerc : ∀ x : ↥K, x ∈ f.ker → ∀ y : ↥K, x * y = y * x := by
    intro x hx y
    rw [hker, Subgroup.mem_subgroupOf] at hx
    exact Subtype.ext (hRc _ hx _ y.2)
  have hSZ : S ≤ Subgroup.center ↥K := by
    intro s hs
    have hfs := Subgroup.mem_center_iff.mp hs
    have hc : ∀ x : ↥K, s * x * s⁻¹ * x⁻¹ ∈ f.ker := by
      intro x
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hfs (f x)]
      group
    set g : ↥K →* ↥K :=
      { toFun := fun x => s * x * s⁻¹ * x⁻¹
        map_one' := by group
        map_mul' := fun x y => by
          have hy := hkerc _ (hc y) x
          calc s * (x * y) * s⁻¹ * (x * y)⁻¹
              = (s * x * s⁻¹ * x⁻¹) * (x * (s * y * s⁻¹ * y⁻¹)) * x⁻¹ := by group
            _ = (s * x * s⁻¹ * x⁻¹) * ((s * y * s⁻¹ * y⁻¹) * x) * x⁻¹ := by rw [hy]
            _ = s * x * s⁻¹ * x⁻¹ * (s * y * s⁻¹ * y⁻¹) := by group } with hg
    have h1 : ∀ x, g x = 1 := eq_one_of_perfect hperf' g
      (fun x y => hkerc _ (hc x) (g y))
    rw [Subgroup.mem_center_iff]
    intro x
    have := h1 x
    rw [hg] at this
    change s * x * s⁻¹ * x⁻¹ = 1 at this
    calc x * s = (s * x * s⁻¹ * x⁻¹)⁻¹ * (s * x) := by group
      _ = s * x := by rw [this, inv_one, one_mul]
  set ψ : ↥K →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp f with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hf
  have hψk : ψ.ker = S := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hS, Subgroup.mem_comap]
  set e : ↥K ⧸ S ≃* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) with he
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  have : IsSimpleGroup (↥K ⧸ S) := e.isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient S hSZ hperf' this
    ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

variable {V : Type} [CommGroup V] [Finite V]

theorem ffJ_dichotomy (hV : ∀ v : V, v ^ 2 = 1) {X K R : Subgroup (MulAut V)}
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hXR : X ≤ Subgroup.normalizer (R : Set (MulAut V))) (hperf : ⁅K, K⁆ = K)
    (hRn : Group.IsNilpotent ↥R) (hRodd : Odd (Nat.card ↥R)) (hR3 : ¬ 3 ∣ Nat.card ↥R)
    {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) (f : ↥K →* Q)
    (hf : Function.Surjective f) (hker : f.ker = R.subgroupOf K) :
    ⁅K, ffJ X⁆ = ⊥ ∨ (K ≤ ffJ X ∧ ∀ r ∈ R, ∀ k ∈ K, r * k = k * r) := by
  set J := ffJ X with hJdef
  have hoffR : ∀ A, IsFFStarOffender X A → ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := by
    intro A hA a ha r hr
    have h := commutator_eq_bot_of_nilpotent hV hA hRn hRodd hR3 (hA.1.trans hXR)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact Subgroup.mem_centralizer_iff.mp (h hr) a ha
  have hJR : ∀ j ∈ J, ∀ r ∈ R, j * r = r * j := by
    intro j hj r hr
    have hle : J ≤ Subgroup.centralizer (R : Set (MulAut V)) :=
      iSup₂_le fun A hA a ha => Subgroup.mem_centralizer_iff.mpr fun r hr =>
        (hoffR A hA a ha r hr).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hj) r hr).symm
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : X ≤ Subgroup.normalizer (J : Set (MulAut V)) := B6.le_normalizer_ffJ X
  set N := ⁅K, J⁆ with hNdef
  have hNK : N ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp (hJX.trans hXK)
  have hNJ : N ≤ J := by
    rw [hNdef, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hKX.trans hXJ)
  have hKN : K ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun k hk =>
    mem_normalizer_commutator (hXK (hKX hk)) (hXJ (hKX hk))
  have hNn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hMn : ((N.subgroupOf K).map f).Normal := hNn.map f hf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hMn with hM | hM
  ·
    right
    have hKJR : K ≤ J ⊔ R := by
      intro k hk
      have h1 : f ⟨k, hk⟩ ∈ (N.subgroupOf K).map f := hM ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hfn⟩ := h1
      have h2 : n⁻¹ * ⟨k, hk⟩ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, inv_mul_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at h2
      have e : k = (n : MulAut V) * ((n : MulAut V)⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (hNJ hn) h2
    have hKJ := le_of_le_sup_of_perfect hperf hJR IsNilpotent.to_isSolvable hKJR
    exact ⟨hKJ, fun r hr k hk => (hJR k (hKJ hk) r hr).symm⟩
  ·
    left
    have hoffK : ∀ A, IsFFStarOffender X A → ∀ a ∈ A, ∀ k ∈ K, a * k = k * a := by
      intro A hA a ha
      have haJ : a ∈ J := B6.le_ffJ hA ha
      have haK : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk =>
        (Subgroup.mem_normalizer_iff.mp (hXK (hA.1 ha)) k).mp hk
      have hcen : ∀ (k : MulAut V) (hk : k ∈ K),
          f ⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩ ∈ Subgroup.center Q := by
        intro k hk
        refine hM ⟨⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        show ⁅a, k⁆ ∈ N
        rw [hNdef, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator haJ hk
      have hR' : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ R := fun k hk => by
        have h := comm_mem_ker_of_central hperf haK f hcen k hk
        have h' : (⟨a * k * a⁻¹ * k⁻¹, K.mul_mem (haK k hk) (K.inv_mem hk)⟩ : ↥K) ∈ f.ker := h
        rw [hker, Subgroup.mem_subgroupOf] at h'
        exact h'
      exact commute_of_sq_eq_one (hA.2.2.1.2 a ha) hRodd (fun r hr => hoffR A hA a ha r hr) hR'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    have hle : J ≤ Subgroup.centralizer (K : Set (MulAut V)) :=
      iSup₂_le fun A hA a ha => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (hoffK A hA a ha k hk).symm
    exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
      (Subgroup.mem_centralizer_iff.mp (hle hj) k hk).symm

end Dichotomy

end CFSG.Quasithin.H13.Ch9.KGFF
