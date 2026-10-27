module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreTwelveA
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B55

section Aux

variable {Ω : Type*} [Group Ω]

theorem pow_eq_one_of_mem_iSup (n : ℕ) (𝓕 : Finset (Subgroup Ω))
    (hn : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1)
    (hc : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) :
    ∀ x ∈ ⨆ H ∈ 𝓕, H, x ^ n = 1 := by
  classical
  induction 𝓕 using Finset.induction_on with
  | empty =>
    intro x hx
    have : (⨆ H ∈ (∅ : Finset (Subgroup Ω)), H) = ⊥ := by simp
    rw [this, Subgroup.mem_bot] at hx
    rw [hx, one_pow]
  | insert H₀ 𝓕 hH₀ ih =>
    intro x hx
    rw [Finset.iSup_insert] at hx
    have hn' : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1 := fun H hH => hn H (Finset.mem_insert_of_mem hH)
    have hc' : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a :=
      fun H hH H' hH' => hc H (Finset.mem_insert_of_mem hH) H' (Finset.mem_insert_of_mem hH')
    have hK : (⨆ H ∈ 𝓕, H) ≤ Subgroup.centralizer (H₀ : Set Ω) := by
      refine iSup₂_le fun H hH => ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hne : H₀ ≠ H := fun h => hH₀ (h ▸ hH)
      exact hc H₀ (Finset.mem_insert_self _ _) H (Finset.mem_insert_of_mem hH) hne a ha b hb
    have hnorm : (⨆ H ∈ 𝓕, H) ≤ Subgroup.normalizer (H₀ : Set Ω) :=
      hK.trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨h, hh, k, hk, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hnorm).1 hx
    have hcomm : Commute h k := Subgroup.mem_centralizer_iff.1 (hK hk) h hh
    rw [hcomm.mul_pow, hn H₀ (Finset.mem_insert_self _ _) h hh, ih hn' hc' k hk, one_mul]

theorem odd_orderOf_of_isPGroup_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {R : Subgroup Ω} (h : IsPGroup p R) {x : Ω} (hx : x ∈ R) : Odd (orderOf x) := by
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 h ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hi
  rw [hi]
  exact Odd.pow (hp.out.odd_of_ne_two hp2)

end Aux

section Six

variable {V : Type} [CommGroup V] [Finite V]

theorem pow_six_eq_one_of_mem_ffJ (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hFF : IsFFModule X) : ∀ x ∈ ffJ X, x ^ 6 = 1 := by
  obtain ⟨𝓗, -, hJ, hcomm, -, -, -, hL2, -⟩ := B1_8 hV hsolv hO2 hFF
  rw [hJ]
  refine pow_eq_one_of_mem_iSup 6 𝓗 (fun H hH x hx => ?_)
    (fun H hH H' hH' hne a ha b hb => hcomm H hH H' hH' hne a ha b hb)
  obtain ⟨e, -, -⟩ := hL2 H hH
  have h6 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), g ^ 6 = 1 := by decide
  have : e (⟨x, hx⟩ ^ 6) = 1 := by rw [map_pow]; exact h6 _
  have h1 : (⟨x, hx⟩ : ↥H) ^ 6 = 1 := e.injective (by rw [this, map_one])
  exact congrArg Subtype.val h1

theorem pCoreOf_le_centralizer (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (hJ : G = ffJ G) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    pCoreOf p G ≤ Subgroup.centralizer (G : Set (MulAut V)) := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pCoreOf p G with hXdef
  have hXG : X ≤ G := CFSG.LieType.BorelTits.pCoreOf_le p G
  have hXp : IsPGroup p ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup p G
  obtain ⟨A, hA, hAX⟩ : ∃ A, IsFFStarOffender G A ∧
      ¬ A ≤ Subgroup.centralizer (X : Set (MulAut V)) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have h1 : ffJ G ≤ Subgroup.centralizer (X : Set (MulAut V)) :=
      iSup_le fun A => iSup_le fun hA => hcon A hA
    rw [← hJ] at h1
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.1 (h1 hg) x hx).symm
  have hAG : A ≤ G := hA.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hA2 : IsPGroup 2 ↥A := hAel.isPGroup
  have hGn : G ≤ Subgroup.normalizer (X : Set (MulAut V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p G
  have hAnX : A ≤ Subgroup.normalizer (X : Set (MulAut V)) := hAG.trans hGn
  set Y := ⁅X, A⁆ with hYdef
  have hYX : Y ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hAnX
  have hYp : IsPGroup p ↥Y := hXp.to_le hYX
  have hYne : Y ≠ ⊥ := by
    intro h
    apply hAX
    rw [hYdef, Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hAnY : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := fun a ha y hy => conj_mem_commutator ha hy
  have hAY : A ≤ Subgroup.normalizer (Y : Set (MulAut V)) := le_normalizer_of_conj hAnY
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥X) := by
    obtain ⟨a, ha⟩ := hA2.exists_card_eq
    obtain ⟨b, hb⟩ := hXp.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  have hYA : ⁅Y, A⁆ ≠ ⊥ := by
    intro h
    have h0 : ⁅⁅X, A⁆, A⁆ = ⊥ := h
    exact hYne (CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot X A
      hAnX hcop h0)
  set G₀ := Y ⊔ A with hG₀def
  have hG₀n : ∀ x ∈ G₀, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    obtain ⟨y', hy', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAY).1 hx
    have e : y' * a * y * (y' * a)⁻¹ = y' * (a * y * a⁻¹) * y'⁻¹ := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hy' (hAnY a ha y hy)) (Y.inv_mem hy')
  have hYodd : ∀ y ∈ Y, Odd (orderOf y) := fun y hy => odd_orderOf_of_isPGroup_odd hp2 hYp hy
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
  have h6 := pow_six_eq_one_of_mem_ffJ (B1.sq_eq_one_sub hV W) hbsolv
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

end Six

end B55

end CFSG.Quasithin
