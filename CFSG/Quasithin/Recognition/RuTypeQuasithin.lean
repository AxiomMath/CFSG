module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.RuTypeJ31c


public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Group G] [Finite G] in
theorem pow_lt_sq_of_dvd {p k n : ℕ} (hp : p.Prime) (hn : ¬ p ^ 2 ∣ n) (h : p ^ k ∣ n) :
    p ^ k < p ^ 2 := by
  have hk : k < 2 := by
    by_contra hk
    exact hn ((pow_dvd_pow p (not_lt.mp hk)).trans h)
  exact Nat.pow_lt_pow_right hp.one_lt hk

theorem isQuasithinSub_of_card_lt
    (h : ∀ u : G, u ^ 2 = 1 → u ≠ 1 → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ B : Subgroup G,
      IsPGroup p B → (∀ b ∈ B, b * u = u * b) → Nat.card B < p ^ 2)
    (X : Subgroup G) : IsQuasithinSub X := by
  intro p hp hp2 R hRX hR hR2
  have : Fact p.Prime := ⟨hp⟩
  apply csSup_le'
  rintro k ⟨E, hEX, hEab, hEk⟩
  by_contra hk
  push Not at hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 3)
    (by rw [hEk]; exact pow_dvd_pow p hk)
  set E' : Subgroup G := K.map E.subtype with hE'
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE', Subgroup.card_map_of_injective E.subtype_injective, hK]
  have hE'E : E' ≤ E := Subgroup.map_subtype_le K
  have hE'N : E' ≤ Subgroup.normalizer (R : Set G) := hE'E.trans (hEX.trans inf_le_right)
  have : IsMulCommutative E' := ⟨⟨fun a b => Subtype.ext (by
    have := congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, hE'E a.2⟩ ⟨b, hE'E b.2⟩)
    exact this)⟩⟩
  have hA : IsPGroup p E' := IsPGroup.of_card hE'c
  let f : E' →* MulAut R := (autNHom R).comp (Subgroup.inclusion hE'N)
  let _ : MulDistribMulAction E' R := MulDistribMulAction.compHom R f
  have hsmul : ∀ (e : E') (r : R), ((e • r : R) : G) = (e : G) * r * (e : G)⁻¹ := by
    intro e r
    show ((autNHom R (Subgroup.inclusion hE'N e) r : R) : G) = _
    rw [autNHom_apply]
    rfl
  have hRp : ¬ p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hgen := a117_generation (A := E') hA (G := R) hRp
  obtain ⟨D, hDc, hDR⟩ : ∃ D : Subgroup E', IsCyclic (E' ⧸ D) ∧
      fixedPointSubgroup D R ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hbot : (⨆ (B : Subgroup E') (_ : IsCyclic (E' ⧸ B) ∧ fixedPointSubgroup B R ≠ ⊥),
        fixedPointSubgroup B R) = ⊥ :=
      iSup₂_eq_bot.mpr fun B hB => absurd (hno B hB.1) hB.2
    rw [hgen] at hbot
    apply hR
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : R) ∈ (⊥ : Subgroup R) := by
      rw [← hbot]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hDcard : p ^ 2 ≤ Nat.card D := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E' ⧸ D)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    have ha : a ^ p = 1 := Subtype.ext (by
      have := hEab.2 (a : G) (hE'E a.2)
      simpa using this)
    have hgp : (a : E' ⧸ D) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
    have hc : Nat.card (E' ⧸ D) ≤ p := Nat.le_of_dvd hp.pos (by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one hgp)
    have he := Subgroup.card_eq_card_quotient_mul_card_subgroup D
    rw [hE'c] at he
    have : p * p ^ 2 ≤ p * Nat.card D := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ = Nat.card (E' ⧸ D) * Nat.card D := he
        _ ≤ p * Nat.card D := Nat.mul_le_mul_right _ hc
    exact Nat.le_of_mul_le_mul_left this hp.pos
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ fixedPointSubgroup D R, r ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hDR ((Subgroup.eq_bot_iff_forall _).mpr hno)
  have hrc : ∀ d ∈ D, ((d : E') : G) * r = r * ((d : E') : G) := by
    intro d hd
    have h1 : d • r = r := hr ⟨d, hd⟩
    have h2 : ((d : E') : G) * (r : G) * ((d : E') : G)⁻¹ = r := by
      rw [← hsmul]
      exact congrArg Subtype.val h1
    calc ((d : E') : G) * r = ((d : E') : G) * (r : G) * ((d : E') : G)⁻¹ * (d : E') := by
          group
      _ = r * ((d : E') : G) := by rw [h2]
  obtain ⟨n, hn⟩ := hR2 r
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hm
    exact hr1 hm
  have hmo : orderOf (r : G) = 2 ^ m := by rw [Subgroup.orderOf_coe]; exact hm
  set u : G := (r : G) ^ 2 ^ (m - 1) with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hm1, ← hmo, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hmo]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  set B : Subgroup G := D.map E'.subtype with hB
  have hBc : Nat.card B = Nat.card D := by
    rw [hB, Subgroup.card_map_of_injective E'.subtype_injective]
  have hBp : IsPGroup p B := (hA.to_subgroup D).map E'.subtype
  have hBu : ∀ b ∈ B, b * u = u * b := by
    rintro _ ⟨d, hd, rfl⟩
    exact (Commute.pow_right (show Commute ((d : E') : G) (r : G) from hrc d hd) _).eq
  have := h u hu2 hu1 p hp hp2 B hBp hBu
  omega

theorem not_sq_dvd_card_H {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 2 ^ 11 * 120 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 14) :=
    Nat.Coprime.pow 2 14 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h' : p ^ 2 ∣ 3 * 5 :=
    hcop.dvd_of_dvd_mul_left (by rw [show 2 ^ 14 * (3 * 5) = 2 ^ 11 * 120 by norm_num]; exact h)
  rcases (Nat.Prime.dvd_mul hp).mp ((dvd_pow_self p two_ne_zero).trans h') with h3 | h5
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3] at h'
    norm_num at h'
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5] at h'
    norm_num at h'

theorem not_sq_dvd_card_Ls {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 29120 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 6) :=
    Nat.Coprime.pow 2 6 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h' : p ^ 2 ∣ 5 * 7 * 13 :=
    hcop.dvd_of_dvd_mul_left (by rw [show 2 ^ 6 * (5 * 7 * 13) = 29120 by norm_num]; exact h)
  have hp' := (dvd_pow_self p two_ne_zero).trans h'
  rcases (Nat.Prime.dvd_mul hp).mp hp' with h57 | h13
  · rcases (Nat.Prime.dvd_mul hp).mp h57 with h5 | h7
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5] at h'
      norm_num at h'
    · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7] at h'
      norm_num at h'
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13] at h'
    norm_num at h'

namespace RuDataM

variable (M : RuDataM G)

include M in
theorem card_lt_of_centralizes
    {u : G} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B : Subgroup G} (hB : IsPGroup p B) (hBu : ∀ b ∈ B, b * u = u * b) :
    Nat.card B < p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial M.S0 :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [M.card_S0]; norm_num)
  obtain ⟨⟨s, hs⟩, hs1⟩ := exists_ne (1 : M.S0)
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  rw [hk]
  rcases (M.lemma_J27_4 hs hs1').2 u hu2 hu1 with hz | hsu
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz
    set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
    have hB'c : Nat.card B' = Nat.card B := by
      rw [hB', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    have hle : B' ≤ ruH M.T := by
      rw [← M.centralizer_z_eq_H]
      rintro _ ⟨b, hb, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hBu b hb
      rw [← hg] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * b * g * M.z = g⁻¹ * (b * (g * M.z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * M.z * g⁻¹) * b) * g := by rw [h1]
        _ = M.z * (g⁻¹ * b * g) := by group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hB'c, hk, M.toRuData.card_H] at hdvd
    exact pow_lt_sq_of_dvd hp (not_sq_dvd_card_H hp hp2) hdvd
  · obtain ⟨g, hg⟩ := isConj_iff.mp hsu
    set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
    have hB'c : Nat.card B' = Nat.card B := by
      rw [hB', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    have hodd : Odd (Nat.card B') := by
      rw [hB'c, hk]
      exact (hp.odd_of_ne_two hp2).pow
    have hle : B' ≤ Ls s := by
      intro x hx
      have hxC : x ∈ Cen s := by
        obtain ⟨b, hb, rfl⟩ := hx
        rw [mem_Cen]
        have h1 := hBu b hb
        rw [← hg] at h1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc g⁻¹ * b * g * s = g⁻¹ * (b * (g * s * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * s * g⁻¹) * b) * g := by rw [h1]
          _ = s * (g⁻¹ * b * g) := by group
      obtain ⟨a, ha, l, hl, rfl⟩ := M.exists_S0_mul_Ls hs hs1' hxC
      have hpow : (a * l) ^ Nat.card B' = 1 := by
        have := congrArg Subtype.val (pow_card_eq_one' (G := B') (x := ⟨a * l, hx⟩))
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        exact this
      have hal : Commute a l := M.comm_S0_Ls hs hs1' ha hl
      rw [hal.mul_pow] at hpow
      obtain ⟨t, ht⟩ := hodd
      have ha2 : a ^ 2 = 1 := M.S0_elem.2 a ha
      have haN : a ^ Nat.card B' = a := by
        rw [ht, pow_succ, pow_mul, ha2, one_pow, one_mul]
      rw [haN] at hpow
      have haL : a ∈ Ls s := by
        rw [eq_inv_of_mul_eq_one_left hpow]
        exact inv_mem (pow_mem hl _)
      rw [M.S0_inf_Ls hs hs1' ha haL, one_mul]
      exact hl
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hB'c, hk, M.card_Ls hs hs1'] at hdvd
    exact pow_lt_sq_of_dvd hp (not_sq_dvd_card_Ls hp hp2) hdvd

end RuDataM

theorem isQuasithinSub_of_isTypeRu
    (h : IsTypeRu G) (X : Subgroup G) : IsQuasithinSub X := by
  obtain ⟨M⟩ := nonempty_ruDataM h
  exact isQuasithinSub_of_card_lt (fun u hu2 hu1 p hp hp2 B hB hBu =>
    M.card_lt_of_centralizes hu2 hu1 hp hp2 hB hBu) X

end CFSG.Quasithin.RuType
