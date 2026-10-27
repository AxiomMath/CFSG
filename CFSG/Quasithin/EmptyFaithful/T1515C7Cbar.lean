module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Grp
public import CFSG.Quasithin.EmptyFaithful.T1515C6Grp

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section SevenCbar

variable {V : Type} [CommGroup V]

namespace SevenCtx

variable {A Tb : Subgroup (MulAut V)} {t : MulAut V} [Finite V] (h : SevenCtx A Tb t)
include h

theorem no_central_complement {Q : Subgroup (MulAut V)} (hQP : Q ≤ oTwoUpper A)
    (hinf : Q ⊓ frattiniIn (oTwoUpper A) = ⊥) (hsup : Q ⊔ frattiniIn (oTwoUpper A) = oTwoUpper A) :
    False := by
  have hcomm : ∀ q ∈ Q, ∀ c ∈ frattiniIn (oTwoUpper A), q * c = c * q := fun q hq c hc =>
    h.Z_central hc (hQP hq)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q (frattiniIn (oTwoUpper A))
    hcomm
  have hQab : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ hq₁ q₂ hq₂
    have h1 : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ ∈ frattiniIn (oTwoUpper A) := h.comm_mem_Z (hQP hq₁) (hQP hq₂)
    have h2 : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁))
      (Q.inv_mem hq₂)
    have h3 : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ ∈ Q ⊓ frattiniIn (oTwoUpper A) := ⟨h2, h1⟩
    rw [hinf, Subgroup.mem_bot] at h3
    calc q₁ * q₂ = (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) * q₂ * q₁ := by group
      _ = q₂ * q₁ := by rw [h3]; group
  obtain ⟨a₀, b₀, hab⟩ := A1c.exists_not_commute_of_isPOnePlusTwo h.P1
  have haP : (a₀ : MulAut V) ∈ (oTwoUpper A : Set (MulAut V)) := a₀.2
  have hbP : (b₀ : MulAut V) ∈ (oTwoUpper A : Set (MulAut V)) := b₀.2
  have hset' : ((Q ⊔ frattiniIn (oTwoUpper A) : Subgroup (MulAut V)) : Set (MulAut V)) =
      (Q : Set (MulAut V)) * (frattiniIn (oTwoUpper A) : Set (MulAut V)) := hset
  rw [hsup] at hset'
  have ha : (a₀ : MulAut V) ∈ (Q : Set (MulAut V)) * (frattiniIn (oTwoUpper A) : Set (MulAut V)) := by
    rw [← hset']; exact haP
  have hb : (b₀ : MulAut V) ∈ (Q : Set (MulAut V)) * (frattiniIn (oTwoUpper A) : Set (MulAut V)) := by
    rw [← hset']; exact hbP
  obtain ⟨q₁, hq₁, c₁, hc₁, h₁⟩ := ha
  obtain ⟨q₂, hq₂, c₂, hc₂, h₂⟩ := hb
  apply hab
  apply Subtype.ext
  show (a₀ : MulAut V) * b₀ = b₀ * a₀
  rw [← h₁, ← h₂]
  have hc₁q : ∀ q ∈ Q, c₁ * q = q * c₁ := fun q hq => (hcomm q hq c₁ hc₁).symm
  have hc₂q : ∀ q ∈ Q, c₂ * q = q * c₂ := fun q hq => (hcomm q hq c₂ hc₂).symm
  have hcc : c₁ * c₂ = c₂ * c₁ := h.Z_central hc₂ (h.Z_le_P hc₁)
  calc q₁ * c₁ * (q₂ * c₂) = q₁ * (c₁ * q₂) * c₂ := by group
    _ = q₁ * (q₂ * c₁) * c₂ := by rw [hc₁q q₂ hq₂]
    _ = (q₁ * q₂) * (c₁ * c₂) := by group
    _ = (q₂ * q₁) * (c₂ * c₁) := by rw [hQab q₁ hq₁ q₂ hq₂, hcc]
    _ = q₂ * (q₁ * c₂) * c₁ := by group
    _ = q₂ * (c₂ * q₁) * c₁ := by rw [hc₂q q₁ hq₁]
    _ = q₂ * c₂ * (q₁ * c₁) := by group

end SevenCtx

namespace SevenGen

variable {A Tb : Subgroup (MulAut V)} {t τ x y z : MulAut V} [Finite V] (h : SevenCtx A Tb t)
  (g : SevenGen A Tb τ x y z)
include h g

omit [Finite V] h in
theorem y_ne_one : y ≠ 1 := by
  intro hy
  apply g.z1
  rw [g.zdef, hy]
  group

theorem card_Q : Nat.card (oTwoUpper A ⊓ fixingV (fixOf y : Set V) : Subgroup (MulAut V)) = 3 := by
  set Q : Subgroup (MulAut V) := oTwoUpper A ⊓ fixingV (fixOf y : Set V) with hQ
  have hy3 := y3 h g
  have hzy : Subgroup.zpowers y ≤ Q := by
    rw [Subgroup.zpowers_le]
    exact ⟨g.yP, fun c hc => hc⟩
  have hy1 := y_ne_one g
  have hQ3 : 3 ≤ Nat.card Q := by
    have := Subgroup.card_le_of_le hzy
    rwa [card_pow_gen hy3 hy1] at this
  have hQP : Q ≤ oTwoUpper A := inf_le_left
  have hQd : Nat.card Q ∣ 27 := by
    rw [← h.card_P]
    exact Subgroup.card_dvd_of_le hQP
  have hQZ : Q ⊓ frattiniIn (oTwoUpper A) = ⊥ := by
    set K := Q ⊓ frattiniIn (oTwoUpper A) with hK
    have hKd : Nat.card K ∣ 3 := by
      rw [← h.card_Z]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hKd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hKZ : K = frattiniIn (oTwoUpper A) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, h.card_Z])
      have hzK : z ∈ K := by rw [hKZ]; exact g.zZ
      have hzfix : z ∈ fixingV (fixOf y : Set V) := hzK.1.2
      have hbot : fixOf y = ⊥ := by
        rw [eq_bot_iff]
        intro c hc
        exact Subgroup.mem_bot.mpr (fpf_z' h g c (hzfix c hc))
      have := (card_fix_y' h g).1
      rw [hbot, Subgroup.card_bot] at this
      omega
  have hcomm : ∀ q ∈ Q, ∀ c ∈ frattiniIn (oTwoUpper A), q * c = c * q := fun q hq c hc =>
    h.Z_central hc (hQP hq)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q
    (frattiniIn (oTwoUpper A)) hcomm
  rw [hQZ, Subgroup.card_bot, mul_one, h.card_Z] at hcard
  have hsupP : Q ⊔ frattiniIn (oTwoUpper A) ≤ oTwoUpper A := sup_le hQP (h.Z_le_P)
  have hsupd : Nat.card (Q ⊔ frattiniIn (oTwoUpper A) : Subgroup (MulAut V)) ∣ 27 := by
    rw [← h.card_P]
    exact Subgroup.card_dvd_of_le hsupP
  have hle9 : Nat.card Q ≤ 9 := by
    have := Nat.le_of_dvd (by norm_num) hsupd
    omega
  have hne9 : Nat.card Q ≠ 9 := by
    intro h9
    have h27 : Nat.card (Q ⊔ frattiniIn (oTwoUpper A) : Subgroup (MulAut V)) = 27 := by omega
    have hsupeq : Q ⊔ frattiniIn (oTwoUpper A) = oTwoUpper A :=
      Subgroup.eq_of_le_of_card_ge hsupP (by rw [h27, h.card_P])
    exact h.no_central_complement hQP hQZ hsupeq
  generalize Nat.card Q = n at *
  interval_cases n <;> simp_all

theorem Q_inf_Z : (oTwoUpper A ⊓ fixingV (fixOf y : Set V) : Subgroup (MulAut V)) ⊓
    frattiniIn (oTwoUpper A) = ⊥ := by
  set Q : Subgroup (MulAut V) := oTwoUpper A ⊓ fixingV (fixOf y : Set V) with hQ
  set K := Q ⊓ frattiniIn (oTwoUpper A) with hK
  have hKd : Nat.card K ∣ 3 := by
    rw [← h.card_Z]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hKd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have hKZ : K = frattiniIn (oTwoUpper A) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, h.card_Z])
    have hzK : z ∈ K := by rw [hKZ]; exact g.zZ
    have hzfix : z ∈ fixingV (fixOf y : Set V) := hzK.1.2
    have hbot : fixOf y = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      exact Subgroup.mem_bot.mpr (fpf_z' h g c (hzfix c hc))
    have := (card_fix_y' h g).1
    rw [hbot, Subgroup.card_bot] at this
    omega

theorem CP_eq : oTwoUpper A ⊓ fixingV (fixOf y : Set V) = Subgroup.zpowers y := by
  have hle : Subgroup.zpowers y ≤ oTwoUpper A ⊓ fixingV (fixOf y : Set V) := by
    rw [Subgroup.zpowers_le]
    exact ⟨g.yP, fun c hc => hc⟩
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_Q h g, card_pow_gen (y3 h g) (y_ne_one g)])).symm

omit [Finite V] h in
theorem tau_inv_eq : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right g.tau_sq

theorem hzinv_pow (j : ℕ) : (z ^ j)⁻¹ = z ^ (2 * j) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add]
  have : j + 2 * j = 3 * j := by ring
  rw [this, pow_mul, z3 h g, one_pow]

theorem mem_Cbar {a : MulAut V} (ha : a ∈ A) (hfix : a ∈ fixingV (fixOf y : Set V)) :
    ∃ i e : ℕ, e < 2 ∧ a = y ^ i * τ ^ e := by
  obtain ⟨p, hp, u, hu, rfl⟩ := h.mem_A ha
  have hτi := tau_inv_eq g
  have hy1 := y_ne_one g
  have hy3 := y3 h g
  have hz3 := z3 h g
  have hac : ∀ c ∈ fixOf y, (p * u) c = c := fun c hc => hfix c hc
  have hainv : ∀ c ∈ fixOf y, (p * u)⁻¹ c = c := by
    intro c hc
    calc (p * u)⁻¹ c = (p * u)⁻¹ ((p * u) c) := by rw [hac c hc]
      _ = c := by simp
  have hfixy : ∀ c ∈ fixOf y, y c = c := fun c hc => hc
  have hfixz : ∀ c ∈ fixOf y, z c ∈ fixOf y := fun c hc =>
    apply_mem_fixOf_of_commute (yz h g).symm hc
  have hay : (p * u) * y * (p * u)⁻¹ ∈ Subgroup.zpowers y := by
    rw [← CP_eq h g]
    refine ⟨SevenCtx.P_conj ha g.yP, fun c hc => ?_⟩
    show ((p * u) * y * (p * u)⁻¹) c = c
    show (p * u) (y ((p * u)⁻¹ c)) = c
    rw [hainv c hc, hfixy c hc, hac c hc]
  obtain ⟨lam, hlam⟩ : ∃ l : ℕ, (p * u) * y * (p * u)⁻¹ = y ^ l := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hay
    obtain ⟨l, hl⟩ := exists_nat_pow_eq_zpow hy3 hy1 m
    exact ⟨l, by rw [← hm, hl]⟩
  have hlam0 : lam % 3 ≠ 0 := by
    intro h0
    have h1y : y ^ lam = 1 := pow_eq_one_of_mod_three hy3 h0
    apply hy1
    have h1 : (p * u) * y * (p * u)⁻¹ = 1 := by rw [hlam, h1y]
    calc y = (p * u)⁻¹ * ((p * u) * y * (p * u)⁻¹) * (p * u) := by group
      _ = 1 := by rw [h1]; group
  have huz : u * z = z * u := by
    have haz : (p * u) * z * (p * u)⁻¹ = z := by
      have hZ : (p * u) * z * (p * u)⁻¹ ∈ frattiniIn (oTwoUpper A) := h.Z_conj ha g.zZ
      have hkZ : z⁻¹ * ((p * u) * z * (p * u)⁻¹) ∈ frattiniIn (oTwoUpper A) :=
        (frattiniIn (oTwoUpper A)).mul_mem ((frattiniIn (oTwoUpper A)).inv_mem g.zZ) hZ
      have hkQ : z⁻¹ * ((p * u) * z * (p * u)⁻¹) ∈ fixingV (fixOf y : Set V) := by
        intro c hc
        show z⁻¹ (((p * u) * z * (p * u)⁻¹) c) = c
        show z⁻¹ ((p * u) (z ((p * u)⁻¹ c))) = c
        rw [hainv c hc, hac _ (hfixz c hc)]
        simp
      have hkQ' : z⁻¹ * ((p * u) * z * (p * u)⁻¹) ∈
          (oTwoUpper A ⊓ fixingV (fixOf y : Set V)) ⊓ frattiniIn (oTwoUpper A) :=
        ⟨⟨h.Z_le_P hkZ, hkQ⟩, hkZ⟩
      rw [Q_inf_Z h g, Subgroup.mem_bot] at hkQ'
      calc (p * u) * z * (p * u)⁻¹ = z * (z⁻¹ * ((p * u) * z * (p * u)⁻¹)) := by group
        _ = z := by rw [hkQ']; group
    have huzZ : u * z * u⁻¹ ∈ frattiniIn (oTwoUpper A) := h.Z_conj (h.Tb_le hu) g.zZ
    have hpc : p * (u * z * u⁻¹) * p⁻¹ = u * z * u⁻¹ := by
      have := h.Z_central huzZ hp
      calc p * (u * z * u⁻¹) * p⁻¹ = (p * (u * z * u⁻¹)) * p⁻¹ := rfl
        _ = ((u * z * u⁻¹) * p) * p⁻¹ := by rw [this]
        _ = u * z * u⁻¹ := by group
    have e1 : p * (u * z * u⁻¹) * p⁻¹ = z := by
      calc p * (u * z * u⁻¹) * p⁻¹ = (p * u) * z * (p * u)⁻¹ := by group
        _ = z := haz
    rw [hpc] at e1
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [e1]
  have hcomZ : (y ^ lam)⁻¹ * (p⁻¹ * y ^ lam * p) ∈ frattiniIn (oTwoUpper A) := by
    have := h.comm_mem_Z (p := (y ^ lam)⁻¹) (q := p⁻¹)
      ((oTwoUpper A).inv_mem ((oTwoUpper A).pow_mem g.yP lam)) ((oTwoUpper A).inv_mem hp)
    simpa [mul_assoc] using this
  obtain ⟨j, hj⟩ := Z_pow h g hcomZ
  have huy : u * y * u⁻¹ = y ^ lam * z ^ j := by
    have e : (p * u) * y * (p * u)⁻¹ = p * (u * y * u⁻¹) * p⁻¹ := by group
    have e2 : u * y * u⁻¹ = p⁻¹ * y ^ lam * p := by
      calc u * y * u⁻¹ = p⁻¹ * (p * (u * y * u⁻¹) * p⁻¹) * p := by group
        _ = p⁻¹ * ((p * u) * y * (p * u)⁻¹) * p := by rw [e]
        _ = p⁻¹ * y ^ lam * p := by rw [hlam]
    calc u * y * u⁻¹ = y ^ lam * ((y ^ lam)⁻¹ * (p⁻¹ * y ^ lam * p)) := by rw [e2]; group
      _ = y ^ lam * z ^ j := by rw [hj]
  have hu_cases : u = 1 ∨ u = τ := by
    have hl : lam % 3 = 1 ∨ lam % 3 = 2 := by omega
    rcases hl with hl | hl
    · left
      have hyl : y ^ lam = y := by rw [pow_eq_pow_mod lam hy3, hl, pow_one]
      rw [hyl] at huy
      exact eq_one_of_comm h g hu huz huy
    · right
      have hyl : y ^ lam = y⁻¹ := by
        rw [pow_eq_pow_mod lam hy3, hl]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_succ, hy3]
      have hu'T : u * τ ∈ Tb := Tb.mul_mem hu g.tau_mem
      have hu'z : (u * τ) * z = z * (u * τ) := by
        calc (u * τ) * z = u * (τ * z) := by group
          _ = u * (z * τ) := by rw [g.tau_z]
          _ = (u * z) * τ := by group
          _ = (z * u) * τ := by rw [huz]
          _ = z * (u * τ) := by group
      have hu'y : (u * τ) * y * (u * τ)⁻¹ = y * z ^ (2 * j) := by
        calc (u * τ) * y * (u * τ)⁻¹ = u * (τ * y * τ⁻¹) * u⁻¹ := by group
          _ = (u * y * u⁻¹)⁻¹ := by rw [g.tau_y]; group
          _ = (y⁻¹ * z ^ j)⁻¹ := by rw [huy, hyl]
          _ = (z ^ j)⁻¹ * y := by group
          _ = z ^ (2 * j) * y := by rw [hzinv_pow h g j]
          _ = y * z ^ (2 * j) := by
              have := (Commute.pow_left (show Commute z y from (yz h g).symm) (2 * j)).eq
              exact this
      have h1 := eq_one_of_comm h g hu'T hu'z hu'y
      calc u = (u * τ) * τ⁻¹ := by group
        _ = τ := by rw [h1, hτi]; group
  rcases hu_cases with hu1 | hu1
  · subst hu1
    have hpQ : p ∈ oTwoUpper A ⊓ fixingV (fixOf y : Set V) :=
      ⟨hp, fun c hc => by simpa using hac c hc⟩
    rw [CP_eq h g] at hpQ
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hpQ
    obtain ⟨i, hi⟩ := exists_nat_pow_eq_zpow hy3 hy1 m
    exact ⟨i, 0, by norm_num, by rw [pow_zero, mul_one, mul_one, ← hm, hi]⟩
  · have hτc : ∀ c ∈ fixOf y, τ c = c := tau_fix_y h g
    have hpQ : p ∈ oTwoUpper A ⊓ fixingV (fixOf y : Set V) := by
      refine ⟨hp, fun c hc => ?_⟩
      have h1 : (p * u) c = c := hac c hc
      have h2 : u c = c := by rw [hu1]; exact hτc c hc
      have h3 : (p * u) c = p (u c) := rfl
      rw [h3, h2] at h1
      exact h1
    rw [CP_eq h g] at hpQ
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hpQ
    obtain ⟨i, hi⟩ := exists_nat_pow_eq_zpow hy3 hy1 m
    exact ⟨i, 1, by norm_num, by rw [hu1, pow_one, ← hm, hi]⟩

omit [Finite V] h in
theorem y_mem_Cbar : y ∈ sixCbar A (fixOf y) :=
  ⟨oTwoUpper_le A g.yP, fun _ hc => hc⟩

theorem tau_mem_Cbar : τ ∈ sixCbar A (fixOf y) :=
  ⟨h.Tb_le g.tau_mem, tau_fix_y h g⟩

theorem Cbar_eq : sixCbar A (fixOf y) = Subgroup.zpowers y ⊔ Subgroup.zpowers τ := by
  apply le_antisymm
  · rintro a ⟨ha, hfix⟩
    obtain ⟨i, e, he, rfl⟩ := mem_Cbar h g ha hfix
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) e)
  · exact sup_le (Subgroup.zpowers_le.mpr (y_mem_Cbar g)) (Subgroup.zpowers_le.mpr (tau_mem_Cbar h g))

omit [Finite V] h in
theorem card_zpowers_tau : Nat.card (Subgroup.zpowers τ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact g.tau_sq) g.tau_ne

theorem T0_eq : Tb ⊓ fixingV (fixOf y : Set V) = Subgroup.zpowers τ := by
  apply le_antisymm
  · rintro u ⟨hu, hufix⟩
    obtain ⟨i, e, he, hue⟩ := mem_Cbar h g (h.Tb_le hu) hufix
    have hτe : τ ^ e ∈ Tb := Tb.pow_mem g.tau_mem e
    have hyi : y ^ i ∈ oTwoUpper A ⊓ Tb := by
      refine ⟨(oTwoUpper A).pow_mem g.yP i, ?_⟩
      have : y ^ i = u * (τ ^ e)⁻¹ := by rw [hue]; group
      rw [this]
      exact Tb.mul_mem hu (Tb.inv_mem hτe)
    rw [h.P_inf_Tb, Subgroup.mem_bot] at hyi
    rw [hue, hyi, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) e
  · rw [Subgroup.zpowers_le]
    exact ⟨g.tau_mem, tau_fix_y h g⟩

omit [Finite V] h in
theorem tau_normalizes : Subgroup.zpowers τ ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (MulAut V)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  have hτi := tau_inv_eq g
  intro w
  have key : ∀ m : ℤ, τ * y ^ m * τ⁻¹ = (y⁻¹) ^ m := by
    intro m
    rw [← g.tau_y, conj_zpow]
  constructor
  · intro hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [key]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) m
  · intro hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
    have : w = τ * (τ * w * τ⁻¹) * τ⁻¹ := by
      calc w = (τ * τ) * w * (τ⁻¹ * τ⁻¹) := by rw [g.tau_sq, hτi, g.tau_sq]; group
        _ = τ * (τ * w * τ⁻¹) * τ⁻¹ := by group
    rw [this, ← hm, key]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) m

theorem card_Cbar : Nat.card (sixCbar A (fixOf y)) = 6 := by
  have hy3 := y3 h g
  have hy1 := y_ne_one g
  have hbot : Subgroup.zpowers τ ⊓ Subgroup.zpowers y = ⊥ := by
    set K := Subgroup.zpowers τ ⊓ Subgroup.zpowers y with hK
    have hd2 : Nat.card K ∣ 2 := by
      rw [← card_zpowers_tau g]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hd3 : Nat.card K ∣ 3 := by
      rw [← card_pow_gen hy3 hy1]
      exact Subgroup.card_dvd_of_le inf_le_right
    have : Nat.card K = 1 := by
      have := Nat.dvd_gcd hd2 hd3
      simpa using this
    exact Subgroup.card_eq_one.mp this
  have hrel := A4.relIndex_sup_eq_of_le_normalizer' (tau_normalizes g)
  have hc1 := Subgroup.relIndex_mul_card (Subgroup.zpowers y) (Subgroup.zpowers τ)
  rw [inf_comm, hbot, Subgroup.card_bot, mul_one] at hc1
  have hc2 := Subgroup.relIndex_mul_card (Subgroup.zpowers y)
    (Subgroup.zpowers τ ⊔ Subgroup.zpowers y)
  rw [inf_of_le_left le_sup_right, hrel, hc1, card_pow_gen hy3 hy1] at hc2
  rw [Cbar_eq h g, sup_comm]
  rw [← hc2, card_zpowers_tau g]

theorem odd_mem_Cbar {a : MulAut V} (ha : a ∈ sixCbar A (fixOf y)) (hao : Odd (orderOf a)) :
    a ∈ Subgroup.zpowers y := by
  obtain ⟨haA, hfix⟩ := ha
  obtain ⟨i, e, he, rfl⟩ := mem_Cbar h g haA hfix
  interval_cases e
  · rw [pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i
  · have hconj : τ * y ^ i * τ⁻¹ = (y ^ i)⁻¹ := by rw [← inv_pow, ← g.tau_y, conj_pow]
    have key : ∀ a s : MulAut V, (a * s) * (a * s) = a * (s * a * s⁻¹) * (s * s) := by
      intro a s
      group
    have hx2 : (y ^ i * τ ^ 1) * (y ^ i * τ ^ 1) = 1 := by
      rw [pow_one]
      calc (y ^ i * τ) * (y ^ i * τ) = y ^ i * (τ * y ^ i * τ⁻¹) * (τ * τ) := key _ _
        _ = 1 := by rw [hconj, g.tau_sq]; group
    have hd : orderOf (y ^ i * τ ^ 1) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · rw [h2] at hao
      exact absurd hao (by decide)

theorem oTwoUpper_Cbar : oTwoUpper (sixCbar A (fixOf y)) = Subgroup.zpowers y := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun a ha => odd_mem_Cbar h g ha.1 ha.2
  · rw [Subgroup.zpowers_le]
    refine mem_oTwoUpper_of_odd (y_mem_Cbar g) ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime (y3 h g) (y_ne_one g)]
    decide

end SevenGen

end SevenCbar

end CFSG.Quasithin
