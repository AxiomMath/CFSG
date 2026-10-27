module

public import CFSG.RankThree.PartOne.S12.Sec13Base
public import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G]

structure ReflCtx (p : ℕ) (E : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  comm : ∀ a b : E, a * b = b * a
  pow : ∀ a : E, a ^ p = 1

namespace ReflCtx

variable {p : ℕ} {E : Subgroup G} (C : ReflCtx p E)

include C

theorem mem_autMoved_iff {t : MulAut E} {x : E} :
    x ∈ autMoved E t ↔ ∃ e : E, x = t e * e⁻¹ := by
  rw [← Sec13Base.range_moveHom C.comm t]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩

theorem mem_autMoved_self {t : MulAut E} (e : E) : t e * e⁻¹ ∈ autMoved E t :=
  (C.mem_autMoved_iff).2 ⟨e, rfl⟩

theorem inv_of_mem_autMoved {t : MulAut E} (htt : t * t = 1) {x : E} (hx : x ∈ autMoved E t) :
    t x = x⁻¹ := by
  obtain ⟨e, rfl⟩ := (C.mem_autMoved_iff).1 hx
  have htte : t (t e) = e := by simpa using congrArg (fun m : MulAut E => m e) htt
  rw [map_mul, map_inv, htte, mul_inv_rev, inv_inv]

theorem map_mem_autMoved {s t : MulAut E} (hst : s * t = t * s) {x : E} (hx : x ∈ autMoved E t) :
    s x ∈ autMoved E t := by
  obtain ⟨e, rfl⟩ := (C.mem_autMoved_iff).1 hx
  have h1 : s (t e) = t (s e) := by simpa using congrArg (fun m : MulAut E => m e) hst
  rw [map_mul, map_inv, h1]
  exact C.mem_autMoved_self (s e)

theorem eq_bot_or_eq_of_le {t : MulAut E} (ht : Nat.card (autMoved E t) = p) {H : Subgroup E}
    (hH : H ≤ autMoved E t) : H = ⊥ ∨ H = autMoved E t := by
  have : Fact (Nat.card (autMoved E t)).Prime := ⟨by rw [ht]; exact C.prime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (H.subgroupOf (autMoved E t)) with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have : (⟨x, hH hx⟩ : autMoved E t) ∈ H.subgroupOf (autMoved E t) := hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hH fun y hy => ?_
    have : (⟨y, hy⟩ : autMoved E t) ∈ H.subgroupOf (autMoved E t) := by rw [h]; trivial
    exact this

theorem eq_one_of_sq_eq_one {κ : E} (h : κ * κ = 1) : κ = 1 := by
  have h1 : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h2 : orderOf κ ∣ p := orderOf_dvd_of_pow_eq_one (C.pow κ)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two C.prime).2 (Ne.symm C.odd)
  have h3 : orderOf κ ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem eq_of_moved_eq {s t : MulAut E} (hss : s * s = 1) (htt : t * t = 1) (hst : s * t = t * s)
    (hM : autMoved E s = autMoved E t) : s = t := by
  have hss' : ∀ e : E, s (s e) = e := fun e => by simpa using congrArg (fun m : MulAut E => m e) hss
  have htt' : ∀ e : E, t (t e) = e := fun e => by simpa using congrArg (fun m : MulAut E => m e) htt
  have hst' : ∀ e : E, s (t e) = t (s e) := fun e => by
    simpa using congrArg (fun m : MulAut E => m e) hst
  have key : ∀ e : E, s (t e) = e := by
    intro e
    have hνt : t e * e⁻¹ ∈ autMoved E t := C.mem_autMoved_self e
    have hμs : s e * e⁻¹ ∈ autMoved E s := C.mem_autMoved_self e
    have hνs : t e * e⁻¹ ∈ autMoved E s := hM ▸ hνt
    have hμt : s e * e⁻¹ ∈ autMoved E t := hM ▸ hμs
    obtain ⟨κ, hκt, hκs, hw⟩ : ∃ κ : E, κ ∈ autMoved E t ∧ κ ∈ autMoved E s ∧ s (t e) = κ * e := by
      refine ⟨(t e * e⁻¹)⁻¹ * (s e * e⁻¹), mul_mem (inv_mem hνt) hμt, mul_mem (inv_mem hνs) hμs, ?_⟩
      have hs_ν : s (t e * e⁻¹) = (t e * e⁻¹)⁻¹ := C.inv_of_mem_autMoved hss hνs
      have h1 : t e = (t e * e⁻¹) * e := by group
      have h2 : s e = (s e * e⁻¹) * e := by group
      calc s (t e) = s ((t e * e⁻¹) * e) := by rw [← h1]
        _ = s (t e * e⁻¹) * s e := map_mul _ _ _
        _ = (t e * e⁻¹)⁻¹ * s e := by rw [hs_ν]
        _ = (t e * e⁻¹)⁻¹ * ((s e * e⁻¹) * e) := by rw [← h2]
        _ = ((t e * e⁻¹)⁻¹ * (s e * e⁻¹)) * e := (mul_assoc _ _ _).symm
    have htκ : t κ = κ⁻¹ := C.inv_of_mem_autMoved htt hκt
    have hsκ : s κ = κ⁻¹ := C.inv_of_mem_autMoved hss hκs
    have h2 : s (t (s (t e))) = e := by
      rw [hst' (s (t e)), hss' (t e), htt']
    rw [hw, map_mul, htκ, map_mul, map_inv, hsκ, inv_inv, hw] at h2
    have h3 : κ * κ = 1 := by
      have h4 : (κ * κ) * e = 1 * e := by rw [one_mul, mul_assoc]; exact h2
      exact (mul_left_inj e).1 h4
    rw [hw, C.eq_one_of_sq_eq_one h3, one_mul]
  refine MulEquiv.ext fun e => ?_
  calc s e = s (s (t e)) := by rw [key e]
    _ = t e := hss' (t e)

theorem moved_inf_moved_eq_bot [Finite G] {s t : MulAut E} (hss : s * s = 1) (htt : t * t = 1)
    (hst : s * t = t * s) (hs : Nat.card (autMoved E s) = p) (ht : Nat.card (autMoved E t) = p)
    (hne : s ≠ t) : autMoved E s ⊓ autMoved E t = ⊥ := by
  rcases C.eq_bot_or_eq_of_le ht (inf_le_right : autMoved E s ⊓ autMoved E t ≤ autMoved E t) with
    h | h
  · exact h
  · exfalso
    have hle : autMoved E t ≤ autMoved E s := h ▸ inf_le_left
    have heq : autMoved E t = autMoved E s :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hs, ht])
    exact hne (C.eq_of_moved_eq hss htt hst heq.symm)

theorem fixes_moved [Finite G] {s t : MulAut E} (hss : s * s = 1) (htt : t * t = 1)
    (hst : s * t = t * s) (hs : Nat.card (autMoved E s) = p) (ht : Nat.card (autMoved E t) = p)
    (hne : s ≠ t) {m : E} (hm : m ∈ autMoved E t) : s m = m := by
  have hsm : s m ∈ autMoved E t := C.map_mem_autMoved hst hm
  have hx : s m * m⁻¹ ∈ autMoved E s := C.mem_autMoved_self m
  have hx' : s m * m⁻¹ ∈ autMoved E t := mul_mem hsm (inv_mem hm)
  have hbot : s m * m⁻¹ ∈ autMoved E s ⊓ autMoved E t := ⟨hx, hx'⟩
  rw [C.moved_inf_moved_eq_bot hss htt hst hs ht hne, Subgroup.mem_bot, mul_inv_eq_one] at hbot
  exact hbot

theorem moved_le_moved_mul [Finite G] {s t : MulAut E} (hss : s * s = 1) (htt : t * t = 1)
    (hst : s * t = t * s) (hs : Nat.card (autMoved E s) = p) (ht : Nat.card (autMoved E t) = p)
    (hne : s ≠ t) : autMoved E t ≤ autMoved E (s * t) := by
  intro n hn
  obtain ⟨j, hj⟩ := C.prime.odd_of_ne_two C.odd
  set k : ℕ := (p - 1) / 2 with hk
  have hk2 : 2 * k + 1 = p := by omega
  set e : E := n ^ k with he
  have heM : e ∈ autMoved E t := pow_mem hn k
  have hte : t e = e⁻¹ := C.inv_of_mem_autMoved htt heM
  have hse : s (e⁻¹) = e⁻¹ := by
    rw [map_inv, C.fixes_moved hss htt hst hs ht hne heM]
  have h1 : (s * t) e * e⁻¹ = n := by
    show s (t e) * e⁻¹ = n
    rw [hte, hse]
    have hnp : n ^ (2 * k + 1) = 1 := by rw [hk2]; exact C.pow n
    have h2 : n ^ (2 * k) = n⁻¹ := by
      rw [pow_succ] at hnp
      exact eq_inv_of_mul_eq_one_left hnp
    calc e⁻¹ * e⁻¹ = (e * e)⁻¹ := (mul_inv_rev e e).symm
      _ = (n ^ (2 * k))⁻¹ := by rw [he, ← pow_add, two_mul]
      _ = n := by rw [h2, inv_inv]
  rw [← h1]
  exact C.mem_autMoved_self e

omit C in
theorem mul_self_eq_one_of {s : MulAut E} (h : IsAutReflection p E s) : s * s = 1 := by
  have := pow_orderOf_eq_one s
  rwa [h.1, pow_two] at this

theorem card_moved_sup [Finite G] {s t : MulAut E} (hss : s * s = 1) (htt : t * t = 1)
    (hst : s * t = t * s) (hs : Nat.card (autMoved E s) = p) (ht : Nat.card (autMoved E t) = p)
    (hne : s ≠ t) : Nat.card ↥(autMoved E s ⊔ autMoved E t) = p ^ 2 := by
  rw [Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => C.comm k l)
    (disjoint_iff.2 (C.moved_inf_moved_eq_bot hss htt hst hs ht hne)), hs, ht]
  ring

theorem not_isAutReflection_mul [Finite G] {s t : MulAut E} (hs : IsAutReflection p E s)
    (ht : IsAutReflection p E t) (hst : s * t = t * s) (hne : s ≠ t) :
    ¬ IsAutReflection p E (s * t) := by
  rintro ⟨-, hcard⟩
  have hss := mul_self_eq_one_of hs
  have htt := mul_self_eq_one_of ht
  have h1 : autMoved E t ≤ autMoved E (s * t) :=
    C.moved_le_moved_mul hss htt hst hs.2 ht.2 hne
  have h2 : autMoved E s ≤ autMoved E (s * t) := by
    rw [hst]
    exact C.moved_le_moved_mul htt hss hst.symm ht.2 hs.2 hne.symm
  have h3 := Subgroup.card_le_of_le (sup_le h2 h1)
  rw [C.card_moved_sup hss htt hst hs.2 ht.2 hne, hcard] at h3
  have hp := C.prime.two_le
  nlinarith

theorem fixed_mul_le [Finite G] {s t : MulAut E} (hs : IsAutReflection p E s)
    (ht : IsAutReflection p E t) (hst : s * t = t * s) (hne : s ≠ t) :
    autFixed E (s * t) ≤ autFixed E s ⊓ autFixed E t := by
  have hss := mul_self_eq_one_of hs
  have htt := mul_self_eq_one_of ht
  intro x hx
  have hx' : s (t x) = x := hx
  have hsup := Sec13Base.fixed_sup_moved C.comm t C.prime C.odd C.pow htt
  have hxmem : x ∈ autFixed E t ⊔ autMoved E t := by rw [hsup]; trivial
  obtain ⟨f, hf, m, hm, rfl⟩ :=
    Torsion37.exists_mul_of_mem_sup_of_commute (fun k _ l _ => C.comm k l) hxmem
  have htf : t f = f := hf
  have htm : t m = m⁻¹ := C.inv_of_mem_autMoved htt hm
  have hsm : s m = m := C.fixes_moved hss htt hst hs.2 ht.2 hne hm
  rw [map_mul, htf, htm, map_mul, map_inv, hsm] at hx'
  have hsf : s f = f * m * m := mul_inv_eq_iff_eq_mul.1 hx'
  have hmm : m * m = s f * f⁻¹ := by
    calc m * m = f⁻¹ * (f * m * m) := by group
      _ = f⁻¹ * s f := by rw [← hsf]
      _ = s f * f⁻¹ := C.comm _ _
  have hmM : m * m ∈ autMoved E s ⊓ autMoved E t :=
    ⟨hmm ▸ C.mem_autMoved_self f, mul_mem hm hm⟩
  rw [C.moved_inf_moved_eq_bot hss htt hst hs.2 ht.2 hne, Subgroup.mem_bot] at hmM
  have hm1 : m = 1 := C.eq_one_of_sq_eq_one hmM
  subst hm1
  rw [mul_one]
  refine ⟨?_, hf⟩
  show s f = f
  simpa using hsf

theorem eq_sup_of_three [Finite G] {t s₁ s₂ : MulAut E} (ht : IsAutReflection p E t)
    (h₁ : IsAutReflection p E s₁) (h₂ : IsAutReflection p E s₂) (hts₁ : t * s₁ = s₁ * t)
    (hts₂ : t * s₂ = s₂ * t) (hs₁s₂ : s₁ * s₂ = s₂ * s₁) (hne₁ : t ≠ s₁) (hne₂ : t ≠ s₂)
    (hne₁₂ : s₁ ≠ s₂) (hE3 : Nat.card E = p ^ 3) :
    autMoved E t ⊔ (autMoved E s₁ ⊔ autMoved E s₂) = ⊤ := by
  have htt := mul_self_eq_one_of ht
  have hss₁ := mul_self_eq_one_of h₁
  have hss₂ := mul_self_eq_one_of h₂
  have hN : Nat.card ↥(autMoved E s₁ ⊔ autMoved E s₂) = p ^ 2 :=
    C.card_moved_sup hss₁ hss₂ hs₁s₂ h₁.2 h₂.2 hne₁₂
  have hdisj : Disjoint (autMoved E t) (autMoved E s₁ ⊔ autMoved E s₂) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxt, hxN⟩
    obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ :=
      Torsion37.exists_mul_of_mem_sup_of_commute (fun k _ l _ => C.comm k l) hxN
    have e₁ : t n₁ = n₁ := C.fixes_moved htt hss₁ hts₁ ht.2 h₁.2 hne₁ hn₁
    have e₂ : t n₂ = n₂ := C.fixes_moved htt hss₂ hts₂ ht.2 h₂.2 hne₂ hn₂
    have hinv := C.inv_of_mem_autMoved htt hxt
    rw [map_mul, e₁, e₂] at hinv
    have h3 : (n₁ * n₂) * (n₁ * n₂) = 1 :=
      (congrArg (fun y => (n₁ * n₂) * y) hinv).trans (mul_inv_cancel _)
    exact Subgroup.mem_bot.2 (C.eq_one_of_sq_eq_one h3)
  rw [← Subgroup.card_eq_iff_eq_top, Torsion37.card_sup_of_commute_disjoint
    (fun k _ l _ => C.comm k l) hdisj, ht.2, hN, hE3]
  ring

theorem exists_frame_element [Finite G] {t s t' s' : MulAut E} (ht : IsAutReflection p E t)
    (hs : IsAutReflection p E s) (ht' : IsAutReflection p E t') (hs' : IsAutReflection p E s')
    (hts : t * s = s * t) (hne : t ≠ s) (ht's' : t' * s' = s' * t') (hne' : t' ≠ s')
    (hconj : (t' * s') * t * (t' * s')⁻¹ = s) (hE3 : Nat.card E = p ^ 3) {a : E}
    (ha : a ∈ autMoved E t) (ha1 : a ≠ 1) :
    ∃ d : E, d ≠ 1 ∧ (∃ b ∈ autMoved E s, d = a * b) ∧ d ∈ autFixed E t' ∧ d ∈ autFixed E s' ∧
      Subgroup.zpowers d ⊔ (autMoved E t' ⊔ autMoved E s') = ⊤ := by
  have htt := mul_self_eq_one_of ht
  have hss := mul_self_eq_one_of hs
  have htt' := mul_self_eq_one_of ht'
  have hss' := mul_self_eq_one_of hs'
  obtain ⟨u, hu⟩ : ∃ u : MulAut E, u = t' * s' := ⟨_, rfl⟩
  rw [← hu] at hconj
  have huu : u * u = 1 := by
    calc u * u = t' * (s' * t') * s' := by rw [hu]; group
      _ = t' * (t' * s') * s' := by rw [ht's']
      _ = (t' * t') * (s' * s') := by group
      _ = 1 := by rw [htt', hss', one_mul]
  have huu' : ∀ e : E, u (u e) = e := fun e => by simpa using congrArg (fun m : MulAut E => m e) huu
  have hMs : autMoved E s = (autMoved E t).map u.toMonoidHom := by
    rw [← hconj]
    exact Equivariance.autMoved_conj u t
  have hub : u a ∈ autMoved E s := hMs ▸ Subgroup.mem_map_of_mem _ ha
  have hbot := C.moved_inf_moved_eq_bot hss htt hts.symm hs.2 ht.2 hne.symm
  have hd1 : a * u a ≠ 1 := by
    intro h
    have h1 : u a = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : u a ∈ autMoved E s ⊓ autMoved E t :=
      Subgroup.mem_inf.2 ⟨hub, by rw [h1]; exact inv_mem ha⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact ha1 (u.injective (by rw [h2, map_one]))
  have hdfix : a * u a ∈ autFixed E u := by
    show u (a * u a) = a * u a
    rw [map_mul, huu', C.comm]
  have hdboth : a * u a ∈ autFixed E t' ⊓ autFixed E s' :=
    C.fixed_mul_le ht' hs' ht's' hne' (by rw [← hu]; exact hdfix)
  obtain ⟨hdt, hds⟩ := Subgroup.mem_inf.1 hdboth
  refine ⟨a * u a, hd1, ⟨u a, hub, rfl⟩, hdt, hds, ?_⟩
  have hN : Nat.card ↥(autMoved E t' ⊔ autMoved E s') = p ^ 2 :=
    C.card_moved_sup htt' hss' ht's' ht'.2 hs'.2 hne'
  have hdisj : Disjoint (Subgroup.zpowers (a * u a)) (autMoved E t' ⊔ autMoved E s') := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxd, hxN⟩
    have hxt : t' x = x := by
      have : Subgroup.zpowers (a * u a) ≤ autFixed E t' := Subgroup.zpowers_le.2 hdt
      exact this hxd
    have hxs : s' x = x := by
      have : Subgroup.zpowers (a * u a) ≤ autFixed E s' := Subgroup.zpowers_le.2 hds
      exact this hxd
    obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ :=
      Torsion37.exists_mul_of_mem_sup_of_commute (fun k _ l _ => C.comm k l) hxN
    have e₁ : t' n₁ = n₁⁻¹ := C.inv_of_mem_autMoved htt' hn₁
    have e₂ : t' n₂ = n₂ := C.fixes_moved htt' hss' ht's' ht'.2 hs'.2 hne' hn₂
    have f₁ : s' n₁ = n₁ := C.fixes_moved hss' htt' ht's'.symm hs'.2 ht'.2 hne'.symm hn₁
    have f₂ : s' n₂ = n₂⁻¹ := C.inv_of_mem_autMoved hss' hn₂
    rw [map_mul, e₁, e₂] at hxt
    rw [map_mul, f₁, f₂] at hxs
    have g₁ : n₁ * n₁ = 1 := by
      have : n₁⁻¹ * n₂ = n₁ * n₂ := hxt
      have h2 : n₁⁻¹ = n₁ := mul_right_cancel this
      calc n₁ * n₁ = n₁ * n₁⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    have g₂ : n₂ * n₂ = 1 := by
      have : n₁ * n₂⁻¹ = n₁ * n₂ := hxs
      have h2 : n₂⁻¹ = n₂ := mul_left_cancel this
      calc n₂ * n₂ = n₂ * n₂⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    rw [Subgroup.mem_bot, C.eq_one_of_sq_eq_one g₁, C.eq_one_of_sq_eq_one g₂, one_mul]
  have : Fact p.Prime := ⟨C.prime⟩
  have hdord : orderOf (a * u a) = p := orderOf_eq_prime (C.pow _) hd1
  rw [← Subgroup.card_eq_iff_eq_top, Torsion37.card_sup_of_commute_disjoint
    (fun k _ l _ => C.comm k l) hdisj, Nat.card_zpowers, hdord, hN, hE3]
  ring

theorem fixed_inf_fixed_ne_bot [Finite G] {s t : MulAut E} (hs : IsAutReflection p E s)
    (ht : IsAutReflection p E t) (hE3 : Nat.card E = p ^ 3) :
    autFixed E s ⊓ autFixed E t ≠ ⊥ := by
  intro hbot
  have hFs : Nat.card (autFixed E s) = p ^ 2 := by
    have h := Sec13Base.card_eq_mul C.comm s
    rw [hE3, hs.2] at h
    have hp : 0 < p := C.prime.pos
    have : p ^ 2 * p = Nat.card (autFixed E s) * p := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hp this).symm
  have hFt : Nat.card (autFixed E t) = p ^ 2 := by
    have h := Sec13Base.card_eq_mul C.comm t
    rw [hE3, ht.2] at h
    have hp : 0 < p := C.prime.pos
    have : p ^ 2 * p = Nat.card (autFixed E t) * p := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hp this).symm
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (autFixed E s) (autFixed E t)
    (fun x _ y _ => C.comm x y)).1
  rw [hbot, Subgroup.card_bot, hFs, hFt] at h1
  have h2 : Nat.card ↥(autFixed E s ⊔ autFixed E t) ≤ Nat.card E := Subgroup.card_le_card_group _
  rw [hE3] at h2
  have hp := C.prime.two_le
  have h3 : p ^ 4 ≤ p ^ 3 := by nlinarith [h1, h2]
  have h4 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right C.prime.one_lt (by norm_num)
  omega

omit C in
theorem fixed_eq_bot_or_top_of_inv {x : MulAut E} (hirr : torusIrreducible E)
    (hinv : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * x * (conjAut E w hw)⁻¹ = x) :
    autFixed E x = ⊥ ∨ autFixed E x = ⊤ := by
  have hB : autFixedInG E x ≤ E := Subgroup.map_subtype_le _
  have hinvB : torusInvariant E ⊤ (autFixedInG E x) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hcomm : conjAut E w hwN * x = x * conjAut E w hwN := by
      have := hinv w hwN
      exact mul_inv_eq_iff_eq_mul.1 this
    have hfix : x (conjAut E w hwN b') = conjAut E w hwN b' := by
      have h1 : (x * conjAut E w hwN) b' = (conjAut E w hwN * x) b' := by rw [hcomm]
      have h2 : x b' = b' := hb'
      calc x (conjAut E w hwN b') = (x * conjAut E w hwN) b' := rfl
        _ = (conjAut E w hwN * x) b' := h1
        _ = conjAut E w hwN (x b') := rfl
        _ = conjAut E w hwN b' := by rw [h2]
    refine Subgroup.mem_map.2 ⟨conjAut E w hwN b', hfix, ?_⟩
    exact (Equivariance.coe_conjAut hwN b').symm ▸ rfl
  rcases hirr _ hB hinvB with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 h
  · right
    have h' : (autFixed E x).map E.subtype = (⊤ : Subgroup E).map E.subtype := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact h
    exact Subgroup.map_injective E.subtype_injective h'

end ReflCtx

end CFSG.RankThree.PartOne.S15K
