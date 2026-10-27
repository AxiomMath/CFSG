module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.PCore.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup

variable {E : Type*} [Group E]

theorem relIndex_dvd_index_of_normal_left [Finite E] (N L : Subgroup E) [N.Normal] :
    L.relIndex N ∣ L.index := by
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_normal N L
  have h1 := Subgroup.index_inf (H := L) (K := N)
  have h2 := Subgroup.index_inf (H := N) (K := L)
  rw [inf_comm N L, h1, hm] at h2
  have hne : N.relIndex L ≠ 0 := (N.subgroupOf L).index_ne_zero_of_finite
  refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_⟩
  rw [← h2]
  ring

theorem mem_or_mem_mul_of_mem_sup_zpowers {W : Subgroup E} {u : E} (hu : u * u = 1)
    (hinv : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹) {x : E} (hx : x ∈ W ⊔ Subgroup.zpowers u) :
    x ∈ W ∨ ∃ w ∈ W, x = w * u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hconj : ∀ h ∈ W, u * h * u⁻¹ = h⁻¹ := fun h hh => by
    have h1 := hinv h hh
    rw [huinv] at h1 ⊢
    exact h1
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (W : Set E) := by
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hconj h hh]; exact W.inv_mem hh, fun hh => ?_⟩
    have h1 := hconj _ hh
    rw [show u * (u * h * u⁻¹) * u⁻¹ = (u * u) * h * (u * u)⁻¹ by group, hu, inv_one,
      one_mul, mul_one] at h1
    rw [h1]
    exact W.inv_mem hh
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W _ hnorm,
    Set.mem_mul] at hx
  obtain ⟨w, hw, v, hv, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hu, one_zpow, mul_one]
    exact hw
  · right
    refine ⟨w, hw, ?_⟩
    rw [zpow_add, zpow_one, zpow_mul, zpow_two, hu, one_zpow, one_mul]

theorem mem_normal_of_involution_conjugacy [Finite E] {J : Subgroup E} {a : ℕ}
    (hJ : J.index = 2 ^ a) (h2 : CFSG.pCore 2 E = ⊥) {u : E}
    (hconj : ∀ v ∈ J, orderOf v = 2 → ∃ g ∈ J, g * u * g⁻¹ = v)
    (hodd : ∀ M : Subgroup E, M ≤ J → (∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      Odd (Nat.card M) → M = ⊥)
    (N : Subgroup E) [hNn : N.Normal] (hN : N ≠ ⊥) : u ∈ N := by
  by_contra huN
  have hModd : Odd (Nat.card (N ⊓ J : Subgroup E)) := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    rw [← Subgroup.orderOf_coe] at hv
    obtain ⟨g, -, hg⟩ := hconj v v.2.2 hv
    apply huN
    have h := hNn.conj_mem (v : E) v.2.1 g⁻¹
    rwa [← hg, inv_inv, show g⁻¹ * (g * u * g⁻¹) * g = u by group] at h
  have hM : N ⊓ J = ⊥ := hodd _ inf_le_right (fun g hg m hm =>
    ⟨hNn.conj_mem m hm.1 g, J.mul_mem (J.mul_mem hg hm.2) (J.inv_mem hg)⟩) hModd
  have hcard : Nat.card N ∣ 2 ^ a := by
    have h1 := Subgroup.relIndex_mul_card J N
    rw [inf_comm, hM, Subgroup.card_bot, mul_one] at h1
    rw [← h1, ← hJ]
    exact relIndex_dvd_index_of_normal_left N J
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard
  have hle : N ≤ CFSG.pCore 2 E := le_sSup ⟨hNn, IsPGroup.of_card hi⟩
  rw [h2, le_bot_iff] at hle
  exact hN hle

theorem mem_normal_of_odd_hall_torus [Finite E] {W : Subgroup E} {a : ℕ}
    (hW : W.index = 2 ^ a) (h2 : CFSG.pCore 2 E = ⊥) (hodd : CFSG.oddCore E = ⊥)
    (hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hWodd : Odd (Nat.card W)) {u : E}
    (hu : u * u = 1) (hinv : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnorm : ∀ P : Subgroup E, P ≤ W → P ≠ ⊥ →
      Subgroup.normalizer (P : Set E) ≤ W ⊔ Subgroup.zpowers u)
    (N : Subgroup E) [N.Normal] (hN : N ≠ ⊥) : u ∈ N := by
  have hWu : ∀ w ∈ W, ∃ b ∈ W, b * u * b⁻¹ = w * u := by
    intro w hw
    have hwn : w ^ Nat.card W = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨w, hw⟩ : W)))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
    set b := w ^ ((Nat.card W + 1) / 2)
    have hbW : b ∈ W := W.pow_mem hw _
    have hbb : b * b = w := by
      rw [← pow_add, ← two_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp hWodd.add_one),
        pow_succ, hwn, one_mul]
    have hub : u * b⁻¹ = b * u := by
      rw [← hinv b hbW]
      group
    refine ⟨b, hbW, ?_⟩
    rw [mul_assoc, hub, ← mul_assoc, hbb]
  suffices h : ∀ n : ℕ, ∀ N : Subgroup E, N.Normal → N ≠ ⊥ → Nat.card N = n → u ∈ N from
    h _ N inferInstance hN rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hNn hN hNcard
  by_contra huN
  have hnot2 : ¬ IsPGroup 2 N := fun h2N => by
    have hle : N ≤ CFSG.pCore 2 E := le_sSup ⟨hNn, h2N⟩
    rw [h2, le_bot_iff] at hle
    exact hN hle
  obtain ⟨p, hp, hpN, hp2⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card N ∧ p ≠ 2 := by
    by_contra hcon
    push Not at hcon
    exact hnot2 (IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => hcon d hd hdvd))
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hidx : W.relIndex N ∣ 2 ^ a := hW ▸ relIndex_dvd_index_of_normal_left N W
  have hpidx : ¬ p ∣ W.relIndex N := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (h.trans hidx)))
  have hpY : p ∣ Nat.card (W ⊓ N : Subgroup E) := by
    have h : p ∣ W.relIndex N * Nat.card (W ⊓ N : Subgroup E) := by
      rw [Subgroup.relIndex_mul_card W N]
      exact hpN
    exact ((Nat.Prime.dvd_mul hp).mp h).resolve_left hpidx
  let S : Sylow p (W ⊓ N : Subgroup E) := default
  let P : Subgroup E := (S : Subgroup (W ⊓ N : Subgroup E)).map (W ⊓ N : Subgroup E).subtype
  have hPY : P ≤ W ⊓ N := Subgroup.map_subtype_le _
  have hPW : P ≤ W := hPY.trans inf_le_left
  have hPN : P ≤ N := hPY.trans inf_le_right
  have hPne : P ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).not.mpr
      (S.ne_bot_of_dvd_card hpY)
  have hPsub : P.subgroupOf (W ⊓ N) = S :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hPidx : ¬ p ∣ (P.subgroupOf N).index := by
    change ¬ p ∣ P.relIndex N
    rw [← Subgroup.relIndex_mul_relIndex P (W ⊓ N) N hPY inf_le_right,
      Subgroup.inf_relIndex_right]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · rw [Subgroup.relIndex, hPsub] at h
      exact S.not_dvd_index h
    · exact hpidx h
  have hPp : IsPGroup p (P.subgroupOf N) :=
    (S.isPGroup'.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  let PN : Sylow p N := hPp.toSylow hPidx
  have hPNcoe : (PN : Subgroup N) = P.subgroupOf N := IsPGroup.toSylow_coe hPp hPidx
  have hNC : Subgroup.normalizer ((PN : Subgroup N) : Set N) ≤
      Subgroup.centralizer ((PN : Subgroup N) : Set N) := by
    rw [hPNcoe]
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hPN] at hx
    have hx' : (x : E) ∈ Subgroup.normalizer (P : Set E) := Subgroup.mem_subgroupOf.mp hx
    rcases mem_or_mem_mul_of_mem_sup_zpowers hu hinv (hnorm P hPW hPne hx') with
      hxW | ⟨w, hw, hxw⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subtype.ext (hWcomm _ (hPW (Subgroup.mem_subgroupOf.mp hh)) _ hxW)
    · exfalso
      obtain ⟨b, -, hb⟩ := hWu w hw
      apply huN
      have h1 := hNn.conj_mem (x : E) x.2 b⁻¹
      rwa [hxw, ← hb, inv_inv, show b⁻¹ * (b * u * b⁻¹) * b = u by group] at h1
  obtain ⟨K, -, -, hKindex, -, hKchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement PN hNC
  have hN'n : (K.map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (hH := hNn) (h := hKchar)
  have hcardPN : Nat.card PN = Nat.card P := by
    rw [hPNcoe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have hP1 : 1 < Nat.card P := P.one_lt_card_iff_ne_bot.mpr hPne
  have hKN : Nat.card K * Nat.card P = Nat.card N := by
    rw [← hcardPN, ← hKindex, Subgroup.card_mul_index]
  have hcardN' : Nat.card (K.map N.subtype) = Nat.card K :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hN'ne : K.map N.subtype ≠ ⊥ := by
    intro hbot
    have hK : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hbot
    rw [hK, Subgroup.card_bot, one_mul, ← hcardPN] at hKN
    obtain ⟨m, hm⟩ := PN.isPGroup'.exists_card_eq
    have hNodd : Odd (Nat.card N) := by
      rw [← hKN, hm]
      exact hpodd.pow
    have hle : N ≤ CFSG.oddCore E := le_sSup ⟨hNn, hNodd⟩
    rw [hodd, le_bot_iff] at hle
    exact hN hle
  have hlt : Nat.card (K.map N.subtype) < n := by
    rw [hcardN', ← hNcard, ← hKN]
    exact lt_mul_of_one_lt_right Nat.card_pos hP1
  exact huN (Subgroup.map_subtype_le K (ih _ hlt _ hN'n hN'ne rfl))

end CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup
