module

public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.S153D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_sq_mem {x : G} (hx : Odd (orderOf x)) {L : Subgroup G}
    (h : x ^ 2 ∈ Subgroup.normalizer (L : Set G)) : x ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    have : 2 * (k + 1) = orderOf x + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact Subgroup.pow_mem _ h _

theorem mem_conjSubgroupsBy_self {I L : Subgroup G} : L ∈ conjSubgroupsBy I L :=
  ⟨1, I.one_mem, by ext x; simp⟩

theorem map_conj_mem_conjSubgroupsBy {I L K : Subgroup G} {x : G} (hx : x ∈ I)
    (hK : K ∈ conjSubgroupsBy I L) : K.map (MulAut.conj x).toMonoidHom ∈ conjSubgroupsBy I L := by
  obtain ⟨t, ht, rfl⟩ := hK
  refine ⟨x * t, I.mul_mem hx ht, ?_⟩
  ext y
  simp [mul_assoc]

theorem eq_of_mem_pair {α : Type*} {a b p q r : α} (hab : a ≠ b) (hp : p = a ∨ p = b)
    (hq : q = a ∨ q = b) (hr : r = a ∨ r = b) (hpq : p ≠ q) (hqr : q ≠ r) : p = r := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
    simp_all

theorem le_normalizer_of_oTwoUpper_eq {I X L : Subgroup G} (hLI : L ≤ I) (hXI : X ≤ I)
    (hX : oTwoUpper X = X)
    (hL : (L.subgroupOf I).Normal ∨ Set.ncard (conjSubgroupsBy I L) = 2) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  rcases hL with hn | h2
  · exact hXI.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mp hn)
  · rw [← hX, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxX, hxodd⟩
    have hxI : x ∈ I := hXI hxX
    by_contra hxn
    have hne : L.map (MulAut.conj x).toMonoidHom ≠ L := fun h => hxn (A38.map_conj_eq_iff.mp h)
    obtain ⟨a, b, hab, hs⟩ := Set.ncard_eq_two.mp h2
    have hLs : L ∈ conjSubgroupsBy I L := mem_conjSubgroupsBy_self
    have h1s := map_conj_mem_conjSubgroupsBy hxI hLs
    have h2s := map_conj_mem_conjSubgroupsBy hxI h1s
    have hinj : ∀ K K' : Subgroup G, K.map (MulAut.conj x).toMonoidHom =
        K'.map (MulAut.conj x).toMonoidHom → K = K' := fun K K' h =>
      Subgroup.map_injective (MulAut.conj x).injective h
    have hne2 : (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom ≠
        L.map (MulAut.conj x).toMonoidHom := fun h => hne (hinj _ _ h)
    rw [hs] at hLs h1s h2s
    have hσσ : (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = L :=
      eq_of_mem_pair hab h2s h1s hLs hne2 hne
    have hsq : x ^ 2 ∈ Subgroup.normalizer (L : Set G) := by
      have e : L.map (MulAut.conj (x ^ 2)).toMonoidHom =
          (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext y
        simp [pow_two, MulAut.conj_apply, mul_assoc]
      exact A38.map_conj_eq_iff.mp (e.trans hσσ)
    exact hxn (mem_normalizer_of_sq_mem hxodd hsq)


theorem isElemAbelian_sup_zpowers {p : ℕ} {E : Subgroup G} {z : G} (hE : IsElemAbelian p E)
    (hz : z ^ p = 1) (hc : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) := by
  have := hE.1
  have hcz : ∀ e ∈ E, ∀ k : ℤ, e * z ^ k = z ^ k * e := fun e he k =>
    ((Commute.zpow_left (show Commute z e from (hc e he).symm) k)).symm.eq
  have hconj : ∀ e ∈ E, z * e * z⁻¹ = e := fun e he => by
    rw [← hc e he]; group
  have hconj' : ∀ e ∈ E, z⁻¹ * e * z = e := fun e he => by
    rw [mul_assoc, hc e he, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzn : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rw [hconj e he]; exact he
    · have h1 := hconj' _ he
      have h2 : z⁻¹ * (z * e * z⁻¹) * z = e := by group
      rw [h2] at h1
      exact h1.symm ▸ he
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left E (Subgroup.zpowers z) hzn
  have hmem : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ e ∈ E, ∃ k : ℤ, x = e * z ^ k := by
    intro x hx
    have hx' : x ∈ (↑(E ⊔ Subgroup.zpowers z) : Set G) := hx
    rw [hmul] at hx'
    obtain ⟨e, he, w, hw, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨e, he, k, rfl⟩
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, k, hk⟩ := hmem a a.2
    obtain ⟨e', he', l, hl⟩ := hmem b b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [hk, hl]
    have h1 : e * z ^ k * (e' * z ^ l) = e * e' * (z ^ k * z ^ l) := by
      calc e * z ^ k * (e' * z ^ l) = e * (z ^ k * e') * z ^ l := by group
        _ = e * (e' * z ^ k) * z ^ l := by rw [← hcz e' he' k]
        _ = e * e' * (z ^ k * z ^ l) := by group
    have h2 : e' * z ^ l * (e * z ^ k) = e' * e * (z ^ l * z ^ k) := by
      calc e' * z ^ l * (e * z ^ k) = e' * (z ^ l * e) * z ^ k := by group
        _ = e' * (e * z ^ l) * z ^ k := by rw [← hcz e he l]
        _ = e' * e * (z ^ l * z ^ k) := by group
    rw [h1, h2, hEcomm e he e' he', ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨e, he, k, rfl⟩ := hmem x hx
    have hcomm : Commute e (z ^ k) := hcz e he k
    rw [hcomm.mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hz, one_zpow]

theorem three_le_pRank_of_acts [Finite G] {X L E : Subgroup G} (hLX : L ≤ X)
    (hn : (L.subgroupOf X).Normal) (hEX : E ≤ X) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEL : E ⊓ L = ⊥) (h3 : 3 ∣ Nat.card L) :
    3 ≤ CFSG.Open.pRank 3 X := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L' : Subgroup ↥X := L.subgroupOf X with hL'
  set E' : Subgroup ↥X := E.subgroupOf X with hE'
  have hE'p : IsPGroup 3 ↥E' := fun g => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have := hE.2 (g : G) (Subgroup.mem_subgroupOf.mp g.2)
    simpa using this⟩
  obtain ⟨P, hP⟩ := hE'p.exists_le_sylow
  have hL'3 : 3 ∣ Nat.card ↥L' := by
    have : Nat.card ↥L' = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
    rwa [this]
  have hPL : (P : Subgroup ↥X) ⊓ L' ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective ((QuotientGroup.mk' L').comp (P : Subgroup ↥X).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
      have hgL : (g : ↥X) ∈ L' := (QuotientGroup.eq_one_iff _).mp hg
      have : (g : ↥X) ∈ (P : Subgroup ↥X) ⊓ L' := ⟨g.2, hgL⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    have hindex : Nat.card (↥X ⧸ L') = L'.index := rfl
    have hcardX : Nat.card ↥L' * L'.index = Nat.card ↥X := Subgroup.card_mul_index L'
    have hX0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
    set a := (Nat.card ↥X).factorization 3 with ha
    have hPcard : Nat.card (P : Subgroup ↥X) = 3 ^ a := P.card_eq_multiplicity
    rw [hPcard, hindex] at hdvd
    have h1 : 3 ^ a * 3 ∣ Nat.card ↥X := by
      rw [← hcardX, mul_comm (3 ^ a)]
      exact Nat.mul_dvd_mul hL'3 hdvd
    have h2 : a + 1 ≤ a := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hX0, pow_succ]
      exact h1
    omega
  have hPp : IsPGroup 3 ↥(P : Subgroup ↥X) := P.isPGroup'
  have hPnil : Group.IsNilpotent ↥(P : Subgroup ↥X) := hPp.isNilpotent
  have hL'n : L'.Normal := hn
  set N : Subgroup ↥(P : Subgroup ↥X) := L'.subgroupOf (P : Subgroup ↥X) with hN
  have hNn : N.Normal := hL'n.subgroupOf _
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPL
  have hN1 : N ≠ ⊥ := by
    intro hb
    have hmem : (⟨x₀, hx₀.1⟩ : ↥(P : Subgroup ↥X)) ∈ N := Subgroup.mem_subgroupOf.mpr hx₀.2
    rw [hb, Subgroup.mem_bot] at hmem
    apply hx₀1
    have h1 : x₀ = 1 := congrArg Subtype.val hmem
    exact Subtype.ext h1
  obtain ⟨⟨⟨z, hzP⟩, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  have hzL' : z ∈ L' := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).1
  have hzcen : ∀ g ∈ (P : Subgroup ↥X), g * z = z * g := fun g hg => by
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hz).2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hord : ∃ m : ℕ, orderOf z = 3 ^ m := by
    have hd : orderOf z ∣ Nat.card (P : Subgroup ↥X) := by
      have := Subgroup.orderOf_dvd_natCard (P : Subgroup ↥X) hzP
      simpa using this
    rw [P.card_eq_multiplicity] at hd
    exact (Nat.dvd_prime_pow Nat.prime_three).mp hd |>.imp fun m hm => hm.2
  obtain ⟨m, hm⟩ := hord
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hz1'
    · exact h0
  set z' : ↥X := z ^ (3 ^ (m - 1)) with hz'
  have hz'ord : orderOf z' = 3 := by
    rw [hz', orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by
      rw [hm]; exact pow_dvd_pow 3 (Nat.sub_le m 1)), hm]
    have : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hz'3 : z' ^ 3 = 1 := by rw [← hz'ord]; exact pow_orderOf_eq_one z'
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'ord
    omega
  have hz'L' : z' ∈ L' := L'.pow_mem hzL' _
  have hz'P : z' ∈ (P : Subgroup ↥X) := (P : Subgroup ↥X).pow_mem hzP _
  have hz'cen : ∀ g ∈ (P : Subgroup ↥X), g * z' = z' * g := fun g hg =>
    ((Commute.pow_right (show Commute g z from hzcen g hg) _)).eq
  have hE'L : E' ⊓ L' = ⊥ := by
    have : E' ⊓ L' = (E ⊓ L).subgroupOf X := by
      ext x
      simp [hE', hL', Subgroup.mem_subgroupOf]
    rw [this, hEL, Subgroup.bot_subgroupOf]
  have hz'E : z' ∉ E' := fun h => hz'1 (by
    have : z' ∈ E' ⊓ L' := ⟨h, hz'L'⟩
    rw [hE'L, Subgroup.mem_bot] at this
    exact this)
  have hE'ea : IsElemAbelian 3 E' := by
    have := hE.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have hma := Subgroup.mem_subgroupOf.mp a.2
      have hmb := Subgroup.mem_subgroupOf.mp b.2
      have := congrArg Subtype.val (mul_comm' (⟨(a : ↥X), hma⟩ : ↥E) ⟨(b : ↥X), hmb⟩)
      simpa using this
    · apply Subtype.ext
      have := hE.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  have hSea : IsElemAbelian 3 (E' ⊔ Subgroup.zpowers z') :=
    isElemAbelian_sup_zpowers hE'ea hz'3 (fun e he => hz'cen e (hP he))
  have hS_le : E' ⊔ Subgroup.zpowers z' ≤ (P : Subgroup ↥X) :=
    sup_le hP ((Subgroup.zpowers_le).mpr hz'P)
  have hS3 : IsPGroup 3 ↥(E' ⊔ Subgroup.zpowers z') := P.isPGroup'.to_le hS_le
  obtain ⟨m', hm'⟩ := IsPGroup.iff_card.mp hS3
  have hE'9 : Nat.card ↥E' = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hlt : 9 < Nat.card ↥(E' ⊔ Subgroup.zpowers z') := by
    by_contra hcon
    have hle : Nat.card ↥(E' ⊔ Subgroup.zpowers z') ≤ Nat.card ↥E' := by omega
    have heq : E' = E' ⊔ Subgroup.zpowers z' := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    exact hz'E (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z'))
  have hm'3 : 3 ≤ m' := by
    rw [hm'] at hlt
    by_contra hcon
    have : m' ≤ 2 := by omega
    have : 3 ^ m' ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hmapea := CFSG.SectionRank.isElemAbelian_map hSea X.subtype
  have hmapcard : Nat.card ↥((E' ⊔ Subgroup.zpowers z').map X.subtype) = 3 ^ m' := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hm']
  exact hm'3.trans (CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_subtype_le _) hmapea
    hmapcard)

end CFSG.Quasithin.S153D
