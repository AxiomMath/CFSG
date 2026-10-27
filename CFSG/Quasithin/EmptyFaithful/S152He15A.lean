module

public import CFSG.Quasithin.EmptyFaithful.S153DGen
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace He15

variable {G : Type} [Group G]

theorem exists_central_order_three [Finite G] {X L E : Subgroup G} (hLX : L ≤ X)
    (hn : (L.subgroupOf X).Normal) (hEX : E ≤ X) (hE : IsPGroup 3 ↥E) (h3 : 3 ∣ Nat.card L) :
    ∃ z ∈ L, orderOf z = 3 ∧ ∀ e ∈ E, e * z = z * e := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L' : Subgroup ↥X := L.subgroupOf X with hL'
  set E' : Subgroup ↥X := E.subgroupOf X with hE'
  have hE'p : IsPGroup 3 ↥E' := by
    intro g
    obtain ⟨k, hk⟩ := hE ⟨((g : ↥X) : G), Subgroup.mem_subgroupOf.mp g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
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
  have hz'L' : z' ∈ L' := L'.pow_mem hzL' _
  have hz'P : z' ∈ (P : Subgroup ↥X) := (P : Subgroup ↥X).pow_mem hzP _
  have hz'cen : ∀ g ∈ (P : Subgroup ↥X), g * z' = z' * g := fun g hg =>
    ((Commute.pow_right (show Commute g z from hzcen g hg) _)).eq
  refine ⟨(z' : G), Subgroup.mem_subgroupOf.mp hz'L', ?_, fun e he => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hz'ord
  · have h1 := hz'cen ⟨e, hEX he⟩ (hP (Subgroup.mem_subgroupOf.mpr he))
    exact congrArg Subtype.val h1

theorem oTwoUpper_zpowers_of_odd {x : G} (hx : Odd (orderOf x)) :
    oTwoUpper (Subgroup.zpowers x) = Subgroup.zpowers x := by
  refine le_antisymm (oTwoUpper_le _) ?_
  intro g hg
  exact mem_oTwoUpper_of_odd hg (Odd.of_dvd_nat hx (orderOf_dvd_of_mem_zpowers hg))

theorem mem_normalizer_of_odd {I L : Subgroup G} {x : G} (hLI : L ≤ I) (hxI : x ∈ I)
    (hxodd : Odd (orderOf x))
    (hL : (L.subgroupOf I).Normal ∨ Set.ncard (conjSubgroupsBy I L) = 2) :
    x ∈ Subgroup.normalizer (L : Set G) :=
  S153D.le_normalizer_of_oTwoUpper_eq hLI (Subgroup.zpowers_le.mpr hxI)
    (oTwoUpper_zpowers_of_odd hxodd) hL (Subgroup.mem_zpowers x)

theorem mem_pCore_iff {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

theorem isElemAbelian_zpowers {x : G} {p : ℕ} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem zpow_mem_eq_one {C : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxC : x ∉ C) {i : ℤ}
    (hi : x ^ i ∈ C) : x ^ i = 1 := by
  have h3 : x ^ i = x ^ (i % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod i 3, zpow_add, zpow_mul]
    have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [this, one_zpow, one_mul]
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · rw [h3, h, zpow_zero]
  · exfalso
    apply hxC
    rw [h3, h, zpow_one] at hi
    exact hi
  · exfalso
    apply hxC
    rw [h3, h] at hi
    have hi' : x ^ 2 ∈ C := by simpa using hi
    have e : x ^ 2 * x ^ 2 = x := by
      calc x ^ 2 * x ^ 2 = x ^ 3 * x := by group
        _ = x := by rw [hx3, one_mul]
    rw [← e]
    exact C.mul_mem hi' hi'

theorem exists_elemAbelian_nine [Finite G] {C L : Subgroup G} {x a : G} (hx3 : x ^ 3 = 1)
    (ha3 : a ^ 3 = 1) (hxC : x ∉ C) (haC : a ∈ C) (haL : a ∉ L) (hLC : L ≤ C)
    (hxa : x * a = a * x) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ x ∈ E ∧ a ∈ E ∧ E ⊓ L = ⊥ ∧
      ∀ H : Subgroup G, x ∈ H → a ∈ H → E ≤ H := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hxC (h ▸ C.one_mem)
  have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hcx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hca : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hoa]
  have hcomm : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers a, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow (show Commute x a from hxa) i j).eq
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hux, hua⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hux
    have huC : x ^ i ∈ C := (Subgroup.zpowers_le.mpr haC) hua
    rw [Subgroup.mem_bot]
    exact zpow_mem_eq_one hx3 hxC huC
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (Subgroup.zpowers a) hcomm
  rw [hdisj, Subgroup.card_bot, mul_one, hcx, hca] at hcard
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers a,
    S153D.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hx3) ha3 (fun e he =>
      hcomm e he a (Subgroup.mem_zpowers a)), by rw [hcard], Subgroup.mem_sup_left
      (Subgroup.mem_zpowers x), Subgroup.mem_sup_right (Subgroup.mem_zpowers a), ?_,
    fun H hxH haH => sup_le (Subgroup.zpowers_le.mpr hxH) (Subgroup.zpowers_le.mpr haH)⟩
  rw [eq_bot_iff]
  rintro e ⟨he, heL⟩
  have he' : e ∈ ((Subgroup.zpowers x : Set G) * (Subgroup.zpowers a : Set G)) := by
    rw [← hset]; exact he
  obtain ⟨u, hu, v, hv, rfl⟩ := he'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  dsimp only at he heL ⊢
  have hxi : x ^ i ∈ C := by
    have h1 : x ^ i * a ^ j * (a ^ j)⁻¹ ∈ C :=
      C.mul_mem (hLC heL) (C.inv_mem (C.zpow_mem haC j))
    simpa using h1
  have hxi1 := zpow_mem_eq_one hx3 hxC hxi
  rw [hxi1, one_mul] at heL ⊢
  rw [Subgroup.mem_bot]
  exact zpow_mem_eq_one ha3 haL heL

end He15

end CFSG.Quasithin
