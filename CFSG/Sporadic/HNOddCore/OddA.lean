module

public import CFSG.Sporadic.HNOddCore.FusC

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.ComponentClassification.SmallLocal Subgroup

theorem oddCore_characteristic' (G : Type*) [Group G] : (CFSG.oddCore G).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.2 fun φ => sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map _ φ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hN.2

theorem oddCore_normal_bot {G : Type*} [Group G] [Finite G] (hO : CFSG.oddCore G = ⊥)
    (K : Subgroup G) [K.Normal] : CFSG.oddCore K = ⊥ := by
  have := oddCore_characteristic' K
  have hN : ((CFSG.oddCore K).map K.subtype).Normal := inferInstance
  have hodd : Odd (Nat.card ((CFSG.oddCore K).map K.subtype)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact odd_card_oddCore
  have hle := le_oddCore_of_normal_odd hN hodd
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle
  exact hle

theorem mem_of_odd_of_sq_mem {C : Type*} [Group C] [Finite C] {K : Subgroup C}
    (hsq : ∀ c : C, c ^ 2 ∈ K) {n : C} (hn : Odd (orderOf n)) : n ∈ K := by
  obtain ⟨m, hm⟩ := hn
  have h1 : n ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one n
  have e : n = ((n ^ 2) ^ m)⁻¹ := by
    rw [← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ']
    exact h1
  rw [e]
  exact K.inv_mem (K.pow_mem (hsq n) m)

theorem oddCore_bot_of_sq_mem {C : Type*} [Group C] [Finite C] {K : Subgroup C} [K.Normal]
    (hsq : ∀ c : C, c ^ 2 ∈ K) (hK : CFSG.oddCore K = ⊥) : CFSG.oddCore C = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  have hNK : N ≤ K := fun n hn => mem_of_odd_of_sq_mem hsq (hN.2.of_dvd_nat
    (Subgroup.orderOf_dvd_natCard N hn))
  have hdvd : Nat.card (N.subgroupOf K) ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : N.subgroupOf K ≤ CFSG.oddCore K :=
    le_oddCore_of_normal_odd (hN.1.subgroupOf K) (hN.2.of_dvd_nat hdvd)
  rw [hK, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  exact eq_bot_iff.2 fun n hn => by
    have := hle.le_bot ⟨hn, hNK hn⟩
    exact this

theorem oddCore_bot_of_selfCentralizing {C : Type*} [Group C] [Finite C] {Q : Subgroup C}
    (hQn : Q.Normal) (hQ : IsPGroup 2 Q) (hC : Subgroup.centralizer (Q : Set C) ≤ Q) :
    CFSG.oddCore C = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  have hNQ : ∀ x, x ∈ N → x ∈ Q → x = 1 := by
    intro x hxN hxQ
    have hodd : Odd (orderOf x) := hN.2.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hxN)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨x, hxQ⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra h
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ] at hodd
      exact Nat.not_even_iff_odd.2 hodd ⟨2 ^ j, by ring⟩
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  have hcomm : ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n := by
    intro n hn q hq
    have h1 : n * q * n⁻¹ * q⁻¹ ∈ N := by
      have := hN.1.conj_mem n⁻¹ (N.inv_mem hn) q
      rw [show n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) by group]
      exact N.mul_mem hn this
    have h2 : n * q * n⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQn.conj_mem q hq n) (Q.inv_mem hq)
    have := hNQ _ h1 h2
    calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
      _ = q * n := by rw [this, one_mul]
  refine eq_bot_iff.2 fun n hn => ?_
  have hnQ : n ∈ Q := hC (Subgroup.mem_centralizer_iff.2 fun q hq => (hcomm n hn q hq).symm)
  exact hNQ n hn hnQ

@[expose] def centralizerConjEquiv {G : Type*} [Group G] (a g : G) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({g * a * g⁻¹} : Set G) where
  toFun x := ⟨g * x * g⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * y * g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [h]
      _ = a * (g⁻¹ * y * g) := by group⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem oddCore_centralizer_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b)
    (ha : CFSG.oddCore (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({b} : Set G)) = ⊥ := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact oddCore_bot_of_mulEquiv (centralizerConjEquiv a g).symm ha

end CFSG.Sporadic.HNOddCore
