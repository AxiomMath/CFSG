module

public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.Quasithin.Vol2.Ch11SecA02Card

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsNatBlock (X : Subgroup G) (n : ℕ) : Prop :=
  IsShort2 X ∧ IsLin2Type X n ∧ blockZ X = ⊥ ∧ blockQ X = blockU X

variable {X : Subgroup G} {n : ℕ}

theorem commutator_le_inf_of_normalizes {N U : Subgroup G}
    (hNU : N ≤ Subgroup.normalizer (U : Set G)) (hUN : U ≤ Subgroup.normalizer (N : Set G)) :
    ⁅N, U⁆ ≤ N ⊓ U := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hUN hb) a⁻¹).mp (N.inv_mem ha)
    have : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact N.mul_mem ha h1
  · have h1 : a * b * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hNU ha) b).mp hb
    rw [commutatorElement_def]
    exact U.mul_mem h1 (U.inv_mem hb)

namespace IsNatBlock

variable (h : IsNatBlock X n)
include h

theorem blockU_le : blockU X ≤ X := by
  rw [← h.2.2.2]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 X

theorem le_normalizer_blockU : X ≤ Subgroup.normalizer (blockU X : Set G) := by
  rw [← h.2.2.2]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X

theorem irred {W : Subgroup G} (hW : W ≤ blockU X) (hWn : X ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = blockU X := by
  have := h.1.2.2.2.2.2 W (by rw [h.2.2.1]; exact bot_le) hW hWn
  rwa [h.2.2.1] at this

theorem inf_centralizer_le : X ⊓ Subgroup.centralizer (blockU X : Set G) ≤ blockU X := by
  have h2 := h.1.2.1
  rw [← h.2.2.2]
  exact h2

theorem inf_centralizer_self : X ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzU : z ∈ blockU X := h.inf_centralizer_le
    ⟨hz.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.blockU_le) hz.2⟩
  have : z ∈ blockZ X := ⟨hzU, hz.2⟩
  rwa [h.2.2.1] at this

theorem mem_blockU_iff (x : ↥X) : (x : G) ∈ blockU X ↔ x ∈ CFSG.pCore 2 ↥X := by
  rw [← h.2.2.2]
  exact C1Pack.coe_mem_pCoreOf_iff X x

theorem normal_cases [Finite G] (hn : 2 ≤ n) {N : Subgroup G} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set G)) : N = ⊥ ∨ N = blockU X ∨ N = X := by
  have hWn : X ≤ Subgroup.normalizer ((N ⊓ blockU X : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hN hg, h.le_normalizer_blockU hg⟩
  rcases h.irred inf_le_right hWn with hW | hW
  · left
    have hc := commutator_le_inf_of_normalizes (hNX.trans h.le_normalizer_blockU)
      (h.blockU_le.trans hN)
    rw [hW, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxU : x ∈ blockU X := h.inf_centralizer_le ⟨hNX hx, hc hx⟩
    have : x ∈ N ⊓ blockU X := ⟨hx, hxU⟩
    rwa [hW] at this
  · right
    have hUN : blockU X ≤ N := hW ▸ inf_le_left
    obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h.2.1
    have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup hn hF
    have hNn : (N.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hN
    have hmapn : ((N.subgroupOf X).map α).Normal := hNn.map α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf X).map α) with hb | ht
    · left
      refine le_antisymm (fun x hx => ?_) hUN
      have h1 : α ⟨x, hNX hx⟩ ∈ (N.subgroupOf X).map α := ⟨⟨x, hNX hx⟩, hx, rfl⟩
      rw [hb, Subgroup.mem_bot, ← MonoidHom.mem_ker, hαk] at h1
      exact (h.mem_blockU_iff ⟨x, hNX hx⟩).mpr h1
    · right
      refine le_antisymm hNX fun x hx => ?_
      have h1 : α ⟨x, hx⟩ ∈ (N.subgroupOf X).map α := by rw [ht]; trivial
      obtain ⟨y, hy, hyx⟩ := h1
      have h2 : y⁻¹ * ⟨x, hx⟩ ∈ α.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hyx,
        inv_mul_cancel]
      rw [hαk] at h2
      have h3 : ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ N := hUN ((h.mem_blockU_iff _).mpr h2)
      have e : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
      rw [e]
      exact N.mul_mem hy h3

theorem mem_of_central_mod [Finite G] (hn : 2 ≤ n) {N : Subgroup G} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set G)) {z : G} (hz : z ∈ X)
    (hc : ∀ x ∈ X, z * x * z⁻¹ * x⁻¹ ∈ N) : z ∈ N := by
  rcases h.normal_cases hn hNX hN with rfl | rfl | rfl
  · have hzc : z ∈ Subgroup.centralizer (X : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun x hx => by
        have := hc x hx
        rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
        exact this.symm
    have : z ∈ X ⊓ Subgroup.centralizer (X : Set G) := ⟨hz, hzc⟩
    rwa [h.inf_centralizer_self] at this
  · obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h.2.1
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF'
    have hcen : α ⟨z, hz⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro A
      obtain ⟨x, rfl⟩ := hαs A
      have h1 : ⟨z, hz⟩ * x * (⟨z, hz⟩ : ↥X)⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥X :=
        (h.mem_blockU_iff _).mp (hc x x.2)
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h2 : (r + 1) ^ 2 = 0 := by
        rw [CharTwo.add_sq, hr, one_pow, CharTwo.add_self_eq_zero]
      have h3 : r + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h2
      rw [← CharTwo.neg_eq r, ← add_eq_zero_iff_neg_eq']
      rw [add_comm]
      exact h3
    have h4 : α ⟨z, hz⟩ = 1 := by
      apply Subtype.ext
      rw [← hrz, hr1]
      simp
    have h5 : (⟨z, hz⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by rw [← hαk]; exact h4
    exact (h.mem_blockU_iff _).mpr h5
  · exact hz

theorem card_blockU [Finite G] : Nat.card ↥(blockU X) = 2 ^ (2 * n) := by
  obtain ⟨F, _, _, hF, -, -, -, β, hβs, hβk, -⟩ := h.2.1
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, h.2.2.1]
    simp
  rw [Nat.card_congr (Equiv.ofBijective (β : ↥(blockU X) → Multiplicative (Fin 2 → F))
    ⟨hinj, hβs⟩)]
  change Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]

theorem card_pCore [Finite G] : Nat.card ↥(CFSG.pCore 2 ↥X) = 2 ^ (2 * n) := by
  rw [← h.card_blockU, ← h.2.2.2, blockQ, pCoreOf,
    Subgroup.card_map_of_injective X.subtype_injective]

theorem card_quot [Finite G] : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 2 ^ n * Ch11.SecA.oSL2 n := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h.2.1
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)).toEquiv, Ch11.SecA.card_SL_two hF']

theorem card [Finite G] : Nat.card ↥X = 2 ^ (3 * n) * Ch11.SecA.oSL2 n := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X), h.card_quot,
    h.card_pCore, show 3 * n = n + 2 * n by ring, pow_add]
  ring

end IsNatBlock

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
