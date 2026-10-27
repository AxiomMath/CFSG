module

public import CFSG.Quasithin.Background.PushS3Klein
public import CFSG.Quasithin.Background.PushS3Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatContract

public section

namespace CFSG.Quasithin.F6.PushS3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D]

theorem card_oddOrderSubgroup_eq_twelve_of_campbell (H S N : Subgroup D) (y a : D)
    (hS : S ≤ H) (hS2 : IsPGroup 2 S) (hSidx : S.relIndex H = 3)
    (hSn : ¬ H ≤ Subgroup.normalizer (S : Set D))
    (hNle : N ≤ H) (hNk : IsKleinFour ↥N) (hNH : H ≤ Subgroup.normalizer (N : Set D))
    (hyH : y ∈ H) (hy3 : orderOf y = 3) (hyN : ∀ n ∈ N, y * n * y⁻¹ = n → n = 1)
    (haS : a ∈ S) (haN : ∃ n ∈ N, a * n * a⁻¹ ≠ n) (hchar : CharTwo H)
    (hnc : ∀ C : Subgroup D, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set D))
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (N : Set D)) :
    Nat.card ↥(oddOrderSubgroup H) = 12 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hNk
  have hidx : (S.subgroupOf H).index = 3 := hSidx
  have hSyl : IsSylowTwoOf S H := ⟨hS, hS2, by rw [hidx]; decide⟩
  have hnn : ¬ (S.subgroupOf H).Normal := fun hn =>
    hSn ((Subgroup.normal_subgroupOf_iff_le_normalizer hS).mp hn)
  have hMP : ¬ H ≤ S := by
    intro hHS
    have h1 : S.relIndex H = 1 := Subgroup.relIndex_eq_one.mpr hHS
    omega
  have hmax : ∀ Y : Subgroup D, S ≤ Y → Y < H → Y ≤ S := by
    intro Y hSY hYH
    have h1 := Subgroup.relIndex_mul_relIndex S Y H hSY hYH.le
    have h2 : Y.relIndex H ≠ 1 := fun h => (not_le_of_gt hYH) (Subgroup.relIndex_eq_one.mp h)
    have h3 : Y.relIndex H ∣ 3 := ⟨S.relIndex Y, by rw [← hSidx, ← h1, mul_comm]⟩
    have h4 : Y.relIndex H = 3 := ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left h2
    have h5 : S.relIndex Y = 1 := by rw [h4, hSidx] at h1; omega
    exact Subgroup.relIndex_eq_one.mp h5
  have helem : IsElemAbelian 2 N := by
    refine ⟨IsKleinFour.isMulCommutative, fun x hx => ?_⟩
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥N)
    rw [IsKleinFour.exponent_two] at h
    exact congrArg Subtype.val h
  have hy : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have h3 : actOn N H hNH ⟨y, hyH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  have hnt : Nontrivial ↥N :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four]; norm_num)
  have h31 : actOn N H hNH ⟨y, hyH⟩ ≠ 1 := by
    intro h1
    obtain ⟨u0, hu0⟩ := exists_ne (1 : ↥N)
    apply hu0
    have hc := (actOn_eq_one_iff hNH ⟨y, hyH⟩).1 h1 u0
    exact Subtype.ext (hyN _ u0.2 (mul_inv_eq_iff_eq_mul.mpr hc))
  obtain ⟨k, hk⟩ := hS2 ⟨a, haS⟩
  have h2 : actOn N H hNH ⟨a, hS haS⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨a, hS haS⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have h21 : actOn N H hNH ⟨a, hS haS⟩ ≠ 1 := by
    intro h1
    obtain ⟨n, hn, hne⟩ := haN
    exact hne (mul_inv_eq_iff_eq_mul.mpr ((actOn_eq_one_iff hNH ⟨a, hS haS⟩).1 h1 ⟨n, hn⟩))
  have hind := exists_induce_of_orders hNH h3 h31 h2 h21
  have hred : IsTwoReducedIn H N := isTwoReduced_of_induce hNle hNH helem hind
  obtain ⟨ρ, ψ, hψρ, -, hsurj⟩ := exists_natural_rep (P := H) (U := N) hNH
  have hψker : (ψ.toMonoidHom).ker =
      (Subgroup.centralizer (oddOrderSubgroup H : Set D)).subgroupOf N := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      have h1 : u = 1 := ψ.injective (hu.trans (map_one ψ).symm)
      rw [h1]
      exact Subgroup.one_mem _
    · intro hu
      have hy' : y ∈ oddOrderSubgroup H :=
        Subgroup.subset_closure ⟨hyH, by rw [hy3]; exact ⟨1, rfl⟩⟩
      have hc : y * (u : D) = (u : D) * y := Subgroup.mem_centralizer_iff.mp hu y hy'
      have h1 : u = 1 := Subtype.ext (hyN _ u.2 (mul_inv_eq_iff_eq_mul.mpr hc))
      rw [h1]
      exact map_one ψ.toMonoidHom
  obtain ⟨ϱ', φ, hset⟩ := natQuotSetting_of_module (k := ZMod 2) (S := S) (P := H) (M := S)
    (W := N) hSyl hnn le_rfl hMP hmax hred ρ (hsurj.2 hind) ψ.toMonoidHom ψ.surjective
    (fun p u u' hu' => hψρ p u u' hu') hψker
  have hJ' : ⁅elemThompsonIn 2 (S.subgroupOf H), N.subgroupOf H⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    have h1 := congrArg (Subgroup.map H.subtype) hbot
    rw [Subgroup.map_commutator, elemThompsonIn_subgroupOf_map_eq hS,
      Subgroup.map_subgroupOf_eq_of_le hNle, Subgroup.map_bot] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  obtain ⟨-, -, -, -, h5⟩ := hset.actual_Campbell_natural_minimal_parabolic_chi0_block
    (charTwo_top_of_charTwo hchar) (noCharNormal_top_of hS hnc) hJ' (n := 1) le_rfl
    (by rw [Nat.card_zmod]; norm_num)
  obtain ⟨-, ⟨e⟩⟩ := h5 rfl
  have hcard : Nat.card ↥(oddOrderSubgroup (⊤ : Subgroup ↥H)) = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hL : oddOrderSubgroup (⊤ : Subgroup ↥H) = (oddOrderSubgroup H).subgroupOf H := by
    rw [← oddOrderSubgroup_top_map H]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  rw [hL] at hcard
  rw [← hcard]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oddOrderSubgroup_le H)).toEquiv).symm

theorem two_subgroup_card_le_four_of_campbell (H S N : Subgroup D) (y a : D)
    (hS : S ≤ H) (hS2 : IsPGroup 2 S) (hSidx : S.relIndex H = 3)
    (hSn : ¬ H ≤ Subgroup.normalizer (S : Set D))
    (hNle : N ≤ H) (hNk : IsKleinFour ↥N) (hNH : H ≤ Subgroup.normalizer (N : Set D))
    (hyH : y ∈ H) (hy3 : orderOf y = 3) (hyN : ∀ n ∈ N, y * n * y⁻¹ = n → n = 1)
    (haS : a ∈ S) (haN : ∃ n ∈ N, a * n * a⁻¹ ≠ n) (hchar : CharTwo H)
    (hnc : ∀ C : Subgroup D, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set D))
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (N : Set D)) :
    ∀ X : Subgroup D, X ≤ oddOrderSubgroup H → IsPGroup 2 X → Nat.card X ≤ 4 := by
  intro X hX hX2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h12 := card_oddOrderSubgroup_eq_twelve_of_campbell H S N y a hS hS2 hSidx hSn hNle hNk hNH
    hyH hy3 hyN haS haN hchar hnc hJ
  have hdvd : Nat.card X ∣ 12 := h12 ▸ Subgroup.card_dvd_of_le hX
  obtain ⟨n, hn⟩ := hX2.exists_card_eq
  rw [hn] at hdvd ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 h
    have := h8.trans hdvd
    omega
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

end CFSG.Quasithin.F6.PushS3
