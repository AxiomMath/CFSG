module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.Sporadic.J4.QT2LocX0CentMain
public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore
public import CFSG.Quasithin.H13.GoldschmidtCTKFamSporLoc

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint.NativeSporadic

theorem card_le_card_mul_card_centralizer {G : Type*} [Group G] [Finite G] {K N : Subgroup G}
    (hKN : K ≤ N) (hN : N ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K) :
    Nat.card N ≤ Nat.card K * Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  let x' : N := ⟨x, hKN hx⟩
  have h1 := Subgroup.index_centralizer_eq_ncard x'
  have hsub : Subtype.val '' (_root_.conjugatesOf x') ⊆ (K : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 (show IsConj x' y from hy)
    have hcy : (y : G) = (c : G) * x * (c : G)⁻¹ := by
      rw [← hc]
      rfl
    rw [hcy]
    exact (Subgroup.mem_normalizer_iff.1 (hN c.2) x).1 hx
  have hconj : (_root_.conjugatesOf x').ncard ≤ Nat.card K := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    calc (Subtype.val '' _root_.conjugatesOf x').ncard ≤ (K : Set G).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card K := (Nat.card_coe_set_eq (K : Set G)).symm
  have hcent : Nat.card ↥(Subgroup.centralizer ({x'} : Set N)) ≤
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨(c.1 : G), ?_⟩) ?_
    · have := (Subgroup.mem_centralizer_singleton_iff.1 c.2)
      exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
    · intro a b hab
      have h3 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h3)
  calc Nat.card N = Nat.card ↥(Subgroup.centralizer ({x'} : Set N)) *
          (Subgroup.centralizer ({x'} : Set N)).index :=
        (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) * Nat.card K := by
        rw [h1]
        exact Nat.mul_le_mul hcent hconj
    _ = Nat.card K * Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := Nat.mul_comm _ _

theorem card_centralizer_le_j4
    {S : Type} [Group S] (e : S ≃* Carrier .J4) {x : S} (hx : orderOf x = 5) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set S)) ≤ 6720 := by
  let e' : S ≃* ↥CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hx' : orderOf (e' x) = 5 := by rw [MulEquiv.orderOf_eq]; exact hx
  have h := CFSG.QuasithinUnique.A5.Dec2.card_centralizer_of_orderOf_five
    (CFSG.Sporadic.J4.QT2.centralizer_fiveElt_eq CFSG.Sporadic.J4.j4Facts).le hx'
  rw [← h]
  refine Nat.card_le_card_of_injective (fun c => ⟨e' c.1, ?_⟩) ?_
  · have := Subgroup.mem_centralizer_singleton_iff.1 c.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, this])
  · intro a b hab
    have h3 := congrArg Subtype.val hab
    exact Subtype.ext (e'.injective h3)

theorem not_a5Config_j4
    {S : Type} [Group S] [Finite S] (e : S ≃* Carrier .J4) : ¬ A5Config S := by
  intro h
  obtain ⟨K, V, T₁, T₂, hVK, hV16, -, hΔ, hT1N, hN, hT1S, hT2S, hT12, hrel⟩ := h
  have hcardV : Nat.card ↥(V.subgroupOf K) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV16]
  have hK : Nat.card K = 960 := hΔ.card_eq hcardV
  obtain ⟨x, hxK, hx5⟩ := exists_orderOf_five_of_card_eq_960 hK
  have hKN : K ≤ Subgroup.normalizer (V : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).1 hΔ.normal
  have hnorm : Subgroup.normalizer (V : Set S) ≤ Subgroup.normalizer (K : Set S) := by
    rw [hN]
    exact sup_le Subgroup.le_normalizer hT1N
  have hupper := card_le_card_mul_card_centralizer hKN hnorm hxK
  have hC := card_centralizer_le_j4 e hx5
  rw [hK] at hupper
  have hUp : Nat.card ↥(Subgroup.normalizer (V : Set S)) ≤ 960 * 6720 :=
    hupper.trans (Nat.mul_le_mul_left _ hC)
  have hSc : Nat.card S = 2 ^ 21 * 41377816699065 :=
    (Nat.card_congr e.toEquiv).trans (CFSG.Sporadic.J4.card_J4.trans (by norm_num))
  have hT2 : Nat.card T₂ = 2 ^ 21 :=
    CFSG.QuasithinUnique.A5.G3.card_eq_of_isSylowTwoOf hT2S (by norm_num) hSc
  have hT2c : Nat.card T₁ * T₁.relIndex T₂ = Nat.card T₂ := by
    have := Subgroup.card_mul_index (T₁.subgroupOf T₂)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT12).toEquiv] at this
  have hT1ge : 2 ^ 20 ≤ Nat.card T₁ := by
    rw [hT2] at hT2c
    rcases Nat.eq_zero_or_pos (T₁.relIndex T₂) with h0 | hpos
    · rw [h0] at hT2c
      omega
    · interval_cases hr : T₁.relIndex T₂ <;> omega
  obtain ⟨a, ha⟩ := hT1S.2.1.exists_card_eq
  have ha20 : 20 ≤ a := by
    have h20 : 2 ^ 20 ≤ 2 ^ a := ha ▸ hT1ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h20
  have hdvd1 : 2 ^ 20 ∣ Nat.card ↥(Subgroup.normalizer (V : Set S)) := by
    have h1 : Nat.card T₁ ∣ Nat.card ↥(Subgroup.normalizer (V : Set S)) :=
      Subgroup.card_dvd_of_le (by rw [hN]; exact le_sup_right)
    rw [ha] at h1
    exact (pow_dvd_pow 2 ha20).trans h1
  have hdvd2 : 960 ∣ Nat.card ↥(Subgroup.normalizer (V : Set S)) := by
    have := Subgroup.card_dvd_of_le hKN
    rwa [hK] at this
  have hdvd3 : 2 ^ 20 * 15 ∣ Nat.card ↥(Subgroup.normalizer (V : Set S)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hdvd1
      ((by norm_num : 15 ∣ 960).trans hdvd2)
  have hle := Nat.le_of_dvd Nat.card_pos hdvd3
  norm_num at hle hUp
  omega

end CFSG.Quasithin.H13.CTK
