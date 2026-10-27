module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313Pre

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

noncomputable local instance yo2_fintypeW3 : Fintype S152N.W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance yo2_decEqW3 : DecidableEq S152N.W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

theorem yo2_w3_centralizer :
    ∀ w : S152N.W3, w ^ 4 = 1 → (∀ x : S152N.W3, x ^ 3 = 1 → w * x = x * w) → w = 1 := by
  decide +kernel

theorem yo2_wreath_of_iso {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hTsyl : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3) :
    Nat.card T = 8 * Nat.card (pCoreOf 2 H) ∧
      ∀ t ∈ T, (∀ y ∈ oTwoUpper H, ⁅t, y⁆ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H := by
  have hTH : T ≤ H := hTsyl.1
  have hKT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hD : Nat.card (imageOTwoQuot H T) = 8 := by
    have hsyl : IsSylowTwoOf ((imageOTwoQuot H T).map (φ : OTwoQuot H →* S152N.W3)) ⊤ :=
      S152N.isSylowTwoOf_image hTsyl φ
    have h9 := S152N.W3.index_eq_nine hsyl
    have hinj : Function.Injective (φ : OTwoQuot H →* S152N.W3) := φ.injective
    have hm := Subgroup.card_mul_index ((imageOTwoQuot H T).map (φ : OTwoQuot H →* S152N.W3))
    rw [h9, S152N.W3.card_eq, Subgroup.card_map_of_injective hinj] at hm
    omega
  have hrel : (pCoreOf 2 H).relIndex T = 8 := by
    have h1 := C1Pack12.relIndex_inf_pCoreOf_eq_card hTH
    rw [inf_eq_right.mpr hKT, hD] at h1
    exact h1
  have hcard : Nat.card T = 8 * Nat.card (pCoreOf 2 H) := by
    have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
    rw [inf_eq_left.mpr hKT, hrel] at h2
    omega
  refine ⟨hcard, fun t ht hcomm => ?_⟩
  have htH : t ∈ H := hTH ht
  have hw4 : Lem3313.piH φ ⟨t, htH⟩ ^ 4 = 1 := by
    rw [← map_pow]
    refine (Lem3313.piH_eq_one_iff φ _).mpr ?_
    simpa using Lem3313.pow_four_mem_of_iso hTsyl φ ht
  have hcomm' : ∀ x : S152N.W3, x ^ 3 = 1 →
      Lem3313.piH φ ⟨t, htH⟩ * x = x * Lem3313.piH φ ⟨t, htH⟩ := by
    intro x hx
    have hxI : x ∈ (imageOTwoQuot H (oTwoUpper H)).map (φ : OTwoQuot H →* S152N.W3) := by
      rw [C1Pack12.map_imageOTwoQuot_oTwoUpper φ]
      exact S152N.W3.mem_N0_of_pow_three x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxI
    obtain ⟨y, hyH, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hcH : ⁅t, y⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem htH hyH) (H.inv_mem htH)) (H.inv_mem hyH)
    have h1 : Lem3313.piH φ ⟨⁅t, y⁆, hcH⟩ = 1 :=
      (Lem3313.piH_eq_one_iff φ _).mpr (hcomm y hyY)
    have e : (⟨⁅t, y⁆, hcH⟩ : ↥H) = ⟨t, htH⟩ * ⟨y, hyH⟩ * ⟨t, htH⟩⁻¹ * ⟨y, hyH⟩⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    show Lem3313.piH φ ⟨t, htH⟩ * Lem3313.piH φ ⟨y, hyH⟩ =
      Lem3313.piH φ ⟨y, hyH⟩ * Lem3313.piH φ ⟨t, htH⟩
    calc Lem3313.piH φ ⟨t, htH⟩ * Lem3313.piH φ ⟨y, hyH⟩
        = (Lem3313.piH φ ⟨t, htH⟩ * Lem3313.piH φ ⟨y, hyH⟩ * (Lem3313.piH φ ⟨t, htH⟩)⁻¹ *
            (Lem3313.piH φ ⟨y, hyH⟩)⁻¹) *
          (Lem3313.piH φ ⟨y, hyH⟩ * Lem3313.piH φ ⟨t, htH⟩) := by group
      _ = Lem3313.piH φ ⟨y, hyH⟩ * Lem3313.piH φ ⟨t, htH⟩ := by rw [h1, one_mul]
  have hw1 : Lem3313.piH φ ⟨t, htH⟩ = 1 := yo2_w3_centralizer _ hw4 hcomm'
  exact (Lem3313.piH_eq_one_iff φ ⟨t, htH⟩).mp hw1

theorem yo2_wreath {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hTsyl : IsSylowTwoOf T H) (hTop : pCoreOf 2 H ≠ ⊥)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) :
    Nat.card T = 8 * Nat.card (pCoreOf 2 H) ∧
      ∀ t ∈ T, (∀ y ∈ oTwoUpper H, ⁅t, y⁆ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H :=
  yo2_wreath_of_iso hTsyl (oTwoQuotEquiv e)

end CFSG.Quasithin.H13.NF314pt
