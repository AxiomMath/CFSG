module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13
open S152N

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

noncomputable local instance instFintypeW3a2 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3a2 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0a2 : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem a2_W3_sq_inverts_N0 :
    ∀ w : W3, w ^ 4 = 1 → w ^ 2 ≠ 1 → ∀ n ∈ W3.N0, w ^ 2 * n * (w ^ 2)⁻¹ * n = 1 := by
  decide +kernel

theorem a2_comm_of_sq_eq_one {A : Type*} [Group A] {α β : A} (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (hαβ : (α * β) ^ 2 = 1) : α * β = β * α := by
  have h1 : α * α = 1 := (pow_two α).symm.trans hα
  have h2 : β * β = 1 := (pow_two β).symm.trans hβ
  have h3 : α * β * (α * β) = 1 := (pow_two (α * β)).symm.trans hαβ
  have ha : α⁻¹ = α := inv_eq_of_mul_eq_one_right h1
  have hb : β⁻¹ = β := inv_eq_of_mul_eq_one_right h2
  calc α * β = (α * β)⁻¹ := eq_inv_of_mul_eq_one_left h3
    _ = β⁻¹ * α⁻¹ := mul_inv_rev α β
    _ = β * α := by rw [ha, hb]

theorem a2_piH_comm_term (φ : OTwoQuot H ≃* S152N.W3) {A B Y : ↥H}
    (h : Lem3313.piH φ A * Lem3313.piH φ B = Lem3313.piH φ B * Lem3313.piH φ A) :
    Lem3313.piH φ (A * B * Y * (A * B)⁻¹ * (B * A * Y * (B * A)⁻¹)⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [← h]
  exact mul_inv_cancel _

theorem exists_sq_ne_one_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3) :
    ∃ x : ↥H, (x : G) ∈ T ∧ Lem3313.piH φ x ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, y, hy, hne⟩ := Lem3313.exists_noncomm_of_iso hT φ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hyH : y ∈ H := hYH hy
  have haH : a ∈ H := hT.1 ha
  have hbH : b ∈ H := hT.1 hb
  have habH : a * b ∈ H := H.mul_mem haH hbH
  have hbaH : b * a ∈ H := H.mul_mem hbH haH
  have hcomm : Lem3313.piH φ (⟨a, haH⟩ : ↥H) * Lem3313.piH φ (⟨b, hbH⟩ : ↥H) =
      Lem3313.piH φ (⟨b, hbH⟩ : ↥H) * Lem3313.piH φ (⟨a, haH⟩ : ↥H) := by
    refine a2_comm_of_sq_eq_one (hcon (⟨a, haH⟩ : ↥H) ha) (hcon (⟨b, hbH⟩ : ↥H) hb) ?_
    rw [← map_mul]
    exact hcon ((⟨a, haH⟩ : ↥H) * (⟨b, hbH⟩ : ↥H)) (T.mul_mem ha hb)
  have hE := a2_piH_comm_term φ (A := (⟨a, haH⟩ : ↥H)) (B := (⟨b, hbH⟩ : ↥H))
    (Y := (⟨y, hyH⟩ : ↥H)) hcomm
  apply hne
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : a * b * y * (a * b)⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H habH) y).mp hy
    have h2 : b * a * y * (b * a)⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hbaH) y).mp hy
    exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem h2)
  · exact (Lem3313.piH_eq_one_iff φ _).mp hE

theorem piH_mem_N0 (φ : OTwoQuot H ≃* S152N.W3) {y : G} (hyH : y ∈ H)
    (hy : y ∈ oTwoUpper H) : Lem3313.piH φ ⟨y, hyH⟩ ∈ S152N.W3.N0 := by
  have hmem : Lem3313.piH φ ⟨y, hyH⟩ ∈
      (imageOTwoQuot H (oTwoUpper H)).map (φ : OTwoQuot H →* S152N.W3) := by
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk ⟨y, hyH⟩, ?_, rfl⟩
    exact mem_imageOTwoQuot_iff.mpr ⟨y, hyH, hy, rfl⟩
  rwa [C1Pack12.map_imageOTwoQuot_oTwoUpper φ] at hmem

theorem exists_inverting_square_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3) :
    ∃ g ∈ T, ∀ y ∈ oTwoUpper H, g ^ 2 * y * (g ^ 2)⁻¹ * y ∈ pCoreOf 2 H := by
  obtain ⟨x, hxT, hx2⟩ := exists_sq_ne_one_of_iso hT φ
  refine ⟨(x : G), hxT, fun y hy => ?_⟩
  have hyH : y ∈ H := oTwoUpper_le H hy
  have hx2H : (x : G) ^ 2 ∈ H := H.pow_mem x.2 2
  have hmem : (x : G) ^ 2 * y * ((x : G) ^ 2)⁻¹ * y ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hx2H hyH) (H.inv_mem hx2H)) hyH
  have hw4 : Lem3313.piH φ x ^ 4 = 1 := by
    have h4 : Lem3313.piH φ ⟨(x : G) ^ 4, H.pow_mem x.2 4⟩ = 1 :=
      (Lem3313.piH_eq_one_iff φ _).mpr (Lem3313.pow_four_mem_of_iso hT φ hxT)
    have e : (⟨(x : G) ^ 4, H.pow_mem x.2 4⟩ : ↥H) = x ^ 4 := Subtype.ext (by simp)
    rwa [e, map_pow] at h4
  have key := a2_W3_sq_inverts_N0 _ hw4 hx2 _ (piH_mem_N0 φ hyH hy)
  have e : (⟨(x : G) ^ 2 * y * ((x : G) ^ 2)⁻¹ * y, hmem⟩ : ↥H) =
      x ^ 2 * (⟨y, hyH⟩ : ↥H) * (x ^ 2)⁻¹ * (⟨y, hyH⟩ : ↥H) := Subtype.ext (by simp)
  have hE : Lem3313.piH φ ⟨(x : G) ^ 2 * y * ((x : G) ^ 2)⁻¹ * y, hmem⟩ = 1 := by
    rw [e]
    simp only [map_mul, map_inv, map_pow]
    exact key
  exact (Lem3313.piH_eq_one_iff φ _).mp hE

theorem A2Cfg.exists_inverting_square (c : A2Cfg G T M L D H K q) :
    ∃ g ∈ T, ∀ y ∈ oTwoUpper H, g ^ 2 * y * (g ^ 2)⁻¹ * y ∈ pCoreOf 2 H := by
  obtain ⟨e⟩ := c.nf.wreath
  exact exists_inverting_square_of_iso c.sylow_H (CFSG.Quasithin.H13.oTwoQuotEquiv e)

end CFSG.Quasithin.H13.NFa2
