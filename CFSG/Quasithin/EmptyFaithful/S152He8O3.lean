module

public import CFSG.Quasithin.EmptyFaithful.S152He8Rank
public import CFSG.Quasithin.EmptyFaithful.S152He8Act

public section

namespace CFSG.Quasithin.He8

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.C1Pack12

section N0

noncomputable local instance instFintypeW3 : Fintype S152N.W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3 : DecidableEq S152N.W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0W3 : DecidablePred (· ∈ S152N.W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem N0_comm : ∀ a b : S152N.W3, a ∈ S152N.W3.N0 → b ∈ S152N.W3.N0 → a * b = b * a := by
  decide +kernel

end N0

variable {G : Type} [Group G] [Finite G]

theorem mem_of_cube_eq_one {Mc H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3)
    (hHMc : H ≤ Mc) (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hrk : CFSG.Open.pRank 3 Mc ≤ 2) {x : G} (hx : x ∈ Mc) (hx3 : x ^ 3 = 1)
    (hc : ∀ y ∈ oTwoUpper H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) :
    x ∈ oTwoUpper H := by
  classical
  by_contra hxK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKMc : oTwoUpper H ≤ Mc := (oTwoUpper_le H).trans hHMc
  set K := oTwoUpper H with hKdef
  set N := pCoreOf 2 K with hNdef
  have hNK : N ≤ K := pCoreOf_le 2 K
  have hNn : Mc ≤ Subgroup.normalizer (N : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)
  let N' : Subgroup ↥Mc := N.subgroupOf Mc
  have : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  let π : ↥Mc →* ↥Mc ⧸ N' := QuotientGroup.mk' N'
  let ΨK : ↥K →* ↥Mc ⧸ N' := π.comp (Subgroup.inclusion hKMc)
  have hΨ : ∀ y : ↥K, ΨK y = 1 ↔ (y : G) ∈ N := by
    intro y
    change π (Subgroup.inclusion hKMc y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hΨκ : ∀ y : ↥K, ΨK y = 1 ↔ kappa φ y = 1 := fun y => (hΨ y).trans (kappa_eq_one_iff φ y).symm
  let A : Subgroup (↥Mc ⧸ N') := ΨK.range
  have hAcard : Nat.card A = 9 := by
    have h1 : ΨK.ker = N.subgroupOf K := by
      ext y
      rw [MonoidHom.mem_ker, hΨ, Subgroup.mem_subgroupOf]
    have h2 := Subgroup.index_ker ΨK
    rw [h1] at h2
    have h3 : (N.subgroupOf K).index = 9 := relIndex_pCoreOf_oTwoUpper φ
    rw [h3] at h2
    exact h2.symm
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨y₁, rfl⟩ _ ⟨y₂, rfl⟩
    have h1 : kappa φ (y₁ * y₂ * (y₂ * y₁)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        N0_comm _ _ (kappa_mem_N0 φ y₁) (kappa_mem_N0 φ y₂)]
      group
    have h2 : ΨK (y₁ * y₂ * (y₂ * y₁)⁻¹) = 1 := (hΨκ _).mpr h1
    rw [map_mul, map_mul, map_inv, map_mul] at h2
    exact mul_inv_eq_one.mp h2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow]
    refine (hΨκ _).mpr ?_
    rw [map_pow]
    exact S152N.W3.pow_three_of_mem_N0 _ (kappa_mem_N0 φ y)
  let xm : ↥Mc := ⟨x, hx⟩
  have hz3 : π xm ^ 3 = 1 := by
    rw [← map_pow]
    have : xm ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hzA : π xm ∉ A := by
    rintro ⟨y, hy⟩
    have hy' : π xm = π (Subgroup.inclusion hKMc y) := hy.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hy'
    have h1 : (xm : G)⁻¹ * (y : G) ∈ N := hy'
    apply hxK
    have h2 : (y : G) * ((xm : G)⁻¹ * (y : G))⁻¹ ∈ K :=
      K.mul_mem y.2 (K.inv_mem (hNK h1))
    have h3 : (y : G) * ((xm : G)⁻¹ * (y : G))⁻¹ = x := by
      change (y : G) * ((x⁻¹ * (y : G))⁻¹) = x
      group
    rwa [h3] at h2
  have hzc : ∀ a ∈ A, a * π xm = π xm * a := by
    rintro _ ⟨y, rfl⟩
    have h1 : π xm * π (Subgroup.inclusion hKMc y) * (π xm)⁻¹ * (π (Subgroup.inclusion hKMc y))⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      exact hc y y.2
    have h2 : ΨK y = π (Subgroup.inclusion hKMc y) := rfl
    rw [h2]
    exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := π xm) (g₂ := π (Subgroup.inclusion hKMc y))).mp
      (by simpa [commutatorElement_def] using h1)).symm
  have h3 := three_le_pRank_of_central hAcomm hA3 hAcard hz3 hzA hzc
  have hnd : ¬ 3 ∣ Nat.card N' := by
    have hN2 : IsPGroup 2 N := pCoreOf_isPGroup 2 K
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hN2
    have : Nat.card N' = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNK.trans hKMc)).toEquiv
    rw [this, hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup (↥Mc ⧸ N')) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N' hnd, pRank_top_subtype]
    exact hrk
  omega

end CFSG.Quasithin.He8
