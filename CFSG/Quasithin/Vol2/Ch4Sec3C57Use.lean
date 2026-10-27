module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isPerfect_of_card_eq_six {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

omit [Finite G] in
theorem one_lt_of_isLin2Type {L : Subgroup G} (hL : IsShort2 L) {n : ℕ} (h : IsLin2Type L n) :
    1 < n := by
  obtain ⟨F, _, _, hF, α, hα, hαk, -⟩ := h
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  by_contra hn
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · rw [hF, pow_zero] at hq; omega
    · rfl
    · omega
  subst hn1
  have hF2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF, pow_one]
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6 := by
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF2]
    norm_num
  rcases hL.2.2.2.1 with hqs | h3
  · exact not_isPerfect_of_card_eq_six hcard hqs.1
  · omega

omit [Finite G] in
theorem isChi0Block_of {X L : Subgroup G} (hL : IsBlock2 X L)
    (ht : (∃ n : ℕ, IsLin2Type L n) ∨ IsAltType L 3 ∨ IsAltType L 5) : IsChi0Block X L := by
  refine ⟨hL, ?_⟩
  rcases ht with ⟨n, hn⟩ | h3 | h5
  · exact Or.inl ⟨n, one_lt_of_isLin2Type hL.1 hn, hn⟩
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h5)

theorem relIndex_eq_two_of_block {H M₀ R L : Subgroup G} (hHL : H = L ⊔ R)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hL : IsBlock2 H L)
    (ht : (∃ n : ℕ, IsLin2Type L n) ∨ IsAltType L 3 ∨ IsAltType L 5)
    (hsyl : IsSylowTwoOf R H) (hc : CharTwo H) (hum : ∃ N : Subgroup G, IsUniqueMaxOver H R N)
    (hRM : R ≤ M₀) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set G)) (hC : C5.NoCommonNormal R H M₀)
    (hJ : ⁅L, thompsonJ R⁆ = L)
    (hmax : IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (L : Set G))) :
    (M₀ ⊓ Subgroup.normalizer (L : Set G)).relIndex M₀ = 2 :=
  Setup.lemmaC57
    { sylow := hsyl
      charTwo := hc
      uniqueMax := hum
      R_le := hRM
      normal_R := hM₀R
      noCommon := hC
      block := isChi0Block_of hL ht
      K_eq := by rw [hHL, oTwoUpper_sup_eq_of_short hL.1 hsyl.2.1 hRN]
      thompson := hJ
      maxN := hmax }

end CFSG.Quasithin.H13.Ch4.C57
