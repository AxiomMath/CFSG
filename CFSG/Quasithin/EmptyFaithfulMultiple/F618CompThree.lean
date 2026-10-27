module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL2

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped commutatorElement

theorem commutatorElement_mul_mul {D : Type*} [Group D] {k₁ k₂ z₁ z₂ : D}
    (h₁₂ : z₁ * k₂ = k₂ * z₁) (h₂₁ : z₂ * k₁ = k₁ * z₂) (hz : z₁ * z₂ = z₂ * z₁) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have e : z₂ * k₁⁻¹ = k₁⁻¹ * z₂ := (show Commute z₂ k₁ from h₂₁).inv_right
  simp only [commutatorElement_def, mul_inv_rev]
  calc k₁ * z₁ * (k₂ * z₂) * (z₁⁻¹ * k₁⁻¹) * (z₂⁻¹ * k₂⁻¹)
      = k₁ * (z₁ * k₂) * z₂ * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by group
    _ = k₁ * k₂ * (z₁ * z₂) * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by rw [h₁₂]; group
    _ = k₁ * k₂ * (z₂ * k₁⁻¹) * z₂⁻¹ * k₂⁻¹ := by rw [hz]; group
    _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by rw [e]; group

theorem commutator_sup_eq {D : Type*} [Group D] {K Z : Subgroup D} [Group.IsPerfect ↥K]
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) :
    ⁅K ⊔ Z, K ⊔ Z⁆ = K := by
  apply le_antisymm
  · have hZN : Z ≤ Subgroup.normalizer (K : Set D) := fun z hz =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm k hk z hz)
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K Z hZN] at hg₁ hg₂
    obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := hg₁
    obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := hg₂
    rw [commutatorElement_mul_mul (hcomm k₂ hk₂ z₁ hz₁).symm (hcomm k₁ hk₁ z₂ hz₂).symm
      (hZ z₁ hz₁ z₂ hz₂)]
    exact Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator hk₁ hk₂)
  · calc K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅K ⊔ Z, K ⊔ Z⁆ := Subgroup.commutator_mono le_sup_left le_sup_left

variable {D : Type} [Group D] [Finite D]

theorem odd_card_of_inf_eq_bot {T C : Subgroup D} (hT : ∃ S : Sylow 2 D, (S : Subgroup D) = T)
    [C.Normal] (hTC : T ⊓ C = ⊥) : Odd (Nat.card ↥C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  have hS : IsSylowIn 2 (S : Subgroup D) ⊤ :=
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have h := (F6.isSylowIn_inf_of_isSubnormal (F6.isSubnormal_top_of_normal (X := C)) hS).2.2
  rw [hTC, Subgroup.relIndex_bot_left] at h
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)

theorem socle_of_caseThree {H₁ H₂ : Subgroup D}
    (hT : ∃ S : Sylow 2 D, (S : Subgroup D) = H₁ ⊓ H₂) (h : F6.IsF618CaseThree H₁ H₂) :
    Socle D := by
  obtain ⟨p, K, Z, hp, hp24, hK, hZ3, hKZ, -, hcomm, -, -, -, hout⟩ := h
  have hp2 : p ≠ 2 := by omega
  have h11 : 11 ≤ p := by omega
  obtain ⟨hs, hnab, hcard⟩ := isL2_facts hK hp2 (by rw [pow_one]; omega)
  rw [pow_one] at hcard
  have : Group.IsPerfect ↥K := F6.isPerfect_of_isSimpleGroup hnab
  have hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic ↥Z := isCyclic_of_prime_card hZ3
    intro z hz z' hz'
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := ↥Z)).is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩)
  have hKn : K.Normal := by
    have := F6.twoResidual_top_normal (D := D)
    rw [← commutator_sup_eq hcomm hZ, hKZ]
    exact Subgroup.commutator_normal _ _
  have hTC : H₁ ⊓ H₂ ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.mp ht
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_centralizer_iff] at htC
    by_cases htK : t ∈ K
    · have hc : (⟨t, htK⟩ : ↥K) ∈ Subgroup.center ↥K :=
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (htC g g.2)
      rw [center_eq_bot_of_isSimpleGroup hnab, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    · exfalso
      obtain ⟨y, hyK, hne⟩ := (hout t htT htK).1.2 1 K.one_mem
      apply hne
      rw [← htC y hyK]
      group
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (K : Set D))) :=
    odd_card_of_inf_eq_bot hT hTC
  refine Or.inr ⟨K, hKn, isQuasisimple_of_isSimpleGroup hnab, hCodd,
    notSL2_of_card_psl2_mod_eight hcard (by omega) h11, ?_⟩
  rintro ⟨f⟩
  exfalso
  have h1 := Nat.card_congr f.toEquiv
  rw [hcard, card_alternating_six] at h1
  have := le_psl2_card h11
  omega

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
