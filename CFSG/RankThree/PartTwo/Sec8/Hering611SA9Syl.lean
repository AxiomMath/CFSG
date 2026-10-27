module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

section SylowInSubgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_conj_mem_of_isSylow {X B₁ B₂ : Subgroup G} (hle₁ : B₁ ≤ X)
    (hle₂ : B₂ ≤ X) (hp₁ : IsPGroup 3 B₁) (hp₂ : IsPGroup 3 B₂)
    (hi₁ : ¬ 3 ∣ (B₁.subgroupOf X).index) (hi₂ : ¬ 3 ∣ (B₂.subgroupOf X).index) :
    ∃ l ∈ X, ∀ x : G, x ∈ B₂ ↔ l⁻¹ * x * l ∈ B₁ := by
  have hP₁ : IsPGroup 3 ↥(B₁.subgroupOf X) :=
    hp₁.of_equiv (Subgroup.subgroupOfEquivOfLe hle₁).symm
  have hP₂ : IsPGroup 3 ↥(B₂.subgroupOf X) :=
    hp₂.of_equiv (Subgroup.subgroupOfEquivOfLe hle₂).symm
  let S₁ : Sylow 3 ↥X := hP₁.toSylow hi₁
  let S₂ : Sylow 3 ↥X := hP₂.toSylow hi₂
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥X S₁ S₂
  have key : ∀ z : ↥X, z ∈ (S₂ : Subgroup ↥X) ↔
      ∃ s ∈ (S₁ : Subgroup ↥X), y * s * y⁻¹ = z := by
    intro z
    rw [← hy, Sylow.coe_subgroup_smul]
    exact Iff.rfl
  refine ⟨y, y.2, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (key ⟨x, hle₂ hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    have : s = y⁻¹ * ⟨x, hle₂ hx⟩ * y := by
      rw [← hsx]
      group
    rw [this] at hs
    exact Subgroup.mem_subgroupOf.mp hs
  · intro hx
    have hxX : x ∈ X := by
      have h3 : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem y.2 (hle₁ hx)) (X.inv_mem y.2)
      have : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ = x := by group
      rwa [this] at h3
    have hs : (⟨(y : G)⁻¹ * x * y, hle₁ hx⟩ : ↥X) ∈ (S₁ : Subgroup ↥X) :=
      Subgroup.mem_subgroupOf.mpr hx
    have := (key ⟨x, hxX⟩).mpr ⟨_, hs, Subtype.ext (by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group)⟩
    exact Subgroup.mem_subgroupOf.mp this

private theorem isPGroup_three_of_card_nine {B : Subgroup G} (hB : Nat.card B = 9) :
    IsPGroup 3 B :=
  IsPGroup.iff_card.mpr ⟨2, by simp [hB]⟩

private theorem not_three_dvd_index_of_card {X B : Subgroup G} (hBX : B ≤ X)
    (hB : Nat.card B = 9) (hX : Nat.card X = 360) : ¬ 3 ∣ (B.subgroupOf X).index := by
  have h1 := (B.subgroupOf X).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv, hB, hX] at h1
  omega

end SylowInSubgroup

private theorem mem_zpowers_three {H : Type} [Group H] {g x : H} (hord : orderOf g = 3)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g ∨ x = g ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h : g ^ (k % 3) = g ^ k := by
    have h0 := zpow_mod_orderOf g k
    rw [hord] at h0
    simpa using h0
  rw [← h]
  have hm0 : 0 ≤ k % 3 := by omega
  have hm3 : k % 3 < 3 := by omega
  generalize k % 3 = m at hm0 hm3 ⊢
  interval_cases m <;> simp

private theorem a9fT1_cube : a9fT1 ^ 3 = 1 := by
  rw [pow_three]
  decide

private theorem a9fT2_cube : a9fT2 ^ 3 = 1 := by
  rw [pow_three]
  decide

private theorem a9fT1_ne_one : a9fT1 ≠ 1 := by decide

private theorem a9fT2_ne_one : a9fT2 ≠ 1 := by decide

private theorem a9fT2_ne_a9T1 : a9fT2 ≠ a9fT1 := by decide

private theorem a9fT2_ne_sq : a9fT2 ≠ a9fT1 ^ 2 := by
  rw [pow_two]
  decide

private theorem a9fT2_sq_sq : (a9fT2 ^ 2) ^ 2 = a9fT2 := by
  rw [pow_two, pow_two]
  decide

private theorem a9fT1_mul_a9T2 : a9fT1 * a9fT2 = a9fT2 * a9fT1 := by decide

private theorem a9fT1_ord : orderOf a9fT1 = 3 := orderOf_eq_prime a9fT1_cube a9fT1_ne_one

private theorem a9fT2_ord : orderOf a9fT2 = 3 := orderOf_eq_prime a9fT2_cube a9fT2_ne_one

private theorem a9fT1_mem : a9fT1 ∈ a9fAlt6 :=
  (alternatingGroup.mem_range_ofSubtype_iff a9fS a9fT1).mpr (by decide)

private theorem a9fT2_mem : a9fT2 ∈ a9fAlt6 :=
  (alternatingGroup.mem_range_ofSubtype_iff a9fS a9fT2).mpr (by decide)

private theorem a9fE0_le : a9fE0 ≤ a9fAlt6 := by
  unfold a9fE0
  exact sup_le (Subgroup.zpowers_le.mpr a9fT1_mem) (Subgroup.zpowers_le.mpr a9fT2_mem)

private theorem a9fT2_not_mem : a9fT2 ∉ Subgroup.zpowers a9fT1 := by
  intro h
  rcases mem_zpowers_three a9fT1_ord h with h' | h' | h'
  · exact a9fT2_ne_one h'
  · exact a9fT2_ne_a9T1 h'
  · exact a9fT2_ne_sq h'

private theorem a9_disjoint : Disjoint (Subgroup.zpowers a9fT1) (Subgroup.zpowers a9fT2) := by
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  rcases mem_zpowers_three a9fT2_ord hx2 with rfl | rfl | rfl
  · rfl
  · exact absurd hx1 a9fT2_not_mem
  · exfalso
    have h4 := (Subgroup.zpowers a9fT1).pow_mem hx1 2
    rw [a9fT2_sq_sq] at h4
    exact a9fT2_not_mem h4

private theorem a9fT2_le_normalizer :
    Subgroup.zpowers a9fT2 ≤
      Subgroup.normalizer (↑(Subgroup.zpowers a9fT1) : Set (alternatingGroup (Fin 9))) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hh)
  exact ((show Commute a9fT1 a9fT2 from a9fT1_mul_a9T2).zpow_left k).eq

private theorem a9fE0_card : Nat.card a9fE0 = 9 := by
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers a9fT1) (Subgroup.zpowers a9fT2) a9fT2_le_normalizer a9_disjoint
  rw [Nat.card_zpowers, Nat.card_zpowers, a9fT1_ord, a9fT2_ord] at h
  exact h

private theorem card_a9Alt6 : Nat.card a9fAlt6 = 360 := by
  have hinj := alternatingGroup.ofSubtype_injective (s := a9fS)
  have h1 : Nat.card a9fAlt6 = Nat.card (alternatingGroup ↥a9fS) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 : Fintype.card ↥a9fS = 6 := by
    rw [Fintype.card_coe]
    decide
  haveI : Nontrivial ↥a9fS := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [h1, nat_card_alternatingGroup, Nat.card_eq_fintype_card, h2]
  decide

theorem exists_conj_a9E0 {E : Subgroup (alternatingGroup (Fin 9))} (hE9 : Nat.card E = 9)
    (hE : E ≤ a9fAlt6) :
    ∃ g ∈ a9fAlt6, E = a9fE0.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨l, hl, hlE⟩ := exists_conj_mem_of_isSylow a9fE0_le hE
    (isPGroup_three_of_card_nine a9fE0_card) (isPGroup_three_of_card_nine hE9)
    (not_three_dvd_index_of_card a9fE0_le a9fE0_card card_a9Alt6)
    (not_three_dvd_index_of_card hE hE9 card_a9Alt6)
  refine ⟨l, hl, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨l⁻¹ * x * l, (hlE x).mp hx, ?_⟩
    show l * (l⁻¹ * x * l) * l⁻¹ = x
    group
  · rintro ⟨y, hy, rfl⟩
    refine (hlE _).mpr ?_
    show l⁻¹ * (l * y * l⁻¹) * l ∈ a9fE0
    have key : l⁻¹ * (l * y * l⁻¹) * l = y := by group
    rw [key]
    exact hy

end CFSG.RankThree.PartTwo.Sec8.Hering611
