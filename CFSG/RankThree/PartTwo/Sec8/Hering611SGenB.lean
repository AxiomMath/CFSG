module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

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

theorem exists_mul_mem_normalizer {B N : Subgroup G} (hB : IsPGroup 3 B)
    (hN3 : ¬ 3 ∣ Nat.card N) (hBN : B ≤ Subgroup.normalizer (N : Set G)) {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hyB : ∀ b ∈ B, y * b * y⁻¹ ∈ B ⊔ N) :
    ∃ n ∈ N, y * n ∈ Subgroup.normalizer (B : Set G) := by
  have hdisj : Disjoint N B := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxB
    have hS : IsPGroup 3 (N ⊓ B : Subgroup G) := hB.to_le inf_le_right
    have h1 : Nat.card (N ⊓ B : Subgroup G) = 1 := by
      rcases hS.card_eq_or_dvd with h | h
      · exact h
      · exact absurd (h.trans (Subgroup.card_dvd_of_le inf_le_left)) hN3
    have hx : x ∈ (N ⊓ B : Subgroup G) := ⟨hxN, hxB⟩
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hx
    exact hx
  set X : Subgroup G := N ⊔ B with hXdef
  have hXcard : Nat.card X = Nat.card N * Nat.card B :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N B hBN hdisj
  have hBX : B ≤ X := le_sup_right
  have hidx : ∀ S : Subgroup G, S ≤ X → Nat.card S = Nat.card B →
      ¬ 3 ∣ (S.subgroupOf X).index := by
    intro S hS hcard
    have h1 := (S.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, hcard, hXcard] at h1
    have h2 : (S.subgroupOf X).index = Nat.card N := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥B))
      rw [h1, mul_comm]
    rw [h2]
    exact hN3
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  set B' : Subgroup G := B.map (MulAut.conj y).toMonoidHom with hB'
  have hB'p : IsPGroup 3 B' := hB.map (MulAut.conj y).toMonoidHom
  have hcardB' : Nat.card B' = Nat.card B :=
    (Nat.card_congr (Subgroup.equivMapOfInjective B _ hinj).toEquiv).symm
  have hB'X : B' ≤ X := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hXdef, sup_comm]
    exact hyB b hb
  obtain ⟨l, hlX, hl⟩ :=
    exists_conj_mem_of_isSylow hBX hB'X hB hB'p (hidx B hBX rfl) (hidx B' hB'X hcardB')
  have hlmem : l ∈ (N : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N B hBN]
    exact hlX
  obtain ⟨n₀, hn₀, b₀, hb₀, hl0⟩ := Set.mem_mul.mp hlmem
  have hyN' : ∀ s : G, s ∈ N ↔ y * s * y⁻¹ ∈ N := fun s => Subgroup.mem_normalizer_iff.mp hyN s
  refine ⟨y⁻¹ * n₀⁻¹ * y, ?_, ?_⟩
  · have h2 : y * (y⁻¹ * n₀⁻¹ * y) * y⁻¹ ∈ N := by
      rw [show y * (y⁻¹ * n₀⁻¹ * y) * y⁻¹ = n₀⁻¹ by group]
      exact N.inv_mem hn₀
    exact (hyN' _).mpr h2
  · have hyn : y * (y⁻¹ * n₀⁻¹ * y) = n₀⁻¹ * y := by group
    rw [hyn, Subgroup.mem_normalizer_iff]
    intro s
    have key : n₀⁻¹ * y * s * (n₀⁻¹ * y)⁻¹ = b₀ * (l⁻¹ * (y * s * y⁻¹) * l) * b₀⁻¹ := by
      rw [← hl0]
      group
    have hs : l⁻¹ * (y * s * y⁻¹) * l ∈ B ↔ s ∈ B :=
      (hl (y * s * y⁻¹)).symm.trans (Subgroup.mem_map_iff_mem (K := B) hinj (x := s))
    have hconj : ∀ t : G, b₀ * t * b₀⁻¹ ∈ B ↔ t ∈ B := fun t =>
      (B.mul_mem_cancel_right (B.inv_mem hb₀)).trans (B.mul_mem_cancel_left hb₀)
    rw [key]
    exact ((hconj _).trans hs).symm

end CFSG.RankThree.PartTwo.Sec8.Hering611
