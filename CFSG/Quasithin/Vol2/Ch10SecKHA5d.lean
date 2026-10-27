module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def NoSL25In (X : Type) [Group X] [Finite X] : Prop :=
  ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
    T ≤ Subgroup.normalizer (B : Set X) → ¬ IsSL25Group ↥B

theorem sl25_sup_data {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hD : IsSL25Group ↥B)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    ∃ j : ℕ, Nat.card ↥T = 2 ^ (7 + j) ∧ Nat.card ↥(B ⊔ T) = 2 ^ j * 1920 ∧
      (B.subgroupOf (B ⊔ T)).Normal ∧
      Nat.card (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) = 2 ^ j := by
  classical
  have h1920 : Nat.card ↥B = 1920 := hD.card
  set Y : Subgroup X := B ⊔ T with hY
  have hBY : B ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (B : Set X) := sup_le Subgroup.le_normalizer hTB
  set N : Subgroup ↥Y := B.subgroupOf Y with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYN
  have hTp : IsPGroup 2 ↥(T.subgroupOf Y) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hsup : N ⊔ T.subgroupOf Y = ⊤ := by
    rw [hN, ← Subgroup.subgroupOf_sup hBY hTY, ← hY, Subgroup.subgroupOf_self]
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (T.subgroupOf Y).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : (N ⊔ T.subgroupOf Y).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hsup]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hQp : IsPGroup 2 (↥Y ⧸ N) := IsPGroup.of_surjective (hTp) _ hsurj
  obtain ⟨j, hj⟩ := hQp.exists_card_eq
  have hNcard : Nat.card N = 1920 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, h1920]
  have hYcard : Nat.card ↥Y = 2 ^ j * 1920 := by
    rw [← hj, ← hNcard]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N)
  have ht2Y : Nat.card ↥T ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hTY
  obtain ⟨s, hs⟩ := hT.2.1.exists_card_eq
  have hid : 2 ^ j * 1920 = 2 ^ (7 + j) * 15 := by rw [pow_add]; ring
  have hsj : s = 7 + j := by
    have h1 : 2 ^ s ∣ 2 ^ (7 + j) * 15 := by
      rw [← hs, ← hid, ← hYcard]
      exact ht2Y
    have h2 : 2 ^ s ∣ 2 ^ (7 + j) :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left s (by norm_num : Nat.Coprime 2 15))
        h1
    have h3 : s ≤ 7 + j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    have h4 : 2 ^ (7 + j) ∣ Nat.card X := by
      have h5 : 2 ^ (7 + j) ∣ Nat.card ↥Y := by
        rw [hYcard, show 2 ^ (7 + j) = 2 ^ j * 128 by rw [pow_add]; ring]
        exact mul_dvd_mul_left _ (by norm_num)
      exact h5.trans (Subgroup.card_subgroup_dvd_card Y)
    have hidx : Nat.card X = Nat.card ↥T * T.index := (Subgroup.card_mul_index T).symm
    have hodd : ¬ 2 ∣ T.index := by
      have h1 : (T.subgroupOf (⊤ : Subgroup X)).index = T.index := Subgroup.relIndex_top_right T
      have := hT.2.2
      rwa [h1] at this
    have hcop : Nat.Coprime (2 ^ (7 + j)) T.index :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have h6 : 2 ^ (7 + j) ∣ 2 ^ s := by
      rw [hidx, hs] at h4
      exact hcop.dvd_of_dvd_mul_right h4
    have h7 : 7 + j ≤ s := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h6
    omega
  refine ⟨j, by rw [hs, hsj], hYcard, hNn, ?_⟩
  rw [← hj]

theorem noSL25In_of_card_lt {X : Type} [Group X] [Finite X]
    (h : ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E < 32) : NoSL25In X := by
  intro T hT B hB hne hTB hD
  have hE : IsElemAbelian 2 ((CFSG.pCore 2 ↥B).map B.subtype) :=
    Lin2.isElemAbelian_map' hD.isElemAbelian_pCore B.subtype
  have hcard : Nat.card ((CFSG.pCore 2 ↥B).map B.subtype) = 32 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hD.card_pCore
  have := h _ hE
  omega

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
