module

import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G]

@[expose] def UniqueTwoLocal (M X : Subgroup G) : Prop :=
  ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → X ≤ H → H ≤ M

@[expose] def IsCalH (M Y H : Subgroup G) : Prop :=
  Y ≤ H ∧ ¬ H ≤ M ∧ CFSG.Open.pCoreOf 2 H ≠ ⊥

variable [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] def KyInEta : Prop :=
  ∀ R : Subgroup G, R ≤ c.S.M → IsPGroup 2 R → t.Ky ≤ Subgroup.normalizer (R : Set G) →
    c.L ⊓ t.d.N ≤ R → UniqueTwoLocal c.S.M (c.S.M ⊓ Subgroup.normalizer (R : Set G))

@[expose] def IsMu (Y : Subgroup G) : Prop :=
  Y ≤ c.S.M ∧ Y = t.Ky ⊔ CFSG.Open.pCoreOf 2 Y ∧ CFSG.Open.pCoreOf 2 Y ≠ ⊥ ∧
    ¬ UniqueTwoLocal c.S.M Y

@[expose] def IsMuStar (Y : Subgroup G) : Prop :=
  t.IsMu Y ∧ ∀ Y' : Subgroup G, t.IsMu Y' → Y ≤ Y' → Y' = Y

@[expose] noncomputable def Dn (N : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure ((t.Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype

@[expose] noncomputable def On (N : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore 3 ↥(t.Dn N)).map (t.Dn N).subtype

abbrev Dhat (N : Subgroup G) : Type := ↥(t.Dn N) ⧸ CFSG.pPrimeCore 3 ↥(t.Dn N)

theorem Dn_le (N : Subgroup G) : t.Dn N ≤ N := Subgroup.map_subtype_le _

theorem On_le_Dn (N : Subgroup G) : t.On N ≤ t.Dn N := Subgroup.map_subtype_le _

theorem Z_le_Dn {N : Subgroup G} (hZN : t.Z ≤ N) : t.Z ≤ t.Dn N := by
  intro x hx
  exact ⟨⟨x, hZN hx⟩, Subgroup.subset_normalClosure hx, rfl⟩

theorem normal_Dn (N : Subgroup G) : ((t.Dn N).subgroupOf N).Normal := by
  rw [Dn, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  exact Subgroup.normalClosure_normal

theorem le_normalizer_Dn (N : Subgroup G) : N ≤ Subgroup.normalizer (t.Dn N : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxN : x ∈ N := t.Dn_le N hx
    have h := (t.normal_Dn N).conj_mem ⟨x, hxN⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨n, hn⟩
    exact Subgroup.mem_subgroupOf.mp h
  · intro hx
    have hxN : n * x * n⁻¹ ∈ N := t.Dn_le N hx
    have hx' : x ∈ N := by
      have h : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [h]
      exact N.mul_mem (N.mul_mem (N.inv_mem hn) hxN) hn
    have h := (t.normal_Dn N).conj_mem ⟨n * x * n⁻¹, hxN⟩ (Subgroup.mem_subgroupOf.mpr hx)
      ⟨n⁻¹, N.inv_mem hn⟩
    have h' := Subgroup.mem_subgroupOf.mp h
    simpa [mul_assoc] using h'

theorem inf_N_isPGroup : IsPGroup 2 ((c.L ⊓ t.d.N : Subgroup G)) :=
  (SylowThreeData.N_isPGroup t.d).to_le inf_le_right

theorem Z_inf_N_eq_bot : t.Z ⊓ t.d.N = ⊥ := by
  have hZL : t.Z ≤ c.L := (t.Z_le_AA.trans t.d.AA_le_S).trans (t.hdS ▸ inf_le_right)
  have h2 : IsPGroup 2 ↥(t.Z ⊓ t.d.N) :=
    (inf_N_isPGroup t).to_le (le_inf (inf_le_left.trans hZL) inf_le_right)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdiv : 2 ^ n ∣ 3 := by
    rw [← hn, ← t.card_Z]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hn0 : n = 0 := by
    by_contra hne
    exact absurd ((dvd_pow_self 2 hne).trans hdiv) (by norm_num)
  have hcard : Nat.card ↥(t.Z ⊓ t.d.N) = 1 := by rw [hn, hn0, pow_zero]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem not_three_dvd_card_On (N : Subgroup G) : ¬ 3 ∣ Nat.card (t.On N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  change ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 ↥(t.Dn N)).map (t.Dn N).subtype)
  rw [Subgroup.card_map_of_injective (t.Dn N).subtype_injective]
  exact (Nat.prime_three.coprime_iff_not_dvd).1
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(t.Dn N)))

theorem not_Z_le_On {N : Subgroup G} : ¬ t.Z ≤ t.On N := by
  intro hle
  have h3 : 3 ∣ Nat.card (t.On N) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [t.card_Z] at h
  exact t.not_three_dvd_card_On N h3

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
