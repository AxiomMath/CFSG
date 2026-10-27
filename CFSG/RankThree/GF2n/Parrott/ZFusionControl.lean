module

public import CFSG.RankThree.GF2n.Parrott.Section2Lemma11Prep

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_H_of_mem_normalizer_J (h : Tim79a.ParrottHyp z) {g : G}
    (hg : g ∈ Subgroup.normalizer (J z : Set G)) : g ∈ H z := by
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  have hJ : (J z).map (MulAut.conj g).toMonoidHom = J z :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := J z)).mp hg
  have hmap : ((⁅J z, J z⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom) =
      ⁅J z, J z⁆ := by
    rw [Subgroup.map_commutator, hJ]
  have hcommJ : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
  have hz : z ∈ ⁅J z, J z⁆ := by
    rw [hcommJ]
    exact Subgroup.mem_zpowers z
  have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    have h' : g * z * g⁻¹ ∈ ((⁅J z, J z⁆ : Subgroup G).map
        (MulAut.conj g).toMonoidHom) :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz
    rw [hmap, hcommJ] at h'
    exact h'
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    have hord : orderOf z = 2 := h.1
    rw [h2, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hconj : g * z * g⁻¹ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkmod : k % (↑(2 : ℕ) : ℤ) = 1 := by
      rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
      · exfalso
        apply hne
        have hk0' : k % (↑(2 : ℕ) : ℤ) = 0 := by simpa using hk0
        rw [← hk, ← zpow_mod_orderOf z k, h.1]
        rw [hk0', zpow_zero]
      · simpa using hk1
    have hkz : z ^ k = z := by
      rw [← zpow_mod_orderOf z k, h.1]
      rw [hkmod, zpow_one]
    rw [← hk]
    exact hkz
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hconj]

theorem normalizer_centerIn_le_H (h : Tim79a.ParrottHyp z) :
    Subgroup.normalizer (centerIn (J z) : Set G) ≤ H z := by
  intro g hg
  set C : Subgroup G := Subgroup.centralizer (centerIn (J z) : Set G) with hC
  have hNC : g ∈ Subgroup.normalizer (C : Set G) := by
    have hle : Subgroup.normalizer (centerIn (J z) : Set G) ≤
        Subgroup.normalizer (C : Set G) := by
      rw [hC]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (centerIn (J z) : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (centerIn (J z) : Set G))
    exact hle hg
  have hNJ : g ∈ Subgroup.normalizer (J z : Set G) := by
    have h1 : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) C hNC
    rwa [hC, pCore_centralizer_centerIn_eq (z := z) h] at h1
  exact mem_H_of_mem_normalizer_J (z := z) h hNJ

theorem normalizer_centerIn_eq_H (h : Tim79a.ParrottHyp z) :
    Subgroup.normalizer (centerIn (J z) : Set G) = H z := by
  refine le_antisymm (normalizer_centerIn_le_H (z := z) h) ?_
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
    (centerIn_subgroupOf_normal z)

def NormalizerControlsCenterJFusion (z : G) : Prop :=
  ∀ ⦃a b : G⦄, a ∈ centerIn (J z) → b ∈ centerIn (J z) →
    (∃ g : G, g * a * g⁻¹ = b) →
    ∃ n ∈ Subgroup.normalizer (centerIn (J z) : Set G), n * a * n⁻¹ = b

theorem conj_z_mem_centerIn_eq (h : Tim79a.ParrottHyp z)
    (hF : NormalizerControlsCenterJFusion z) {g : G}
    (hg : g * z * g⁻¹ ∈ centerIn (J z)) : g * z * g⁻¹ = z := by
  have hzA : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  obtain ⟨n, hn, hna⟩ := hF hzA hg ⟨g, rfl⟩
  have hnH : n ∈ H z := by
    rw [← normalizer_centerIn_eq_H (z := z) h]
    exact hn
  have hz_cent : n * z * n⁻¹ = z := by
    have hcomm : n * z = z * n :=
      Subgroup.mem_centralizer_singleton_iff.mp (by
        rwa [H_eq_centralizer] at hnH)
    rw [hcomm, mul_inv_cancel_right]
  rw [← hna]
  exact hz_cent

end CFSG.RankThree.GF2n.Parrott
