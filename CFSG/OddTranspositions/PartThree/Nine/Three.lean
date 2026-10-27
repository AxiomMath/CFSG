module

public import CFSG.OddTranspositions.PartThree.Nine.ThreeOdd
public import CFSG.OddTranspositions.PartThree.Nine.ThreeTwo
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}


theorem lemma9_3 : Lemma9_3 := by
  intro G _ _ D hC hH hs
  obtain ⟨-, hcard, hsup, hdisj⟩ := Halpha_pCore_split hC hH
  set P := (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hPdef
  have hPne : P ≠ ⊥ := by
    intro hP
    refine false_of_pCore_eq_bot hC hH hs ?_
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Halpha D hC.alpha).subtype_injective).mp hP
  obtain ⟨⟨z, hzP⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzpow : Subgroup.zpowers z ≤ P := (Subgroup.zpowers_le).mpr hzP
  have hord : 2 ≤ orderOf z := by
    have hpos := orderOf_pos z
    have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    omega
  have hPz : P = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge hzpow ?_).symm
    rw [Nat.card_zpowers]
    omega
  have hz2 : z * z = 1 := by
    have hdvd : orderOf z ∣ 2 := by
      have h := orderOf_dvd_natCard (⟨z, hzP⟩ : P)
      rw [Subgroup.orderOf_mk] at h
      have hcard2 : Nat.card P = 2 := by
        have := Subgroup.card_le_of_le hzpow
        rw [Nat.card_zpowers] at this
        omega
      rwa [hcard2] at h
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hzα : z ∈ hC.alpha := mem_alpha_of_pCore hC hH hs hPz hz1
  have hα : hC.alpha = {z} := by
    ext a
    constructor
    · intro ha
      have hzD := hC.isBlock_alpha.subset hzα
      have haD := hC.isBlock_alpha.subset ha
      obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hzD haD)
      have hgN := mem_normalizer_block_of_conj_mem hC (mem_blockClass_self _) hzα (hg ▸ ha)
      have hgP := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
        (normalizer_le_normalizer_Halpha hC.setup.normal hgN)
      have hgz : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
        rw [← hPz]
        exact (hgP z).mp hzP
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgz
      have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
      have hcases : z ^ n = 1 ∨ z ^ n = z := by
        rw [zpow_eq_zpow_emod' n hz2']
        rcases Int.emod_two_eq_zero_or_one n with h | h
        · left
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
        · right
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rcases hcases with h | h
      · exfalso
        rw [h] at hn
        exact hC.setup.oddT.ne_one haD (by rw [← hg, ← hn])
      · rw [Set.mem_singleton_iff, ← hg, ← hn, h]
    · rintro rfl
      exact hzα
  have hu : hC.d = z := by
    have := hC.d_mem_alpha
    rwa [hα, Set.mem_singleton_iff] at this
  refine ⟨by rw [hα, hu], ?_, ?_, ?_⟩
  · rw [hu, ← hPz]
  · rw [hu, ← hPz]
    exact hsup
  · rw [hu, ← hPz]
    exact hdisj

end CFSG.OddTranspositions.PartThree.Nine
