module

public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.GroupTheory.ParityTransfer
public import CFSG.GroupTheory.SylowOfFusionTrivialCenter
public import CFSG.GroupTheory.Commutator.RelIndexLeFour
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_index_two_inf_eq_commutator_of_lift_of_not_isConj (h : Tim79a.ParrottHypA z)
    (hidx : ⁅H z, H z⁆.relIndex (H z) = 2)
    {x : G} (hxH : x ∈ H z) (hxH' : x ∉ ⁅H z, H z⁆) (hxx : x * x ∈ zpowers z)
    (hZY : ∀ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) →
      ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j)
    (hzsq : x * x = z → ∀ g : G, g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆)
    (hxJ : ∀ j ∈ J z, ¬ IsConj z (x * j)) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := ⁅H z, H z⁆ with hW
  have hWleH : W ≤ H z := by rw [hW]; exact Subgroup.commutator_le_self (H z)
  have hx2 : x ^ 2 = 1 ∨ x ^ 2 = z := by
    have h := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp hxx
    simpa [pow_two] using h
  have hx4 : x ^ 4 = 1 := by
    have h4 : x ^ 4 = (x ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rcases hx2 with h1 | h1
    · rw [h4, h1, one_pow]
    · rw [h4, h1]
      simpa [pow_two] using zpowers_sq_eq_one_A h (Subgroup.mem_zpowers z)
  let xH : ↥(H z) := ⟨x, hxH⟩
  have hxH4 : xH ^ 4 = 1 := by
    apply Subtype.ext
    simpa [xH] using hx4
  have hxp : IsPGroup 2 (Subgroup.zpowers xH) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨2, ?_⟩
    have hg : orderOf g ∣ orderOf xH := by
      have h := orderOf_dvd_of_mem_zpowers g.2
      rwa [Subgroup.orderOf_coe g] at h
    have hxord : orderOf xH ∣ 4 := orderOf_dvd_of_pow_eq_one hxH4
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact hg.trans hxord
  obtain ⟨T₀, hxT₀⟩ := hxp.exists_le_sylow
  let T : Subgroup G := (T₀ : Subgroup ↥(H z)).map (H z).subtype
  have hT : IsSylowOf 2 T (H z) := ⟨T₀, rfl⟩
  have hxT : x ∈ T :=
    Subgroup.mem_map.mpr ⟨xH, hxT₀ (Subgroup.mem_zpowers xH), rfl⟩
  have hJT : J z ≤ T := by
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    have hJQ : (J z).subgroupOf (H z) ≤ (Q : Subgroup ↥(H z)) := by
      rw [J_subgroupOf_eq_pCore]
      exact IsPGroup.le_sylow_of_normal pCore_isPGroup Q
    intro a ha
    have ha' : (⟨a, J_le_H ha⟩ : ↥(H z)) ∈ (Q : Subgroup ↥(H z)) :=
      hJQ (Subgroup.mem_subgroupOf.mpr ha)
    rw [hQ] at ha'
    exact Subgroup.mem_subgroupOf.mp ha'
  have hzT : z ∈ T := hJT (z_mem_J_A h)
  have hTtop : IsSylowOf 2 T ⊤ := by
    refine CFSG.GroupTheory.isSylowOf_of_fusion_trivial_center (p := 2) (z := z) (M := ⊤) (Y := T) ?_ ?_ ?_
    · simpa [H_eq_centralizer] using hT
    · refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z)) t (hT.le ht)
    · intro g hg
      have haT : g * z * g⁻¹ ∈ T := (Subgroup.mem_inf.mp hg).1
      have haC : g * z * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.mp hg).2
      have haH : g * z * g⁻¹ ∈ H z := hT.le haT
      have haJ : g * z * g⁻¹ ∈ Subgroup.centralizer (J z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_iff.mp haC j (hJT hj)
      have haZ : g * z * g⁻¹ ∈ centerIn (J z) := by
        rw [← centralizer_J_eq_centerIn_A h]
        exact Subgroup.mem_inf.mpr ⟨haH, haJ⟩
      rw [centerIn_J_eq_zpowers_A h] at haZ
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp haZ with h1 | h1
      · exfalso
        have hz1 : z = 1 := by
          calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group
        have hzord := orderOf_z_A h
        rw [hz1, orderOf_one] at hzord
        norm_num at hzord
      · exact h1
  have hTidx : ¬ 2 ∣ T.index := by
    have h := (isSylowOf_iff.mp hTtop).2.2
    rwa [Subgroup.relIndex_top_right] at h
  set U : Subgroup G := T ⊓ W with hU
  have hUT : U ≤ T := by rw [hU]; exact inf_le_left
  have hsup : T ⊔ W = H z := by
    have hle : T ⊔ W ≤ H z := sup_le hT.le hWleH
    have hne : T ⊔ W ≠ W := by
      intro heq
      exact hxH' (by rw [← heq]; exact Subgroup.mem_sup_left hxT)
    have e1 : W.relIndex (T ⊔ W) * (T ⊔ W).relIndex (H z) = W.relIndex (H z) :=
      Subgroup.relIndex_mul_relIndex W (T ⊔ W) (H z) le_sup_right hle
    rw [hidx] at e1
    have hdvd : (T ⊔ W).relIndex (H z) ∣ 2 := Dvd.intro_left _ e1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
    · exfalso
      rw [h1] at e1
      have hW1 : W.relIndex (T ⊔ W) = 1 := by omega
      exact hne (le_antisymm le_sup_right (Subgroup.relIndex_eq_one.mp hW1)).symm
  have hUidx : U.relIndex T = 2 := by
    have hnorm : T ≤ Subgroup.normalizer (W : Set G) := by
      rw [hW]
      exact hT.le.trans (Subgroup.normalizer_commutator_ge_left (H₁ := H z) (H₂ := H z))
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := T) (K := W) hnorm).2
    rw [hsup, hidx] at h
    rw [hU]
    exact h.symm
  have hxU : x ∉ U := by
    intro hx
    rw [hU] at hx
    exact hxH' hx.2
  have hsq : ∀ g : G, g⁻¹ * x ^ 2 * g ∈ T → g⁻¹ * x ^ 2 * g ∈ U := by
    intro g hgT
    rw [hU]
    refine Subgroup.mem_inf.mpr ⟨hgT, ?_⟩
    rcases hx2 with h1 | h1
    · rw [h1]
      simp
    · rw [h1] at hgT ⊢
      have hconjH : (g⁻¹) * z * (g⁻¹)⁻¹ ∈ H z := by simpa using hT.le hgT
      have h := hzsq ((sq x).symm.trans h1) g⁻¹ hconjH
      simpa using h
  have hout : ∀ g : G, g * z = z * g → g⁻¹ * x * g ∉ U := by
    intro g hgz hgU
    have hgH : g ∈ H z := by
      rw [H_eq_centralizer]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hgz
    rw [hU] at hgU
    have hnorm : g ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.normalizer_commutator_ge_left (H₁ := H z) (H₂ := H z) hgH
    have hxW : x ∈ W := by
      have h := (Subgroup.mem_normalizer_iff.mp hnorm (g⁻¹ * x * g)).mp hgU.2
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h
    exact hxH' hxW
  obtain ⟨Y, hY⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({x} : Set G))
  have hYzx : Y ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    simpa [H_eq_centralizer] using hY.le
  have hY2 : IsPGroup 2 Y := hY.isPGroup
  have hYmax : ∀ P : Subgroup G,
      P ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) →
      IsPGroup 2 P → Y ≤ P → P = Y := by
    intro P hPle hP hYP
    rw [← H_eq_centralizer] at hPle
    exact hY.eq_of_le hYP hPle hP
  have hzK : z ∈ H z ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨z_mem_H, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_z_sigma_A (x := xH)).eq
  have hzY : z ∈ Y := by
    obtain ⟨Q, hQ⟩ := hY.exists_sylow_eq_subgroupOf
    let zK : ↥(H z ⊓ Subgroup.centralizer ({x} : Set G)) := ⟨z, hzK⟩
    have hgen_center : zK ∈ Subgroup.center ↥(H z ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z)) k.1 k.2.1
    have hZ2 : IsPGroup 2 (Subgroup.zpowers zK) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers]
      have hord : orderOf zK = 2 := by
        rw [← Subgroup.orderOf_coe zK]
        exact orderOf_z_A h
      rw [hord, pow_one]
    have : (Subgroup.zpowers zK).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hgen_center)
    have hZle : Subgroup.zpowers zK ≤
        (Q : Subgroup ↥(H z ⊓ Subgroup.centralizer ({x} : Set G))) :=
      IsPGroup.le_sylow_of_normal hZ2 Q
    have hzQ : zK ∈ (Q : Subgroup ↥(H z ⊓ Subgroup.centralizer ({x} : Set G))) :=
      hZle (Subgroup.mem_zpowers zK)
    have hzsub : zK ∈ Y.subgroupOf (H z ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [← hQ]
      exact hzQ
    simpa using Subgroup.mem_subgroupOf.mp hzsub
  have hR : ∀ a ∈ Y, (∀ y ∈ Y, a * y = y * a) → ∀ g : G, g⁻¹ * z * g = a → a = z := by
    intro a haY haCent g hga
    have ha_mem : a ∈ Y ⊓ Subgroup.centralizer (Y : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨haY, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (haCent y hy).symm
    rcases hZY Y hY a ha_mem with haJ | ⟨j, hjJ, rfl⟩
    · have hconj : IsConj z a := isConj_iff.mpr ⟨g⁻¹, by simpa using hga⟩
      have ha_order : orderOf a = 2 := by
        rw [← IsConj.orderOf_eq hconj]
        exact orderOf_z_A h
      by_cases haz : a ∈ Subgroup.zpowers z
      · rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp haz with h1 | h1
        · exfalso
          have hz1 : z = 1 := by
            calc z = g * a * g⁻¹ := by rw [← hga]; group
              _ = 1 := by rw [h1]; group
          have hzord := orderOf_z_A h
          rw [hz1, orderOf_one] at hzord
          norm_num at hzord
        · exact h1
      · exact absurd hconj (hF1 a haJ ha_order haz)
    · exact absurd (isConj_iff.mpr ⟨g⁻¹, by simpa using hga⟩) (hxJ j hjJ)
  have hzc : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z)) t (hT.le ht)
  obtain ⟨N, hNnorm, hNidx, hxN⟩ :=
    CFSG.ParityTransfer.exists_normal_index_two_not_mem_of_parity'
      hT.isPGroup hTidx hUT hUidx hzT hzc hxT hxU hx4 hsq hout
      hYzx hY2 hYmax hzY hR
  have hWcomm : W ≤ _root_.commutator G := by
    rw [hW, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have : N.Normal := hNnorm
  have hcommGN : _root_.commutator G ≤ N := by
    have h := CFSG.GroupTheory.commutator_le_of_relIndex_le_four (G := G) (N := N) (H := ⊤)
      Subgroup.le_normalizer_of_normal (by rw [Subgroup.relIndex_top_right, hNidx]; norm_num)
    simpa [_root_.commutator_def] using h
  have hzW : z ∈ W := by
    rw [hW]
    exact (Subgroup.commutator_mono (J_le_H (z := z)) (J_le_H (z := z)))
      (by rw [h.commutator]; exact Subgroup.mem_zpowers z)
  have hzN : z ∈ N := hcommGN (hWcomm hzW)
  have hWN : W ≤ N := hWcomm.trans hcommGN
  have hle : W ≤ H z ⊓ N := le_inf hWleH hWN
  have hne : H z ⊓ N ≠ H z := by
    intro heq
    refine hxN ?_
    have hxHN : x ∈ H z ⊓ N := by rw [heq]; exact hxH
    exact hxHN.2
  have hHN : H z ⊓ N = W := by
    have e1 : W.relIndex (H z ⊓ N) * (H z ⊓ N).relIndex (H z) = W.relIndex (H z) :=
      Subgroup.relIndex_mul_relIndex W (H z ⊓ N) (H z) hle inf_le_left
    rw [hidx] at e1
    have hdvd : (H z ⊓ N).relIndex (H z) ∣ 2 := Dvd.intro_left _ e1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h1)) hne
    · rw [h1] at e1
      have hW1 : W.relIndex (H z ⊓ N) = 1 := by omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hW1) hle
  exact ⟨N, hNnorm, hNidx, hzN, by simpa [hW] using hHN⟩

theorem not_mem_commutator_of_qH_not_mem_QP45
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) {x : G} (hxH : x ∈ H z)
    (hq : qH D ⟨x, hxH⟩ ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :
    x ∉ ⁅H z, H z⁆ := by
  intro hxW
  apply hq
  have hxC : (⟨x, hxH⟩ : ↥(H z)) ∈ _root_.commutator ↥(H z) := by
    have hmem : (H z).subtype ⟨x, hxH⟩ ∈
        (_root_.commutator ↥(H z)).map (H z).subtype := by
      rw [Subgroup.map_subtype_commutator]
      simpa using hxW
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyx' : y = ⟨x, hxH⟩ := (H z).subtype_injective hyx
    simpa [hyx'] using hy
  have hqC : qH D ⟨x, hxH⟩ ∈ _root_.commutator ↥QA45.originalSubgroup := by
    have hmem : qH D ⟨x, hxH⟩ ∈ (_root_.commutator ↥(H z)).map (qH D) :=
      Subgroup.mem_map_of_mem (qH D) hxC
    rwa [show (_root_.commutator ↥(H z)).map (qH D) =
        _root_.commutator ↥QA45.originalSubgroup by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (qH_surjective (z := z) D)]] at hmem
  have : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  exact (CFSG.GroupTheory.commutator_le_of_relIndex_le_four (G := ↥QA45.originalSubgroup)
    (N := QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) (H := ⊤)
    Subgroup.le_normalizer_of_normal (by
      rw [Subgroup.relIndex_top_right, index_QP45]
      norm_num)) hqC

end CFSG.RankThree.GF2n.Parrott
