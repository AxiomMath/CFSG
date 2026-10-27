module

public import CFSG.GroupTheory.SylowOfFusionTrivialCenter
public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4
public import CFSG.RankThree.GF2n.Parrott.Section4G0Closure

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem isSylowOf_centralizer_of_fusion_free (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j)
    {x : G} (hxH : x ∈ H z) {Y : Subgroup G}
    (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)))
    (hZs : ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j)
    (hf : ∀ j ∈ J z, orderOf (x * j) = 2 → ¬ IsConj z (x * j)) :
    IsSylowOf 2 Y (centralizer ({x} : Set G)) := by
  have hz2 : orderOf z = 2 := h.1
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.mp hxH
  have hzC : z ∈ H z ⊓ centralizer ({x} : Set G) :=
    mem_inf.mpr ⟨z_mem_H, mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hCN : H z ⊓ centralizer ({x} : Set G) ≤ normalizer (zpowers z : Set G) := by
    intro c hc
    refine centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact (mem_inf.mp hc).1
  have hzN : zpowers z ≤ Y :=
    le_isSylowOf_of_isPGroup_of_le_normalizer hY (zpowers_le.mpr hzC) hCN
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one]))
  have hzY : z ∈ Y ⊓ centralizer (Y : Set G) := by
    refine mem_inf.mpr ⟨hzN (mem_zpowers z), ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((mem_inf.mp (hY.le hy)).1)
  have hfus : ∀ g : G, g * z * g⁻¹ ∈ Y ⊓ centralizer (Y : Set G) → g * z * g⁻¹ = z := by
    intro g hg
    have hconj : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have hw2 : orderOf (g * z * g⁻¹) = 2 := by
      rw [← hz2]
      exact (SemiconjBy.orderOf_eq g (show g * z = (g * z * g⁻¹) * g by group)).symm
    rcases hZs _ hg with hwJ | ⟨j, hjJ, hwj⟩
    · by_contra hne
      have hnz : g * z * g⁻¹ ∉ zpowers z := by
        intro hmem
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
        have hk' : z ^ (k % 2) = z ^ k := by
          have := zpow_mod_orderOf z k
          rwa [hz2] at this
        have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases hmod with h0 | h1
        · have h1' : g * z * g⁻¹ = 1 := by rw [← hk, ← hk', h0]; simp
          rw [h1', orderOf_one] at hw2
          exact absurd hw2 (by norm_num)
        · exact hne (by rw [← hk, ← hk', h1]; simp)
      exact hJ _ hwJ hnz hconj
    · rw [hwj] at hconj hw2
      exact absurd hconj (hf j hjJ hw2)
  exact isSylowOf_of_fusion_trivial_center hY hzY hfus

theorem exists_sylow_centralizer_of_fusion_free (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j)
    {x : G} (hxH : x ∈ H z)
    (hZs : ∀ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) →
      ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j)
    (hf : ∀ j ∈ J z, orderOf (x * j) = 2 → ¬ IsConj z (x * j)) :
    ∃ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) ∧
      IsSylowOf 2 Y (centralizer ({x} : Set G)) := by
  obtain ⟨Y, hY⟩ := exists_isSylowOf 2 (H z ⊓ centralizer ({x} : Set G))
  exact ⟨Y, hY, isSylowOf_centralizer_of_fusion_free h hJ hxH hY (hZs Y hY) hf⟩

section Certified


theorem parrott_theorem4_of_sylow_centralizer (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hNF : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y)
    (hB2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) ∧
          (∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀)
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hS : ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∃ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) ∧
        IsSylowOf 2 Y (centralizer ({x} : Set G)))
    (hB5 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
        (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
        ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
          (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
          ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥G₁ ≃* X)) :
    Tim79a.ParrottCaseII z := by
  obtain ⟨z₁₀, hZeq, hz₁₀z, hz₁₀2⟩ := exists_z1 h
  have hz₁₀ : z₁₀ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁₀)
  have hNF' : (∀ g : G, (g ∈ centralizer ({z₁₀} : Set G) ∨ g ∈ centralizer ({z * z₁₀} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y := by
    intro hA
    apply hNF
    rintro g ⟨e, he, he1, hez, hge⟩ hgH
    rcases (mem_centerIn_J_iff h hz₁₀ hz₁₀z hz₁₀2).mp he with h1 | h1 | h1 | h1
    · exact absurd h1 he1
    · exact absurd h1 hez
    · rw [h1] at hge
      exact hA g (Or.inl hge) hgH
    · rw [h1] at hge
      exact hA g (Or.inr hge) hgH
  obtain ⟨g, hg, hgH, hgz⟩ := lemma42_of_noFusion h hZ hne hz₁₀ hz₁₀z hz₁₀2 hNF'
  have hgz' : g * z * g⁻¹ ≠ z := fun h1 => hgz (by rw [h1]; exact Subgroup.mem_zpowers z)
  obtain ⟨z₁, hz₁, hz₁z, hz₁2, hfuse⟩ : ∃ z₁ : G, z₁ ∈ centerIn (J z) ∧
      z₁ ∉ Subgroup.zpowers z ∧ orderOf z₁ = 2 ∧
      ∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z := by
    rcases hg with hg | hg
    · exact ⟨z₁₀, hz₁₀, hz₁₀z, hz₁₀2, g, hg, hgH, hgz'⟩
    · obtain ⟨h1, h2, h3⟩ := exists_z1_mul h hz₁₀ hz₁₀z hz₁₀2
      exact ⟨z * z₁₀, h1, h2, h3, g, hg, hgH, hgz'⟩
  obtain ⟨U, hUC, hUi, hJU, hUq, E, hE, hEU, hQ, hweak, hconjE, -⟩ :=
    hB2 z₁ hz₁ hz₁z hz₁2 hfuse
  have hG₀ := exists_index_two_not_le_H_of_sylow_centralizer h hZ hH' hE hJN hweak hconjE hS
  exact parrott_theorem4 h hZ hne hNF hB2 hB3 hB6 hH' hG₀ hB5

end Certified

end CFSG.RankThree.GF2n.Parrott
