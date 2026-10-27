module

public import CFSG.OddTranspositions.SixNineUnconditional

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem centralizer_eq_of_mul_mem (hS : Setup G D) {v y : G} (hv : v ∈ D) (hy : y ∈ D)
    (hne : v ≠ y) (hc : Commute v y) (hvy : v * y ∈ D) :
    D ∩ Subgroup.centralizer ({v} : Set G) = D ∩ Subgroup.centralizer ({y} : Set G) ∧
    D ∩ Subgroup.centralizer ({v * y} : Set G) =
      D ∩ Subgroup.centralizer ({v} : Set G) := by
  classical
  have h1 : ∀ x ∈ D, (Commute x v ↔ Commute x (v * y)) :=
    fun x hx => OddTransp.commute_iff_mul_of_mem hS hv hy hne hc hvy hx
  have hyvD : y * v ∈ D := hc.eq ▸ hvy
  have h2 : ∀ x ∈ D, (Commute x y ↔ Commute x (y * v)) :=
    fun x hx => OddTransp.commute_iff_mul_of_mem hS hy hv hne.symm hc.symm hyvD hx
  have h2' : ∀ x ∈ D, (Commute x y ↔ Commute x (v * y)) :=
    fun x hx => hc.eq.symm ▸ h2 x hx
  constructor
  · ext x
    constructor
    · rintro ⟨hxD, hx⟩
      have hxv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hxvy : Commute x (v * y) := (h1 x hxD).mp hxv
      exact ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr ((h2' x hxD).mpr hxvy)⟩
    · rintro ⟨hxD, hx⟩
      have hxy : Commute x y := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hxvy : Commute x (v * y) := (h2' x hxD).mp hxy
      exact ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr ((h1 x hxD).mpr hxvy)⟩
  · ext x
    constructor
    · rintro ⟨hxD, hx⟩
      have hxvy : Commute x (v * y) := Subgroup.mem_centralizer_singleton_iff.mp hx
      exact ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr ((h1 x hxD).mpr hxvy)⟩
    · rintro ⟨hxD, hx⟩
      have hxv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hx
      exact ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr ((h1 x hxD).mp hxv)⟩

theorem commute_DalphaStar_of_mul_mem (hC : HypothesisC D)
    (hH : ∀ x w y : G, x ∈ DalphaStar D hC.alpha → w ∈ DalphaStar D hC.alpha →
      y ∈ DalphaStar D hC.alpha → IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)))
    (hB : ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ Commute x y ∧ x * y ∈ D) :
    ∀ v ∈ DalphaStar D hC.alpha, ∀ d ∈ DalphaStar D hC.alpha, Commute v d := by
  classical
  intro v hvStar d hdStar
  have hvD : v ∈ D := DalphaStar_subset hC.isBlock_alpha hvStar
  have hdD : d ∈ D := DalphaStar_subset hC.isBlock_alpha hdStar
  obtain ⟨x, hxD, y, hyD, hne, hcomm, hxyD⟩ := hB
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hxD hvD)
  let y' : G := g * y * g⁻¹
  have hy'D : y' ∈ D := hC.setup.normal g y hyD
  have hcomm' : Commute v y' := by
    have h := hcomm.conj g
    rw [hg] at h
    exact h
  have hvy'D : v * y' ∈ D := by
    have h := hC.setup.normal g (x * y) hxyD
    rw [show g * (x * y) * g⁻¹ = v * y' by
      dsimp only [y']
      rw [← hg]
      group] at h
    exact h
  have hne' : v ≠ y' := by
    intro h
    have hv2 : v * v = 1 := hC.setup.oddT.mul_self_eq_one hvD
    have hmem1 : (1 : G) ∈ D := by
      rw [← h] at hvy'D
      rw [hv2] at hvy'D
      exact hvy'D
    exact hC.setup.oddT.ne_one hmem1 rfl
  have hcent := centralizer_eq_of_mul_mem hC.setup hvD hy'D hne' hcomm' hvy'D
  obtain ⟨hcent1, hcent2⟩ := hcent
  have hy'α : ∀ a ∈ hC.alpha, Commute y' a := by
    intro a ha
    have haD : a ∈ D := hC.isBlock_alpha.subset ha
    obtain ⟨β, hβ, hvβ⟩ := mem_DalphaStar_iff.mp hvStar
    have hva : Commute a v := (mem_Dalpha_iff.mp hβ).2.2.2 a ha v hvβ
    have haCv : a ∈ D ∩ Subgroup.centralizer ({v} : Set G) :=
      ⟨haD, Subgroup.mem_centralizer_singleton_iff.mpr hva⟩
    have haCy : a ∈ D ∩ Subgroup.centralizer ({y'} : Set G) := by
      rwa [hcent1] at haCv
    exact (Subgroup.mem_centralizer_singleton_iff.mp haCy.2).symm
  by_cases hyα : y' ∈ hC.alpha
  ·
    obtain ⟨β, hβ, hdβ⟩ := mem_DalphaStar_iff.mp hdStar
    have hdy : Commute d y' := ((mem_Dalpha_iff.mp hβ).2.2.2 y' hyα d hdβ).symm
    have hdCy : d ∈ D ∩ Subgroup.centralizer ({y'} : Set G) :=
      ⟨hdD, Subgroup.mem_centralizer_singleton_iff.mpr hdy⟩
    have hdCv : d ∈ D ∩ Subgroup.centralizer ({v} : Set G) := by
      rwa [← hcent1] at hdCy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hdCv.2).symm
  ·
    obtain ⟨β, hβclass, hy'β⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hy'D
    have hβα : β ≠ hC.alpha := fun h => hyα (h ▸ hy'β)
    have hβD : β ⊆ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβclass
    have hβDalpha : β ∈ Dalpha D hC.alpha := by
      rw [mem_Dalpha_iff]
      refine ⟨hβclass, hβD, hβα, ?_⟩
      intro a ha b hb
      obtain ⟨k, hk⟩ := mem_blockClass_iff'.mp hβclass
      have hneβ : k • hC.alpha ≠ hC.alpha := by rwa [hk] at hβα
      exact (commute_block_of_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hneβ
        ha (show y' ∈ k • hC.alpha from by rw [← hk]; exact hy'β)
        (hy'α a ha).symm) a ha b (show b ∈ k • hC.alpha from by rw [← hk]; exact hb)
    have hy'Star : y' ∈ DalphaStar D hC.alpha := ⟨β, hβDalpha, hy'β⟩
    by_contra hvd
    have hnotdvy : ¬ Commute d (v * y') := by
      intro h
      have hdCvy : d ∈ D ∩ Subgroup.centralizer ({v * y'} : Set G) :=
        ⟨hdD, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
      have hdCv : d ∈ D ∩ Subgroup.centralizer ({v} : Set G) := by
        rwa [hcent2] at hdCvy
      exact hvd (Subgroup.mem_centralizer_singleton_iff.mp hdCv.2).symm
    have hdy : ¬ Commute y' d := by
      intro h
      have hdCy : d ∈ D ∩ Subgroup.centralizer ({y'} : Set G) :=
        ⟨hdD, Subgroup.mem_centralizer_singleton_iff.mpr h.symm⟩
      have hdCv : d ∈ D ∩ Subgroup.centralizer ({v} : Set G) := by
        rwa [← hcent1] at hdCy
      exact hvd (Subgroup.mem_centralizer_singleton_iff.mp hdCv.2).symm
    have htri : IsTriangle D v d y' :=
      ⟨hvD, hy'D, hdD, hne', hcomm', hvd, hdy⟩
    have hodd : Odd (orderOf (v * y' * d)) :=
      hC.setup.oddT.odd_of_not_commute hvy'D hdD (fun h => hnotdvy h.symm)
    have hgt : 1 < orderOf (v * y' * d) := by
      by_contra hle
      rw [Nat.not_lt] at hle
      have hpos : 0 < orderOf (v * y' * d) := orderOf_pos _
      have h1 : orderOf (v * y' * d) = 1 := by omega
      rw [orderOf_eq_one_iff] at h1
      have hd_eq : d = v * y' := by
        calc d = (v * y')⁻¹ * (v * y' * d) := by group
          _ = (v * y')⁻¹ * 1 := by rw [h1]
          _ = v * y' := by rw [hC.setup.oddT.inv_eq hvy'D, mul_one]
      exact hnotdvy (hd_eq.symm ▸ Commute.refl (v * y'))
    exact hH v d y' hvStar hdStar hy'Star htri ⟨hodd, hgt⟩

theorem Valpha_ne_singleton_of_commute_DalphaStar (hC : HypothesisC D)
    (hcomm : ∀ v ∈ DalphaStar D hC.alpha, ∀ d ∈ DalphaStar D hC.alpha, Commute v d) :
    Valpha D hC.alpha ≠ {hC.alpha} := by
  classical
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  have hβα : β ≠ hC.alpha := hβ.2.2.1
  have hβclass : β ∈ blockClass hC.alpha := hβ.1
  have hβblock : IsBlock D β :=
    isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβclass
  obtain ⟨v, hvβ⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hβclass
  have hvD : v ∈ D := hβ.2.1 hvβ
  have hvStar : v ∈ DalphaStar D hC.alpha := ⟨β, hβ, hvβ⟩
  have hαDβ : hC.alpha ∈ Dalpha D β := by
    rw [mem_Dalpha_iff]
    refine ⟨mem_blockClass_of_mem_blockClass hβclass (mem_blockClass_self _),
      hC.isBlock_alpha.subset, hβα.symm, ?_⟩
    intro a ha b hb
    exact ((mem_Dalpha_iff.mp hβ).2.2.2 b hb a ha).symm
  have hDαDβ : ∀ δ ∈ Dalpha D hC.alpha, δ ≠ β → δ ∈ Dalpha D β := by
    intro δ hδ hδβ
    have hδclass : δ ∈ blockClass hC.alpha := hδ.1
    have hδblockClassβ : δ ∈ blockClass β :=
      mem_blockClass_of_mem_blockClass hβclass hδclass
    obtain ⟨k, hk⟩ := mem_blockClass_iff'.mp hδblockClassβ
    have hkne : k • β ≠ β := by rwa [hk] at hδβ
    rw [mem_Dalpha_iff]
    refine ⟨hδblockClassβ, subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hδclass,
      hδβ, ?_⟩
    intro a ha b hb
    have hbStar : b ∈ DalphaStar D hC.alpha := ⟨δ, hδ, hb⟩
    exact (commute_block_of_mem hC.setup.normal hC.setup.oddT hβblock hkne
      hvβ (show b ∈ k • β from by rw [← hk]; exact hb)
      (hcomm v hvStar b hbStar)) a ha b (show b ∈ k • β from by rw [← hk]; exact hb)
  have hsub : perp D hC.alpha ⊆ perp D β := by
    intro γ hγ
    rcases mem_perp_iff.mp hγ with hγD | rfl
    · by_cases hγβ : γ = β
      · exact mem_perp_iff.mpr (Or.inr hγβ)
      · exact mem_perp_iff.mpr (Or.inl (hDαDβ γ hγD hγβ))
    · exact mem_perp_iff.mpr (Or.inl hαDβ)
  have hcard : (perp D β).ncard = (perp D hC.alpha).ncard := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff'.mp hβclass
    rw [hg]
    exact ncard_perp_conj hC.setup.normal g hC.alpha
  have hperpeq : perp D β = perp D hC.alpha :=
    (Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard)
      (Set.toFinite (perp D β))).symm
  have hβV : β ∈ Valpha D hC.alpha := mem_Valpha_iff.mpr ⟨hβclass, hperpeq⟩
  intro hV
  have hβα' : β = hC.alpha := by simpa [hV] using hβV
  exact hβα hβα'

theorem no_firstKind_of_H (hC : HypothesisC D)
    (hH : ∀ x w y : G, x ∈ DalphaStar D hC.alpha → w ∈ DalphaStar D hC.alpha →
      y ∈ DalphaStar D hC.alpha → IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)))
    (hA : (Aalpha D hC.alpha).Nonempty) :
    ∀ x w y : G, IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)) := by
  classical
  intro x w y htri hfirst
  obtain ⟨hodd, _hgt⟩ := hfirst
  have hxyD : x * y ∈ D :=
    IsTriangle.mul_mem_of_odd hC.setup.oddT hC.setup.normal htri hodd
  have hB : ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ Commute x y ∧ x * y ∈ D :=
    ⟨x, htri.1, y, htri.2.1, htri.2.2.2.1, htri.2.2.2.2.1, hxyD⟩
  have hcomm := commute_DalphaStar_of_mul_mem hC hH hB
  have hVne : Valpha D hC.alpha ≠ {hC.alpha} :=
    Valpha_ne_singleton_of_commute_DalphaStar hC hcomm
  have hproper : Valpha D hC.alpha ≠ blockClass hC.alpha := by
    intro hV
    obtain ⟨γ, hγ⟩ := hA
    have hγV : γ ∈ Valpha D hC.alpha := by
      rw [hV]
      exact hγ.1
    have hγne : γ ≠ hC.alpha :=
      fun e => (mem_Aalpha_iff.mp hγ).2 (mem_perp_iff.mpr (Or.inr e))
    have hαγ : hC.alpha ∈ perp D γ := by
      rw [(mem_Valpha_iff.mp hγV).2]
      exact mem_perp_iff.mpr (Or.inr rfl)
    rcases mem_perp_iff.mp hαγ with h | h
    · have hγDα : γ ∈ Dalpha D hC.alpha := by
        rw [mem_Dalpha_iff]
        refine ⟨hγ.1, subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ.1,
          hγne, ?_⟩
        intro a ha b hb
        exact ((mem_Dalpha_iff.mp h).2.2.2 b hb a ha).symm
      exact (mem_Aalpha_iff.mp hγ).2 (mem_perp_iff.mpr (Or.inl hγDα))
    · exact hγne h.symm
  have hVsingle : Valpha D hC.alpha = {hC.alpha} :=
    Valpha_eq_singleton_of_isMaxBlock_of_ne hC.setup.normal hC.isMaxBlock_alpha hproper
  exact hVne hVsingle

end CFSG.OddTranspositions
