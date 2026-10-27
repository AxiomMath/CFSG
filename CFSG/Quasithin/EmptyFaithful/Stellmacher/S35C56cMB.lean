module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S35.C56

variable {G : Type} [Group G] [Finite G]

theorem exists_central_of_pGroup {P E D : Subgroup G}
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPD : P ≤ Subgroup.normalizer (D : Set G))
    (hDE : D ≤ Subgroup.normalizer (E : Set G)) (hPp : IsPGroup 2 P) (hD : IsPGroup 2 D)
    (hne : ¬ D ≤ E) :
    ∃ d ∈ D, d ∉ E ∧ ∀ p ∈ P, p * d * p⁻¹ * d⁻¹ ∈ E := by
  set K : Subgroup G := D ⊔ P with hK
  have hKp : IsPGroup 2 K := hD.to_sup_of_normal_left' hPp hPD
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := sup_le hDE hPE
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hPD
  have hEn : (E.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      simpa [Subgroup.mem_subgroupOf] using (Subgroup.mem_normalizer_iff.mp (hKE g.2) n).mp
        (Subgroup.mem_subgroupOf.mp hn)⟩
  have hDn : (D.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      simpa [Subgroup.mem_subgroupOf] using (Subgroup.mem_normalizer_iff.mp (hKD g.2) n).mp
        (Subgroup.mem_subgroupOf.mp hn)⟩
  let π := QuotientGroup.mk' (E.subgroupOf K)
  have hQp : IsPGroup 2 (↥K ⧸ E.subgroupOf K) := hKp.to_quotient _
  have : Group.IsNilpotent (↥K ⧸ E.subgroupOf K) := hQp.isNilpotent
  have hNn : ((D.subgroupOf K).map π).Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  have hN1 : (D.subgroupOf K).map π ≠ ⊥ := by
    intro h
    apply hne
    intro d hd
    have hdK : d ∈ K := (le_sup_left : D ≤ D ⊔ P) hd
    have : π ⟨d, hdK⟩ ∈ (D.subgroupOf K).map π := ⟨⟨d, hdK⟩, hd, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp this)
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  obtain ⟨⟨k, hkD, hkc⟩, hcz⟩ := Subgroup.mem_inf.mp c.2
  have hc1 : (c : ↥K ⧸ E.subgroupOf K) ≠ 1 := fun h => hc (Subtype.ext h)
  refine ⟨k.1, Subgroup.mem_subgroupOf.mp hkD, fun hkE => hc1 ?_, fun p hp => ?_⟩
  · rw [← hkc]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkE)
  · have hpK : p ∈ K := (le_sup_right : P ≤ D ⊔ P) hp
    have hz := Subgroup.mem_center_iff.mp hcz (π ⟨p, hpK⟩)
    rw [← hkc] at hz
    have h1 : π (⟨p, hpK⟩ * k * ⟨p, hpK⟩⁻¹ * k⁻¹) = 1 := by
      simp only [map_mul, map_inv, hz]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem exists_central_mod {X Lg P E D : Subgroup G}
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hDE : D ≤ Subgroup.normalizer (E : Set G))
    (hP : P ≤ X) (hPp : IsPGroup 2 P) (hD : IsPGroup 2 D) (hLg : Lg ≤ X)
    (hgen : ∀ x ∈ X, ∃ l ∈ Lg, ∃ p ∈ P, x = l * p) (hne : ¬ D ≤ E)
    (hl : ∀ l ∈ Lg, ∀ d ∈ D, l * d * l⁻¹ * d⁻¹ ∈ E) :
    ∃ d ∈ D, d ∉ E ∧ ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ ∈ E := by
  obtain ⟨d, hdD, hdE, hd⟩ := exists_central_of_pGroup (hP.trans hXE) (hP.trans hXD) hDE hPp hD
    hne
  refine ⟨d, hdD, hdE, fun x hx => ?_⟩
  obtain ⟨l, hl', p, hp, rfl⟩ := hgen x hx
  have h1 := hl l hl' d hdD
  have h2 := hd p hp
  have hconj : l * (p * d * p⁻¹ * d⁻¹) * l⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hXE (hLg hl')) _).mp h2
  have : l * p * d * (l * p)⁻¹ * d⁻¹ =
      (l * (p * d * p⁻¹ * d⁻¹) * l⁻¹) * (l * d * l⁻¹ * d⁻¹) := by group
  rw [this]
  exact E.mul_mem hconj h1

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
