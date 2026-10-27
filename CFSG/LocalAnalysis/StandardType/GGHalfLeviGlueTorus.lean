module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem slLower2Hom_mem_halfTorus {m : ℕ} {s : SpecialLinearGroup (Fin (m + 1)) F2}
    (hs : s ∈ halfTorus m) : slLower2Hom m s ∈ halfTorus (m + 1 + 1) := by
  rw [halfTorus_succ_succ m]
  exact Subgroup.mem_sup_right ⟨s, hs, rfl⟩

theorem slUpper2Hom_mem_halfTorusK {m : ℕ} {s : SpecialLinearGroup (Fin (m + 1)) F2}
    (hs : s ∈ halfTorus m) : slUpper2Hom m s ∈ halfTorusK (m + 1 + 1) := by
  rw [halfTorusK_succ_succ m]
  exact Subgroup.mem_sup_right ⟨s, hs, rfl⟩

private lemma mul_inv_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹ = (b⁻¹ * b) * a * b⁻¹ := by group
    _ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [← h]
    _ = b⁻¹ * a := by group

private lemma conj_mul_of_commute {G : Type*} [Group G] {a b u : G} (h : a * b = b * a) :
    b * (a * u) * b⁻¹ = a * (b * u * b⁻¹) := by
  calc b * (a * u) * b⁻¹ = (b * a) * u * b⁻¹ := by group
    _ = (a * b) * u * b⁻¹ := by rw [← h]
    _ = a * (b * u * b⁻¹) := by group

private lemma conj_mul_eq_of_commute {G : Type*} [Group G] {a u w : G}
    (hu : a * u = u * a) (hw : a * w = w * a) :
    (a * u) * w * (a * u)⁻¹ = u * w * u⁻¹ := by
  have hui : a * u⁻¹ = u⁻¹ * a := mul_inv_comm hu
  have hX : a * (u * w * u⁻¹) = u * w * u⁻¹ * a := by
    calc a * (u * w * u⁻¹)
        = a * u * w * u⁻¹ := by group
      _ = u * a * w * u⁻¹ := by rw [hu]
      _ = u * (a * w) * u⁻¹ := by group
      _ = u * (w * a) * u⁻¹ := by rw [hw]
      _ = u * w * (a * u⁻¹) := by group
      _ = u * w * (u⁻¹ * a) := by rw [hui]
      _ = u * w * u⁻¹ * a := by group
  calc (a * u) * w * (a * u)⁻¹
      = a * (u * w * u⁻¹) * a⁻¹ := by rw [_root_.mul_inv_rev]; group
    _ = u * w * u⁻¹ := by rw [hX, mul_assoc, mul_inv_cancel, mul_one]

private lemma exists_eq_mul_slLower2Hom {m : ℕ}
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorus (m + 1 + 1)) :
    ∃ a ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩),
      ∃ u ∈ halfTorus m, t = a * slLower2Hom m u ∧
        ∀ w, a * slLower2Hom m w = slLower2Hom m w * a := by
  rw [halfTorus_succ_succ m] at ht
  have hSle : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ≤
      halfTorus (m + 1 + 1) := by
    rw [halfTorus_succ_succ m]; exact le_sup_left
  have hTle : (halfTorus m).map (slLower2Hom m) ≤ halfTorus (m + 1 + 1) := by
    rw [halfTorus_succ_succ m]; exact le_sup_right
  have hle : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ≤
      Subgroup.normalizer ((halfTorus m).map (slLower2Hom m)) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    have hcomm : h * k = k * h := halfTorus_comm (hSle hh) (hTle hk)
    have : h * k * h⁻¹ = k := by rw [hcomm]; group
    rwa [this]
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩))
    ((halfTorus m).map (slLower2Hom m)) hle
  have ht' : t ∈ (↑(Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ⊔
      (halfTorus m).map (slLower2Hom m)) :
        Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := ht
  rw [hcoe] at ht'
  rw [Set.mem_mul] at ht'
  obtain ⟨a, ha, b, hb, hab⟩ := ht'
  obtain ⟨u, hu, hub⟩ := Subgroup.mem_map.mp hb
  refine ⟨a, ha, u, hu, ?_, ?_⟩
  · rw [← hab, hub]
  · intro s
    have hωcomm : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * slLower2Hom m s =
        slLower2Hom m s * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ := by
      have hx : slLower2Hom m s ∈
          slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
        rw [← range_slLower2Hom m]
        exact ⟨s, rfl⟩
      exact commute_omegaBlock_slOn (k := ⟨0, by omega⟩)
        (by constructor <;>
          (simp only [Set.mem_setOf_eq, Fin.val_castSucc, Fin.val_succ]; omega)) hx
    have hmem : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ∈
        Subgroup.centralizer
          ({slLower2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hωcomm
    have hle2 : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ≤
        Subgroup.centralizer
          ({slLower2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
      Subgroup.zpowers_le.mpr hmem
    have hmem' := hle2 ha
    rwa [Subgroup.mem_centralizer_singleton_iff] at hmem'

private lemma exists_eq_mul_slUpper2Hom {m : ℕ}
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorusK (m + 1 + 1)) :
    ∃ a ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩),
      ∃ u ∈ halfTorus m, t = a * slUpper2Hom m u ∧
        ∀ w, a * slUpper2Hom m w = slUpper2Hom m w * a := by
  rw [halfTorusK_succ_succ m] at ht
  have hSle : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ≤
      halfTorusK (m + 1 + 1) := by
    rw [halfTorusK_succ_succ m]; exact le_sup_left
  have hTle : (halfTorus m).map (slUpper2Hom m) ≤ halfTorusK (m + 1 + 1) := by
    rw [halfTorusK_succ_succ m]; exact le_sup_right
  have hle : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ≤
      Subgroup.normalizer ((halfTorus m).map (slUpper2Hom m)) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    have hcomm : h * k = k * h := halfTorusK_comm (hSle hh) (hTle hk)
    have : h * k * h⁻¹ = k := by rw [hcomm]; group
    rwa [this]
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩))
    ((halfTorus m).map (slUpper2Hom m)) hle
  have ht' : t ∈ (↑(Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ⊔
      (halfTorus m).map (slUpper2Hom m)) :
        Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := ht
  rw [hcoe] at ht'
  rw [Set.mem_mul] at ht'
  obtain ⟨a, ha, b, hb, hab⟩ := ht'
  obtain ⟨u, hu, hub⟩ := Subgroup.mem_map.mp hb
  refine ⟨a, ha, u, hu, ?_, ?_⟩
  · rw [← hab, hub]
  · intro s
    have hωcomm : omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * slUpper2Hom m s =
        slUpper2Hom m s * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by
      have hx : slUpper2Hom m s ∈
          slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := by
        rw [← range_slUpper2Hom m]
        exact ⟨s, rfl⟩
      exact commute_omegaBlock_slOn (k := ⟨m + 1, by omega⟩)
        (by constructor <;> (simp only [Set.mem_setOf_eq, Fin.val_castSucc, Fin.val_succ]; omega)) hx
    have hmem : omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ ∈
        Subgroup.centralizer
          ({slUpper2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hωcomm
    have hle2 : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ≤
        Subgroup.centralizer
          ({slUpper2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
      Subgroup.zpowers_le.mpr hmem
    have hmem' := hle2 ha
    rwa [Subgroup.mem_centralizer_singleton_iff] at hmem'

theorem exists_levi_conj_lower {m : ℕ} {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ht : t ∈ halfTorus (m + 1 + 1)) :
    ∃ s ∈ halfTorus m, ∀ w : SpecialLinearGroup (Fin (m + 1)) F2,
      t * slLower2Hom m w * t⁻¹ = slLower2Hom m (s * w * s⁻¹) := by
  obtain ⟨a, ha, u, hu, ht_eq, hacomm⟩ := exists_eq_mul_slLower2Hom ht
  refine ⟨u, hu, fun w => ?_⟩
  rw [ht_eq]
  calc (a * slLower2Hom m u) * slLower2Hom m w * (a * slLower2Hom m u)⁻¹
      = slLower2Hom m u * slLower2Hom m w * (slLower2Hom m u)⁻¹ :=
        conj_mul_eq_of_commute (hacomm u) (hacomm w)
    _ = slLower2Hom m (u * w * u⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem exists_levi_conj_upper {m : ℕ} {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ht : t ∈ halfTorusK (m + 1 + 1)) :
    ∃ s ∈ halfTorus m, ∀ w : SpecialLinearGroup (Fin (m + 1)) F2,
      t * slUpper2Hom m w * t⁻¹ = slUpper2Hom m (s * w * s⁻¹) := by
  obtain ⟨a, ha, u, hu, ht_eq, hacomm⟩ := exists_eq_mul_slUpper2Hom ht
  refine ⟨u, hu, fun w => ?_⟩
  rw [ht_eq]
  calc (a * slUpper2Hom m u) * slUpper2Hom m w * (a * slUpper2Hom m u)⁻¹
      = slUpper2Hom m u * slUpper2Hom m w * (slUpper2Hom m u)⁻¹ :=
        conj_mul_eq_of_commute (hacomm u) (hacomm w)
    _ = slUpper2Hom m (u * w * u⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem conj_slUpper2Hom_mem_halfTorusK {m : ℕ} {c : SpecialLinearGroup (Fin (m + 1)) F2}
    (hc : ∀ s ∈ halfTorus m, c * s * c⁻¹ ∈ halfTorus m)
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorusK (m + 1 + 1)) :
    slUpper2Hom m c * t * (slUpper2Hom m c)⁻¹ ∈ halfTorusK (m + 1 + 1) := by
  obtain ⟨a, ha, u, hu, ht_eq, hacomm⟩ := exists_eq_mul_slUpper2Hom ht
  rw [ht_eq, conj_mul_of_commute (hacomm c)]
  have hmap : slUpper2Hom m c * slUpper2Hom m u * (slUpper2Hom m c)⁻¹
      = slUpper2Hom m (c * u * c⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap, halfTorusK_succ_succ m]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right ⟨c * u * c⁻¹, hc u hu, rfl⟩)

end CFSG.StandardType.GGHalf

end
