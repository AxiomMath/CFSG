module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem center_eq_bot (N : ℕ) : Subgroup.center (SpecialLinearGroup (Fin N) F2) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Fintype.card_fin] at hr
  have hscalar : Matrix.scalar (Fin N) r = 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst N
      ext i j
      exact Fin.elim0 i
    · haveI : Subsingleton F2ˣ := by
        have h2 : Nat.card F2 = 2 := GaloisField.card 2 1 (by omega)
        exact (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, h2])).1
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by omega : N ≠ 0)] at hr
        exact zero_ne_one hr
      have hr1 : r = 1 := by
        obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr hr0
        rw [← hu, Subsingleton.elim u 1, Units.val_one]
      rw [hr1]
      ext i j
      simp [Matrix.scalar_apply]
  apply Subtype.ext
  rw [← hrA, hscalar, Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_commute_range {G : Type} [Group G] {N : ℕ}
    {ψ : SpecialLinearGroup (Fin N) F2 →* G} (hψ : Function.Injective ψ)
    {s : SpecialLinearGroup (Fin N) F2} (hs : ∀ t, ψ s * ψ t = ψ t * ψ s) : s = 1 := by
  have hs' : s ∈ Subgroup.center (SpecialLinearGroup (Fin N) F2) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply hψ
    rw [map_mul, map_mul]
    exact (hs t).symm
  have h := hs'
  rw [center_eq_bot N] at h
  exact Subgroup.mem_bot.mp h

theorem mem_zpowers_omegaBlock_of_commute_lower {m : ℕ}
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ht : t ∈ halfTorus (m + 1 + 1))
    (hc : ∀ s, t * slLower2Hom m s = slLower2Hom m s * t) :
    t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := by
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
  have hωcomm : ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * slLower2Hom m s =
        slLower2Hom m s * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ := by
    intro s
    have hx : slLower2Hom m s ∈
        slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
      rw [← range_slLower2Hom m]
      exact ⟨s, rfl⟩
    exact commute_omegaBlock_slOn (k := ⟨0, by omega⟩)
      (by constructor <;>
        (simp only [Set.mem_setOf_eq, Fin.val_castSucc, Fin.val_succ]; omega)) hx
  have hacomm : ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      a * slLower2Hom m s = slLower2Hom m s * a := by
    intro s
    have hmem : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ∈
        Subgroup.centralizer
          ({slLower2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hωcomm s
    have hle2 : Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ≤
        Subgroup.centralizer
          ({slLower2Hom m s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
      Subgroup.zpowers_le.mpr hmem
    have hmem' := hle2 ha
    rwa [Subgroup.mem_centralizer_singleton_iff] at hmem'
  have hXu : slLower2Hom m u = a⁻¹ * t := by
    rw [hub, ← hab, inv_mul_cancel_left]
  have hcomm_u : ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      slLower2Hom m u * slLower2Hom m s = slLower2Hom m s * slLower2Hom m u := by
    intro s
    have hxa : a⁻¹ * slLower2Hom m s * a = slLower2Hom m s := by
      rw [mul_assoc, ← hacomm s, inv_mul_cancel_left]
    rw [hXu]
    calc (a⁻¹ * t) * slLower2Hom m s
        = a⁻¹ * (t * slLower2Hom m s) := by rw [mul_assoc]
      _ = a⁻¹ * (slLower2Hom m s * t) := by rw [hc s]
      _ = a⁻¹ * (slLower2Hom m s * (a * slLower2Hom m u)) := by rw [← hab, ← hub]
      _ = a⁻¹ * slLower2Hom m s * a * slLower2Hom m u := by group
      _ = slLower2Hom m s * slLower2Hom m u := by rw [hxa]
      _ = slLower2Hom m s * (a⁻¹ * t) := by rw [hXu]
  have hcent : u ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F2) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply slLower2Hom_injective m
    rw [map_mul, map_mul]
    exact (hcomm_u s).symm
  have hu1 : u = 1 := by
    have h := hcent
    rw [center_eq_bot (m + 1)] at h
    exact Subgroup.mem_bot.mp h
  have hb1 : b = 1 := by rw [← hub, hu1, map_one]
  rw [← hab, hb1, mul_one]
  exact ha

end CFSG.StandardType.GGHalf

end
