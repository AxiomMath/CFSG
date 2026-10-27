module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem exists_lam_zero_of_mem_centralizer_levi [CharP F 2] {m : ℕ} {u : StatedSp (m + 1) F}
    (hu : u ∈ Subgroup.centralizer
      ((CFSG.StandardType.spLeviBlock m F).range : Set (StatedSp (m + 1) F))) :
    ∃ g : SpecialLinearGroup (Fin 2) F, u = lam (0 : Fin (m + 1)) g := by
  have hN : u ∈ Subgroup.normalizer
      ((CFSG.StandardType.spLeviBlock m F).range : Set (StatedSp (m + 1) F)) :=
    Subgroup.centralizer_le_normalizer _ hu
  obtain ⟨g, h, rfl⟩ := exists_lam_mul_levi_of_mem_normalizer hN
  refine ⟨g, ?_⟩
  have hcentral : ∀ h' : StatedSp m F, h' * h = h * h' := by
    intro h'
    have hmem : CFSG.StandardType.spLeviBlock m F h' ∈
        ((CFSG.StandardType.spLeviBlock m F).range : Set (StatedSp (m + 1) F)) := ⟨h', rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hu _ hmem
    have hcomm : lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h' =
        CFSG.StandardType.spLeviBlock m F h' * lam (0 : Fin (m + 1)) g :=
      (lam_zero_commute_spLeviBlock g h').eq
    have e1 : lam (0 : Fin (m + 1)) g *
        (CFSG.StandardType.spLeviBlock m F h' * CFSG.StandardType.spLeviBlock m F h) =
        lam (0 : Fin (m + 1)) g *
        (CFSG.StandardType.spLeviBlock m F h * CFSG.StandardType.spLeviBlock m F h') := by
      calc lam (0 : Fin (m + 1)) g *
            (CFSG.StandardType.spLeviBlock m F h' * CFSG.StandardType.spLeviBlock m F h)
          = (lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h') *
              CFSG.StandardType.spLeviBlock m F h := by rw [mul_assoc]
        _ = (CFSG.StandardType.spLeviBlock m F h' * lam (0 : Fin (m + 1)) g) *
              CFSG.StandardType.spLeviBlock m F h := by rw [hcomm]
        _ = CFSG.StandardType.spLeviBlock m F h' *
              (lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h) := by
            rw [mul_assoc]
        _ = (lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h) *
              CFSG.StandardType.spLeviBlock m F h' := hc
        _ = lam (0 : Fin (m + 1)) g *
              (CFSG.StandardType.spLeviBlock m F h * CFSG.StandardType.spLeviBlock m F h') := by
            rw [mul_assoc]
    have e2 := mul_left_cancel e1
    apply CFSG.StandardType.spLeviBlock_injective
    rw [map_mul, map_mul]
    exact e2
  have hZ : Subgroup.center (StatedSp m F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hh : h = 1 := by
    have hmem : h ∈ Subgroup.center (StatedSp m F) := Subgroup.mem_center_iff.mpr hcentral
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [hh, map_one, mul_one]

theorem card_le_of_isElemAbelian_le_range_lam_zero [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) {m : ℕ} {E : Subgroup (StatedSp (m + 1) F)} (hE : IsElemAbelian p E)
    (hle : E ≤ (lam (0 : Fin (m + 1)) : SpecialLinearGroup (Fin 2) F →* StatedSp (m + 1) F).range) :
    Nat.card E ≤ p := by
  let E₀ : Subgroup (SpecialLinearGroup (Fin 2) F) := E.comap (lam (0 : Fin (m + 1)))
  have hE₀ : IsElemAbelian p E₀ := IsElemAbelian.comap hE (lam_injective (0 : Fin (m + 1)))
  have hmap : E₀.map (lam (0 : Fin (m + 1))) = E := Subgroup.map_comap_eq_self hle
  have hcard : Nat.card E = Nat.card E₀ := by
    conv_lhs => rw [← hmap]
    exact Subgroup.card_map_of_injective (lam_injective (0 : Fin (m + 1)))
  let E₁ : Subgroup (StatedSp 1 F) := E₀.map (lam (0 : Fin 1))
  have hE₁ : IsElemAbelian p E₁ := IsElemAbelian.map hE₀ _
  have hcard₁ : Nat.card E₁ = Nat.card E₀ :=
    Subgroup.card_map_of_injective (lam_injective (0 : Fin 1))
  have h1 := card_le_pow_of_isElemAbelian hp hp2 hpF E₁ hE₁
  rw [hcard, ← hcard₁]
  simpa using h1

end CFSG.StandardType.SpJoin
