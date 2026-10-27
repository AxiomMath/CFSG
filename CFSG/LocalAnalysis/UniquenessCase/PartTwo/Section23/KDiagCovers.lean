module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

@[expose] noncomputable def quotientCenterAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun a := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) a
    (Subgroup.map_center_eq a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem quotientCenterAut_apply_mk {H : Type*} [Group H] (a : MulAut H) (x : H) :
    quotientCenterAut H a (QuotientGroup.mk' (Subgroup.center H) x) =
      QuotientGroup.mk' (Subgroup.center H) (a x) :=
  QuotientGroup.congr_mk' (Subgroup.center H) (Subgroup.center H) a
    (Subgroup.map_center_eq a) x

theorem kDiag_of_centralQuotient {X : Type} [Group X] [Finite X]
    (hquot : ∀ (θbar : MulAut (X ⧸ Subgroup.center X)), Odd (orderOf θbar) →
      ∀ Sbar : Sylow 2 (X ⧸ Subgroup.center X),
        (∀ y ∈ (Sbar : Subgroup (X ⧸ Subgroup.center X)),
          θbar y ∈ (Sbar : Subgroup (X ⧸ Subgroup.center X))) →
      ∀ Pbar : Subgroup (X ⧸ Subgroup.center X),
        IsParabolicTwo (X ⧸ Subgroup.center X) Pbar →
        (Sbar : Subgroup (X ⧸ Subgroup.center X)) ≤
          Subgroup.normalizer (Pbar : Set (X ⧸ Subgroup.center X)) →
        ∀ y ∈ Pbar, θbar y ∈ Pbar) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ S hSθ P hP hSP x hx
  let Z : Subgroup X := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set θbar : MulAut (X ⧸ Z) := quotientCenterAut X θ with hθbar_def
  have hθbar_apply : ∀ y : X, θbar (π y) = π (θ y) := by
    intro y
    rw [hθbar_def]
    exact quotientCenterAut_apply_mk θ y
  have hθbar_odd : Odd (orderOf θbar) := by
    have hdvd : orderOf θbar ∣ orderOf θ := by
      rw [hθbar_def]
      exact orderOf_map_dvd (quotientCenterAut X) θ
    exact Odd.of_dvd_nat hθ hdvd
  let Sbar : Sylow 2 (X ⧸ Z) := S.mapSurjective (f := π) hπ
  have hSbar_coe : (Sbar : Subgroup (X ⧸ Z)) = (S : Subgroup X).map π :=
    Sylow.coe_mapSurjective (f := π) hπ S
  have hSbarθ : ∀ y ∈ (Sbar : Subgroup (X ⧸ Z)), θbar y ∈ (Sbar : Subgroup (X ⧸ Z)) := by
    intro y hy
    rw [hSbar_coe] at hy ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hθbar_apply s]
    exact Subgroup.mem_map_of_mem π (hSθ s hs)
  have hPbar : IsParabolicTwo (X ⧸ Z) (P.map π) := IsParabolicTwo.map hP π hπ
  have hSPbar : (Sbar : Subgroup (X ⧸ Z)) ≤
      Subgroup.normalizer ((P.map π) : Set (X ⧸ Z)) := by
    rw [hSbar_coe]
    exact (Subgroup.map_mono hSP).trans (Subgroup.le_normalizer_map (f := π) (H := P))
  have hfix := hquot θbar hθbar_odd Sbar hSbarθ (P.map π) hPbar hSPbar
  have hZP : Z ≤ P := hP.center_le
  have hPcomap : Subgroup.comap π (Subgroup.map π P) = P :=
    Subgroup.comap_map_eq_self (by rw [hker]; exact hZP)
  have hmem : π (θ x) ∈ Subgroup.map π P := by
    have h1 := hfix (π x) (Subgroup.mem_map_of_mem π hx)
    rwa [hθbar_apply x] at h1
  rw [show P = Subgroup.comap π (Subgroup.map π P) from hPcomap.symm, Subgroup.mem_comap]
  exact hmem

theorem kDiag_of_isSL3 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsSL3 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P :=
  kDiag_of_centralQuotient (X := X) fun θbar hθbar Sbar hSbarθ Pbar hPbar hSPbar =>
    kDiag_of_isL3 (X := X ⧸ Subgroup.center X) (n := n) hX.2
      θbar hθbar Sbar hSbarθ Pbar hPbar hSPbar

theorem kDiag_of_isSU3 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsSU3 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P :=
  kDiag_of_centralQuotient (X := X) fun θbar hθbar Sbar hSbarθ Pbar hPbar hSPbar =>
    kDiag_of_isU3 (X := X ⧸ Subgroup.center X) (n := n) hX.2
      θbar hθbar Sbar hSbarθ Pbar hPbar hSPbar

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
