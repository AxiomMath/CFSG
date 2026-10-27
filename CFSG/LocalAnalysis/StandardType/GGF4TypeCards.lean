module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD

public section

namespace CFSG.StandardType

private theorem ggF4Orig_card_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hC : GGIntCartan CoxeterMatrix.E₆ (CFSG.Blueprint.Chevalley.Tag.cartan .E6) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) = CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) = 51840 :=
    CFSG.StandardType.NoOffExc.card_weyl_E6
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)).Group) = 51840 at h
  rw [hM] at h
  exact h

private theorem ggF4Orig_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hC : GGIntCartan CoxeterMatrix.E₇ (CFSG.Blueprint.Chevalley.Tag.cartan .E7) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E7) = 2903040 :=
    CFSG.StandardType.NoOffExc.card_weyl_E7
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)).Group) = 2903040 at h
  rw [hM] at h
  exact h

private theorem ggF4Orig_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hC : GGIntCartan CoxeterMatrix.E₈ (CFSG.Blueprint.Chevalley.Tag.cartan .E8) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E8) = 696729600 :=
    CFSG.StandardType.NoOffExc.card_weyl_E8
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)).Group) = 696729600 at h
  rw [hM] at h
  exact h

theorem ggF4Orig_card_coxeterF4 :
    Nat.card (CoxeterMatrix.F₄).Group = 1152 := by
  have hC : GGIntCartan CoxeterMatrix.F₄ (CFSG.Blueprint.Chevalley.Tag.cartan .F4) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .F4) = 1152 :=
    CFSG.Monster.B.Geometry.card_f4WeylGroup
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group) = 1152 at h
  rw [hM] at h
  exact h

theorem ggF4Orig_card_weylOfType_F4
    {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (h : GGWeylOfType p CoxeterMatrix.F₄ A) : Nat.card ↥A = 1152 := by
  obtain ⟨e, -⟩ := h
  rw [← Nat.card_congr e.toEquiv]
  exact ggF4Orig_card_coxeterF4

theorem ggF4Orig_type_cases
    {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (h : GGWeylReflectionGroup p A) (hd : Nat.card ↥A ∣ 1152) :
    (∃ n, 1 ≤ n ∧ n ≤ 3 ∧ GGWeylOfType p (CoxeterMatrix.A n) A) ∨
      (∃ n, 2 ≤ n ∧ n ≤ 4 ∧ GGWeylOfType p (CoxeterMatrix.B n) A) ∨
      GGWeylOfType p (ggCoxeterMatrixD 4) A ∨ GGWeylOfType p CoxeterMatrix.F₄ A ∨
      GGWeylOfType p CoxeterMatrix.G₂ A := by
  have h5 : ¬ (5 ∣ 1152) := by norm_num
  rcases ggWeylReflectionGroup_cases h with ⟨n, hn, hT⟩ | ⟨n, hn, hT⟩ | ⟨n, hn, hT⟩ | hT | hT |
    hT | hT | hT
  · refine Or.inl ⟨n, hn, ?_, hT⟩
    by_contra hlt
    have hcard := ggWeylOfType_A_card hT
    rw [hcard] at hd
    have h5d : 5 ∣ (n + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    exact h5 (h5d.trans hd)
  · refine Or.inr (Or.inl ⟨n, hn, ?_, hT⟩)
    by_contra hlt
    obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 2 ^ n * n.factorial := by
      rw [← Nat.card_congr e.toEquiv]
      exact le_antisymm (card_coxeterB_le n) (CFSG.StandardType.SpFrame.card_coxeterB_ge n hn)
    rw [hcard] at hd
    have h5d : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    exact h5 ((h5d.trans (Dvd.intro_left _ rfl)).trans hd)
  · obtain ⟨e, he⟩ := hT
    by_cases hn4 : n = 4
    · subst hn4
      exact Or.inr (Or.inr (Or.inl ⟨e, he⟩))
    · exfalso
      have hcard : Nat.card ↥A = 2 ^ (n - 1) * n.factorial := by
        rw [← Nat.card_congr e.toEquiv]
        exact CFSG.StandardType.OrthF3.card_coxeterD_eq n hn
      rw [hcard] at hd
      have h5d : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      exact h5 ((h5d.trans (Dvd.intro_left _ rfl)).trans hd)
  · exfalso
    obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 51840 := by
      rw [← Nat.card_congr e.toEquiv, ggF4Orig_card_coxeterE6]
    rw [hcard] at hd
    norm_num at hd
  · exfalso
    obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 2903040 := by
      rw [← Nat.card_congr e.toEquiv, ggF4Orig_card_coxeterE7]
    rw [hcard] at hd
    norm_num at hd
  · exfalso
    obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 696729600 := by
      rw [← Nat.card_congr e.toEquiv, ggF4Orig_card_coxeterE8]
    rw [hcard] at hd
    norm_num at hd
  · exact Or.inr (Or.inr (Or.inr (Or.inl hT)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hT)))

end CFSG.StandardType

end
