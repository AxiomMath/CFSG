module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots

import CFSG.LocalAnalysis.StandardType.GGLevTwoS2aAux
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2aCases

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem LevTwoType CFSG.LieType.Universal.SpecialLinear
open scoped Matrix

private theorem levTwoS2a_data_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    {R R' : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (he : R = R') (p : ℕ) (c : ι → ZMod p) (Φ : Set (ι → ℤ)) :
    LevTwoData hR p c Φ ↔ LevTwoData hR' p c Φ := by
  subst he
  rw [Subsingleton.elim hR hR']

private theorem levTwoS2a_tcRoot_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    {R R' : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (he : R = R') (Φ : Set (ι → ℤ)) : TCRoot hR Φ ↔ TCRoot hR' Φ := by
  subst he
  rw [Subsingleton.elim hR hR']

private theorem levTwoS2a_engine (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) : TCRoot (isFiniteType_A n) Φ := by
  obtain ⟨B, hB, huniq⟩ := levTwoS2a_exists_large_fibre n hn p hp hp2 c Φ h
  have hge := levTwoS2a_fibre_card_ge n hn p hp hp2 c Φ h hB huniq
  let comp : Finset (Fin (n+1)) :=
    Finset.univ.filter (fun k => levTwoS2a_D n p c k ≠ levTwoS2a_D n p c B)
  have hcomp_mem : ∀ k, k ∈ comp ↔ levTwoS2a_D n p c k ≠ levTwoS2a_D n p c B := by
    intro k
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfib_mem : ∀ k, k ∈ levTwoS2a_fibreF n p c B ↔ levTwoS2a_D n p c k = levTwoS2a_D n p c B := by
    intro k
    simp only [levTwoS2a_fibreF, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsplit : (levTwoS2a_fibreF n p c B).card + comp.card = n + 1 := by
    have hdisj : Disjoint (levTwoS2a_fibreF n p c B) comp := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      exact (hcomp_mem k).mp hk2 ((hfib_mem k).mp hk1)
    have hunion : (levTwoS2a_fibreF n p c B) ∪ comp = Finset.univ := by
      ext k
      rw [Finset.mem_union, hfib_mem, hcomp_mem]
      by_cases hk : levTwoS2a_D n p c k = levTwoS2a_D n p c B <;> simp [hk]
    calc (levTwoS2a_fibreF n p c B).card + comp.card
        = ((levTwoS2a_fibreF n p c B) ∪ comp).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = Finset.univ.card := by rw [hunion]
      _ = n + 1 := by simp [Fintype.card_fin]
  have hcz : comp.card = 0 ∨ comp.card = 1 ∨ comp.card = 2 := by omega
  rcases hcz with h0 | h1 | h2
  · exact levTwoS2a_tcRoot_allRoots n hn p hp hp2 c Φ h (B := B) (fun k => by
      by_contra hk
      have hmem : k ∈ comp := (hcomp_mem k).mpr hk
      rw [Finset.card_eq_zero.mp h0] at hmem
      exact absurd hmem (by simp))
  · obtain ⟨a, haz⟩ := Finset.card_eq_one.mp h1
    have haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B :=
      (hcomp_mem a).mp (haz ▸ Finset.mem_singleton_self a)
    exact levTwoS2a_tcRoot_oneComp n hn p hp hp2 c Φ h (B := B) (a := a) haD (fun k => by
      by_cases hka : k = a
      · exact Or.inr hka
      · left
        by_contra hkD
        exact hka (Finset.mem_singleton.mp (haz ▸ ((hcomp_mem k).mpr hkD))))
  · obtain ⟨a, b, hab, habz⟩ := Finset.card_eq_two.mp h2
    have haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B :=
      (hcomp_mem a).mp (habz ▸ by simp)
    have hbD : levTwoS2a_D n p c b ≠ levTwoS2a_D n p c B :=
      (hcomp_mem b).mp (habz ▸ by simp)
    exact levTwoS2a_tcRoot_twoComp n hn p hp hp2 c Φ h (B := B) (a := a) (b := b) haD hbD hab
      (fun k => by
        by_cases hka : k = a
        · exact Or.inr (Or.inl hka)
        · by_cases hkb : k = b
          · exact Or.inr (Or.inr hkb)
          · left
            by_contra hkD
            rcases Finset.mem_insert.mp (habz ▸ ((hcomp_mem k).mpr hkD)) with h | h
            · exact hka h
            · exact hkb (Finset.mem_singleton.mp h))

theorem levTwoEngine_A (n : ℕ) (hn : 1 ≤ n) : LevTwoEngine (LevTwoType.A n) := by
  intro p hp hp2 c Φ h
  have hroot : (LevTwoType.A n).root = CartanMatrix.A n := by
    simp only [LevTwoType.root, LevTwoType.pair]
    exact CartanMatrix.A_transpose n
  refine (levTwoS2a_tcRoot_congr (LevTwoType.rootFT (LevTwoType.A n)) (isFiniteType_A n)
    hroot Φ).mpr ?_
  exact levTwoS2a_engine n hn p hp hp2 c Φ
    ((levTwoS2a_data_congr (LevTwoType.rootFT (LevTwoType.A n)) (isFiniteType_A n)
      hroot p c Φ).mp h)

end CFSG.StandardType.LevTwo
