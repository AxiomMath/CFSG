module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2WeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley
open CFSG.Blueprint (LieModel)

theorem card_center_sylow_three_eq_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y]
    [Finite Y'] (e : Y ≃* Y') (Q : Sylow 3 Y) (Q' : Sylow 3 Y') :
    Nat.card (Subgroup.center (Q : Subgroup Y)) = Nat.card (Subgroup.center (Q' : Subgroup Y')) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q'' : Sylow 3 Y' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ'' : (Q'' : Subgroup Y') = (Q : Subgroup Y).map e.toMonoidHom := by
    simp [Q'']
  have h1 : (Q : Subgroup Y) ≃* (Q'' : Subgroup Y') := by
    rw [hQ'']
    exact e.subgroupMap (Q : Subgroup Y)
  have h2 : (Q'' : Subgroup Y') ≃* (Q' : Subgroup Y') := Sylow.equiv Q'' Q'
  exact Nat.card_congr (Subgroup.centerCongr (h1.trans h2)).toEquiv

theorem g2SylowCenterCardThree_holds :
    ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 3 → (p = 2 → 2 ≤ f) →
      LieModel Y .G2 0 p f → ∀ S : Sylow 3 Y, Nat.card (Subgroup.center (S : Subgroup Y)) = 3 := by
  classical
  intro Y _ _ p f hp hp3 _ hY S
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 p f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨⟨hrp, -, -, hrf3⟩, hm⟩ := hc
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eY⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq3 : 3 ≤ Nat.card K := by
    rw [hKcard]
    exact hrf3
  obtain ⟨Q0, z0, ⟨P, hP⟩, hcen, hord, -⟩ := g2_exists_sylow_center_generator_weakClosed h3 hq3
  have hcard : Nat.card (Subgroup.center (P : Subgroup (adjointGroup .G2 K))) = 3 := by
    rw [hP, hcen, Nat.card_zpowers]
    rw [← hord]
    exact (Subgroup.orderOf_coe z0).symm
  rw [card_center_sylow_three_eq_of_mulEquiv eY S P]
  exact hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
