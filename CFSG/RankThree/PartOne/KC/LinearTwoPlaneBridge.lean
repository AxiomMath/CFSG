module

public import CFSG.RankThree.PartOne.KC.PlaneAbstract
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_automorphism_semilinear_isomorphism)

namespace KCLinearTwo

@[expose] noncomputable def abstractPlaneProduct (p : ℕ) {B : Type*} [Group B] (A : Subgroup B)
    (a : B) : Subgroup B :=
  ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set B)), A⁆ ⊔ thetaT p A

theorem planeData_coordinateG {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (B : Subgroup (MulAut (coordinateG K)))
    (hB : (MulAut.conj : coordinateG K →* MulAut (coordinateG K)).range ≤ B)
    (A : Subgroup (MulAut (coordinateG K))) (hAB : A ≤ B) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) {t : MulAut (coordinateG K)} (htA : t ∈ A) :
    ∃ B' : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ B' ∧ B' ≤ coordinateE K ∧
      ∃ (A' : Subgroup B') (a : B'), CFSG.Assembly.IsElemAbelian p A' ∧ Nat.card A' = p ^ 2 ∧
        a ∈ A' ∧ (t ≠ 1 → a ≠ 1) ∧
        Nat.card (autPlaneProduct p B A t) = Nat.card (abstractPlaneProduct p A' a) ∧
        (abstractPlaneProduct p A' a = ⊥ → autPlaneProduct p B A t = ⊥) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  obtain ⟨c, -, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism K
  let ι : MulAut (coordinateG K) →* Equiv.Perm (Omega K) :=
    (coordinateE K).subtype.comp c.symm.toMonoidHom
  have hι : Function.Injective ι := (coordinateE K).subtype_injective.comp c.symm.injective
  refine ⟨B.map ι, ?_, ?_, ?_⟩
  · intro x hx
    have h1 := hcG ⟨x, hx⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj ⟨x, hx⟩, hB ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    show ((c.symm (MulAut.conj ⟨x, hx⟩) : coordinateE K) : Equiv.Perm (Omega K)) = x
    rw [← h1]
    simp
  · rintro _ ⟨y, -, rfl⟩
    exact (c.symm y).2
  · let Φ : B ≃* B.map ι := B.equivMapOfInjective ι hι
    set AB : Subgroup B := A.subgroupOf B with hABdef
    have hABel : IsElementaryAbelian p AB := IsElementaryAbelian.subgroupOf hAB
    have hABcard : Nat.card AB = p ^ 2 := by
      rw [← hAcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
    have hABne : AB ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hABcard
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    set tB : B := ⟨t, hAB htA⟩ with htB
    have hAmap : AB.map B.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAB
    have htAB : tB ∈ AB := Subgroup.mem_subgroupOf.mpr htA
    refine ⟨AB.map Φ.toMonoidHom, Φ tB, ?_, ?_, Subgroup.mem_map_of_mem _ htAB, ?_, ?_, ?_⟩
    · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp
        (IsElementaryAbelian.map Φ.toMonoidHom)
    · rw [Subgroup.card_map_of_injective Φ.injective, hABcard]
    · intro ht1 h1
      apply ht1
      have : tB = 1 := Φ.injective (by simpa using h1)
      simpa [htB] using congrArg Subtype.val this
    · have h1 := autPlaneProduct_map_subtype hp B AB hABne tB
      rw [hAmap] at h1
      have h2 := map_planeProduct_mulEquiv hp Φ AB tB
      have h3 : Nat.card (autPlaneProduct p B A t) =
          Nat.card (abstractPlaneProduct p AB tB) := by
        rw [show (t : MulAut (coordinateG K)) = (tB : MulAut (coordinateG K)) from rfl, h1,
          Subgroup.card_map_of_injective B.subtype_injective]
        rfl
      rw [h3]
      have h4 := congrArg (fun H : Subgroup (B.map ι) => Nat.card H) h2
      rw [Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective] at h4
      exact h4
    · intro hbot
      have h1 := autPlaneProduct_map_subtype hp B AB hABne tB
      rw [hAmap] at h1
      have h2 := map_planeProduct_mulEquiv hp Φ AB tB
      have h5 : (abstractPlaneProduct p AB tB).map Φ.toMonoidHom = ⊥ := by
        rw [abstractPlaneProduct]
        rw [h2]
        exact hbot
      have h6 : abstractPlaneProduct p AB tB = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).mp h5
      rw [show (t : MulAut (coordinateG K)) = (tB : MulAut (coordinateG K)) from rfl, h1]
      rw [abstractPlaneProduct] at h6
      rw [h6, Subgroup.map_bot]

end KCLinearTwo

end CFSG.RankThree.PartOne
