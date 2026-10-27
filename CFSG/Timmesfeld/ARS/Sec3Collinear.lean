module

public import CFSG.Timmesfeld.ARS.Sec3Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

theorem not_opposite_of_isPGroup_sup [Finite G] (hR : IsRootClass R) {E D : Subgroup G}
    (hE : E ∈ R) (hD : D ∈ R) (h : IsPGroup 2 ↥(E ⊔ D)) : ¬ Opposite E D := by
  intro hop
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD
  have hodd := hop.odd_orderOf_mul (hR.mul_self E hE) he he1 hd hd1
  have h1 := eq_one_of_odd_orderOf_of_isPGroup h
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hd)) hodd
  have hmem : e ∈ E ⊓ D := ⟨he, by rw [eq_inv_of_mul_eq_one_left h1]; exact D.inv_mem hd⟩
  rw [hop.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact he1 hmem

theorem isPGroup_sup_sup_of_not_opposite [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B D : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hD : D ∈ R) (hAB : Commuting A B)
    (hAD : ¬ Opposite A D) (hBD : ¬ Opposite B D) : IsPGroup 2 ↥(A ⊔ B ⊔ D) := by
  have hA2 := hR.isPGroup hA
  have hB2 := hR.isPGroup hB
  have hD2 := hR.isPGroup hD
  have hspec : ∀ {X : Subgroup G}, X ∈ R → ¬ Commuting X D → ¬ Opposite X D → Special R X D := by
    intro X hX hc ho
    have hne : X ≠ D := fun e => hc (e ▸ hR.commuting_self hX)
    rcases hR.rel X hX D hD hne with h | h | h
    · exact absurd h hc
    · exact absurd h ho
    · exact h
  by_cases hcA : Commuting A D <;> by_cases hcB : Commuting B D
  · exact isPGroup_sup_of_commuting (isPGroup_sup_of_commuting hA2 hB2 hAB) hD2
      (Commuting.sup_left hcA hcB)
  · rw [sup_assoc]
    exact isPGroup_sup_of_commuting hA2 (Special.isPGroup_sup hR hB hD (hspec hB hcB hBD))
      (Commuting.sup_right hAB hcA)
  · rw [sup_comm A B, sup_assoc]
    exact isPGroup_sup_of_commuting hB2 (Special.isPGroup_sup hR hA hD (hspec hA hcA hAD))
      (Commuting.sup_right hAB.symm hcB)
  · have := isPGroup_sup_of_special_special hR hiso hA hD hB (hspec hA hcA hAD)
      (hspec hB hcB hBD).symm hAB
    rwa [sup_assoc, sup_comm D B, ← sup_assoc] at this

theorem setOf_opposite_conjSub (hR : IsRootClass R) (X : Subgroup G) (g : G) :
    {D | D ∈ R ∧ Opposite (conjSub X g) D} =
      (fun D => conjSub D g) '' {D | D ∈ R ∧ Opposite X D} := by
  ext D
  constructor
  · rintro ⟨hD, hop⟩
    refine ⟨conjSub D g⁻¹, ⟨hR.conjSub_mem hD g⁻¹, ?_⟩, ?_⟩
    · have := Opposite.conj hop g⁻¹
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    · change conjSub (conjSub D g⁻¹) g = D
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  · rintro ⟨D', ⟨hD', hop⟩, rfl⟩
    exact ⟨hR.conjSub_mem hD' g, Opposite.conj hop g⟩

end Sec3

open Sec3

theorem not_subset_centralSet_union_psiSet [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ lambdaSet R A) :
    ¬ (centralSet R A ∪ psiSet R A ⊆ centralSet R B ∪ psiSet R B) := by
  intro h
  have hBR : B ∈ R := hB.1.1
  have hO : ∀ D ∈ R, Opposite B D → Opposite A D := by
    intro D hD hBD
    by_contra hAD
    have hmem : D ∈ centralSet R A ∪ psiSet R A := by
      by_cases hc : Commuting A D
      · exact Or.inl ⟨hD, hc⟩
      · right
        refine ⟨hD, ?_⟩
        have hne : A ≠ D := fun e => hc (e ▸ hR.commuting_self hA)
        rcases hR.rel A hA D hD hne with h' | h' | h'
        · exact absurd h' hc
        · exact absurd h' hAD
        · exact h'
    rcases h hmem with ⟨-, hc⟩ | ⟨-, hs⟩
    · exact hBD.not_commuting (hR.ne_bot B hBR) hc
    · exact Special.not_opposite hR hBR hs hBD
  have hOE : ∀ E ∈ R, E ≤ A ⊔ B → ∀ D ∈ R, Opposite E D → Opposite A D := by
    intro E hE hEle D hD hED
    by_contra hAD
    have hBD : ¬ Opposite B D := fun h' => hAD (hO D hD h')
    have hp := isPGroup_sup_sup_of_not_opposite hR hiso hA hBR hD hB.1.2.2 hAD hBD
    exact not_opposite_of_isPGroup_sup hR hE hD (hp.to_le (sup_le_sup_right hEle D)) hED
  have hOeq : ∀ E ∈ R, E ≤ A ⊔ B →
      {D | D ∈ R ∧ Opposite E D} = {D | D ∈ R ∧ Opposite A D} := by
    intro E hE hEle
    obtain ⟨-, E', -, F', -, -, -, htrans, -⟩ := line_card_and_transitive hR hiso hA hB
    obtain ⟨x, -, rfl⟩ := htrans A hA le_sup_right E hE (sup_comm A B ▸ hEle)
    have hsub : {D | D ∈ R ∧ Opposite (conjSub A x) D} ⊆ {D | D ∈ R ∧ Opposite A D} :=
      fun D hD => ⟨hD.1, hOE _ hE hEle D hD.1 hD.2⟩
    have hcard : ({D | D ∈ R ∧ Opposite (conjSub A x) D} : Set (Subgroup G)).ncard =
        ({D | D ∈ R ∧ Opposite A D} : Set (Subgroup G)).ncard := by
      rw [setOf_opposite_conjSub hR A x]
      exact Set.ncard_image_of_injective _ fun D D' h => map_conj_inj.1 h
    exact Set.eq_of_subset_of_ncard_le hsub hcard.ge
  obtain ⟨C, hC, hAC⟩ := hiso A hA
  obtain ⟨B₀, ⟨hB₀R, hB₀le, hB₀p⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hC hAC hB
  have hmem : C ∈ {D | D ∈ R ∧ Opposite B₀ D} := by
    rw [hOeq B₀ hB₀R hB₀le]
    exact ⟨hC, hAC⟩
  exact Special.not_opposite hR hC hB₀p.2 hmem.2.symm

end CFSG.Timmesfeld.ARS
