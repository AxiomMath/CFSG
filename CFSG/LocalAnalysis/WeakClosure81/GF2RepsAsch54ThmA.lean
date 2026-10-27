module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Inputs
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def Asch80ThmA54Case (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T M : Subgroup Q), CFSG.Open.IsKGroup Q → L.Normal →
    IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
    Subgroup.centralizer (L : Set Q) = ⊥ → P ↥L → ¬ IsCalL0 ↥L → IsSylowIn 2 T ⊤ →
    M < ⊤ → (∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) →
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
        1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T)) ∨
      (¬ HasCompFactor M IsCalL0 ∧ Shape54 ⊤ T L)

theorem asch80ThmA54Case_of_forall {P : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), CFSG.Open.IsKGroup Q → L.Normal →
      IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
      Subgroup.centralizer (L : Set Q) = ⊥ → P ↥L → ¬ IsCalL0 ↥L → IsSylowIn 2 T ⊤ →
      lGen IsCalL0 ⊤ T = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
          1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T)) :
    Asch80ThmA54Case P := by
  intro Q _ _ L T M hK hLn hLs hnab hC hP hL0 hT hM hMax
  rcases h Q L T hK hLn hLs hnab hC hP hL0 hT with hgen | h2
  · exfalso
    have hle : lGen IsCalL0 ⊤ T ≤ M := iSup₂_le fun X hX => hMax X hX.1 hX.2.1
    rw [hgen] at hle
    exact hM.ne (le_antisymm le_top hle)
  · exact Or.inl h2

theorem asch80ThmA54_of_cases
    (hC2 : Asch80ThmA54Case fun X _ => CFSG.Models.EvenLieType X)
    (hAl : Asch80ThmA54Case fun X _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)))
    (hSp : Asch80ThmA54Case fun X _ => CFSG.Models.SporadicRep X)
    (hCO : Asch80ThmA54Case fun X _ => CFSG.Models.OddLieType X) : Asch80ThmA54 := by
  intro Q _ _ L T M hK hLn hLs hnab hC hL0 hT hM hMax
  haveI := hLs
  have hcat : CFSG.Open.IsCatalogGroup ↥L :=
    (hK.of_injective L.subtype L.subtype_injective).isCatalogGroup_of_surjective ⊤ hnab
      (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
      obtain ⟨a, b, hab⟩ := hnab
      exact absurd (e.injective (by
        rw [map_mul, map_mul]
        exact mul_comm (G := Multiplicative (ZMod p)) _ _)) hab
  | alternating n hn => exact hAl Q L T M hK hLn hLs hnab hC ⟨n, hn, ⟨e⟩⟩ hL0 hT hM hMax
  | lie d =>
      rcases CFSG.Models.oddLieType_or_evenLieType_of_valid d ⟨e⟩ with h | h
      · exact hCO Q L T M hK hLn hLs hnab hC h hL0 hT hM hMax
      · exact hC2 Q L T M hK hLn hLs hnab hC h hL0 hT hM hMax
  | sporadic s => exact hSp Q L T M hK hLn hLs hnab hC ⟨s, ⟨e⟩⟩ hL0 hT hM hMax

end CFSG.LocalAnalysis.WeakClosure81

end
