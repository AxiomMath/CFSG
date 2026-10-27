module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Inputs
import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem asch54_almostSimple (hC2 : Asch54Chev2) (hAl : Asch54Alt) (hSp : Asch54Spor)
    (hCO : Asch54ChevOdd) (hA : Asch80ThmA54) (hON : Asch54ONGen)
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} (hK : CFSG.Open.IsKGroup Q)
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hL0 : ¬ IsCalL0 ↥L) (hT : IsSylowIn 2 T ⊤) :
    lGen IsCalL0 ⊤ T = ⊤ ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
          1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) ∧
          ¬ Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.ON)) ∨
      (∃ M : Subgroup Q, M < ⊤ ∧ (∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) ∧
          ¬ HasCompFactor M IsCalL0 ∧ Shape54 ⊤ T L) := by
  by_cases hO : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.ON)
  · exact Or.inl (hON Q L T hLn hO hC hT)
  by_cases hu : HasUniqueMaxOver T
  · obtain ⟨M, hM, hMax⟩ := hu
    rcases hA Q L T M hK hLn hLs hnab hC hL0 hT hM hMax with
      ⟨p, hp, hp2, h3, h1⟩ | ⟨hM0, hsh⟩
    · exact Or.inr (Or.inl ⟨p, hp, hp2, h3, h1, hO⟩)
    · exact Or.inr (Or.inr ⟨M, hM, hMax, hM0, hsh⟩)
  haveI := hLs
  have hcat : CFSG.Open.IsCatalogGroup ↥L :=
    (hK.of_injective L.subtype L.subtype_injective).isCatalogGroup_of_surjective ⊤ hnab
      (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have key : ∀ {P : ∀ (X : Type) [Group X], Prop}, Asch54Case P → P ↥L →
      lGen IsCalL0 ⊤ T = ⊤ ∨
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
            1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) ∧
            ¬ Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.ON)) ∨
        (∃ M : Subgroup Q, M < ⊤ ∧ (∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) ∧
            ¬ HasCompFactor M IsCalL0 ∧ Shape54 ⊤ T L) := by
    intro P hc hP
    rcases hc Q L T hK hLn hLs hnab hC hP hL0 hT hu with h1 | ⟨p, hp, hp2, h3, h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨p, hp, hp2, h3, h1, hO⟩)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
      obtain ⟨a, b, hab⟩ := hnab
      exact absurd (e.injective (by
        rw [map_mul, map_mul]
        exact mul_comm (G := Multiplicative (ZMod p)) _ _)) hab
  | alternating n hn => exact key hAl ⟨n, hn, ⟨e⟩⟩
  | lie d =>
      rcases CFSG.Models.oddLieType_or_evenLieType_of_valid d ⟨e⟩ with h | h
      · exact key hCO h
      · exact key hC2 h
  | sporadic s => exact key hSp ⟨s, ⟨e⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
