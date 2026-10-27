module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggNbrExcPlusRank : LargeEvenLieTag → ℕ
  | .F4 => 3
  | .E7 => 6
  | .E8 => 7
  | _ => 0

section Main

theorem ggTorusLift_E7Plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    GGTorusLift p 6 (TableBExc.RecipeGroup .E7 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
    (GGPlusLiftTorus.ggTorusLift_of_commutingSL2 hp hp2 hpq
      (TableBExcTwo.rho K TableBExcTwo.frameE7) (TableBExcTwo.rho_injective TableBExcTwo.frameE7)
      (fun i j h => TableBExcTwo.commute_rho TableBExcTwo.frameE7 h))

theorem ggTorusLift_E8Plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    GGTorusLift p 7 (TableBExc.RecipeGroup .E8 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
    (GGPlusLiftTorus.ggTorusLift_of_commutingSL2 hp hp2 hpq
      (TableBExcTwo.rho K TableBExcTwo.frameE8) (TableBExcTwo.rho_injective TableBExcTwo.frameE8)
      (fun i j h => TableBExcTwo.commute_rho TableBExcTwo.frameE8 h))

theorem ggTorusLift_F4Plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    GGTorusLift p 3 (TableBF4.RecipeGroup K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBF4.recipeEquiv K)
    (GGPlusLiftTorus.ggTorusLift_of_commutingSL2 hp hp2 hpq
      (TableBF4Two.rho K) TableBF4Two.rho_injective
      (fun i j h => TableBF4Two.commute_rho h))

theorem largeEvenLabelAll_torusLift_excPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (ggNbrExcPlusRank lab.tag) R := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_E7Plus hp hp2 hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_E8Plus hp hp2 hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_F4Plus hp hp2 hpq⟩

end Main

end CFSG.StandardType

end
