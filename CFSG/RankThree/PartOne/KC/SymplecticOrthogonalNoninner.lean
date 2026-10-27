module

public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

@[expose] def SymplecticNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (ℓ f r p : ℕ), StatedClassicalModel T .PSp r ℓ f →
    p.Prime → 3 < p → p ≠ ℓ →
    ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      ¬ A ≤ (MulAut.conj : T →* MulAut T).range →
      Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      (∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      (∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : T →* MulAut T).range → autPlaneProduct p B A t = ⊥)) ∧
      (r = 2 → ℓ = 2 → f = p → p = 5 ∧ ℓ ^ f = 32)

@[expose] def OrthogonalNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (c : StatedLieTag) (ℓ f n p : ℕ),
    (c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) → StatedClassicalModel T c n ℓ f →
    p.Prime → 3 < p → p ≠ ℓ →
    ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      ¬ A ≤ (MulAut.conj : T →* MulAut T).range →
      Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧
      (∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : T →* MulAut T).range → autPlaneProduct p B A t = ⊥)

theorem symplectic_noninner_actual_component_odd_action_of
    (h : SymplecticNoninnerPlaneLocalCoreOdd) : SymplecticNoninnerActualComponentOddAction := by
  intro G _ _ p ℓ f r hp hp3 hℓ hℓp hf hr E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  have hplane : PlaneLocalCoreOddIf p (L ⧸ center L)
      (fun A => ¬ A ≤ (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h (L ⧸ center L) ℓ f r p hmod hp hp3 hℓp.symm B hB A hAB hA hAcard hPA).2.2.2.2.2.2.1 t htA
        ht1).2.1
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp hp2
    hE hEcard htE ht1 hL hEL hSL hplane hcase
  exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, hnonfaith⟩

theorem orthogonal_noninner_actual_component_odd_action_of
    (h : OrthogonalNoninnerPlaneLocalCoreOdd) : OrthogonalNoninnerActualComponentOddAction := by
  intro G _ _ p ℓ f n hp hp3 hℓ hℓp c hc E hE hEcard t htE ht1 L hL hmod hEL hSL hcase
  have hp2 : p ≠ 2 := by omega
  have hplane : PlaneLocalCoreOddIf p (L ⧸ center L)
      (fun A => ¬ A ≤ (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range) :=
    fun B hB A hAB hA hAcard hPA t htA ht1 =>
      ((h (L ⧸ center L) c ℓ f n p hc hmod hp hp3 hℓp.symm B hB A hAB hA hAcard hPA).2.2.2.2.2 t
        htA ht1).2.1
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane_if hp hp2
    hE hEcard htE ht1 hL hEL hSL hplane hcase
  exact ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, hnonfaith⟩

end CFSG.RankThree.PartOne
