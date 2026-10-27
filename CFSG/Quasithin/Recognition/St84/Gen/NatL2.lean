module

public import CFSG.Quasithin.Recognition.St84.Gen.NatL2Push
import CFSG.Quasithin.Recognition.St84.Gen.NatL2Module
import CFSG.Quasithin.Recognition.St84.Gen.NatL2Sec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem natCoord_of_isL2Quot {X P Z : Subgroup G} (h : PushHyp X P Z) {n : ℕ} (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥X)) (hJ : ¬ thompsonJ P ≤ pCoreOf 2 X) :
    ∃ (α : ↥X →* SL(2, GaloisField 2 n))
      (β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → GaloisField 2 n)),
      Function.Surjective α ∧
      α.ker = Subgroup.centralizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X) ∧
      Function.Surjective β ∧
      (∀ (x : ↥X) (v v' : ↥(Z.subgroupOf X)), (v' : ↥X) = x * v * x⁻¹ →
        Multiplicative.toAdd (β v') =
          (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd (β v))) ∧
      β.ker = (Subgroup.centralizer
        ((oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X)).subgroupOf
          (Z.subgroupOf X) :=
  exists_natCoord_of_pushHyp
    (fun hn _ _ _ hF _ _ _ _ _ ρ hfix A _ hA hoff =>
      exists_natural_of_offender hn hF ρ hfix A hA hoff) h hn hq hJ

theorem baumannC_of_isL2Quot {X P Z : Subgroup G} (h : PushHyp X P Z) {n : ℕ} (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥X)) (hJ : ¬ thompsonJ P ≤ pCoreOf 2 X)
    (hnc : NoCharNormal P X) : BaumannC X Z := by
  obtain ⟨α, β, hα, hαk, hβ, hβe, hβk⟩ := natCoord_of_isL2Quot h hn hq hJ
  exact baumannC_of_natCoord h α β hα hαk hβ hβe hβk hnc

theorem cor42_of_isL2Quot {X P Z : Subgroup G} (h : PushHyp X P Z) {n : ℕ} (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥X)) (hJ : ¬ thompsonJ P ≤ pCoreOf 2 X)
    (hnc : NoCharNormal P X) {H₀ : Subgroup G} (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    (∀ g ∈ H₀, cj g Z ≤ pCoreOf 2 X) ∧ conjJoinOf H₀ Z ≤ pCoreOf 2 X ∧
      (P ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) →
        X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G)) := by
  obtain ⟨α, β, hα, hαk, hβ, hβe, hβk⟩ := natCoord_of_isL2Quot h hn hq hJ
  exact cor42_of_natCoord h α β hα hαk hβ hβe hβk hnc hH₀ hodd

end CFSG.Quasithin.St84
