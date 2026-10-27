module

public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.KE


@[expose] def F4CoreStep (K : Type) [Field K] [Finite K] (p : ℕ) (L : Type) [Field L]
    [Algebra K L] : Prop :=
  ∀ {B : Subgroup (MulAut (adjointGroup .F4 K))},
    (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B →
    ∀ {x : adjointGroup .F4 K} (c : adjointGroup .F4 K) (g0 : ModGL .F4 L),
      g0 ∈ adjointGroup .F4 L →
      ∀ (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L),
        Function.Injective ψ →
        (∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0) →
        ∀ {Pt : Subgroup (ModGL .F4 L)}, CFSG.IsQuasisimple Pt → ⁅ψ.range, ψ.range⁆ = Pt →
        ∀ (i : Fin Tag.F4.rank),
          ((i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3)) →
          ∀ (h₀ : ModGL .F4 L), h₀ ∈ adjointGroup .F4 L →
          (∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) →
          (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))),
            V.Normal → Group.IsSolvable V → Odd (Nat.card V)) →
          Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .F4 K))} :
              Set (MulAut (adjointGroup .F4 K))))))

theorem four_le_or_eq_three_of_ne_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) :
    4 ≤ ℓ ^ f ∨ ℓ ^ f = 3 := by
  have h3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have := Nat.le_self_pow (by omega : f ≠ 0) ℓ
  omega

end CFSG.RankThree.PartOne.KF4
