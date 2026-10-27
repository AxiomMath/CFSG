module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveOne
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveNormal
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveComm
public import CFSG.LocalAnalysis.WeakClosure81.W15Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

section Certified


namespace FourteenFive

variable {G : Type} [Group G] [Finite G] {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem fourteen_five (h15 : Hyp15 M V₀ V) (hO : InCalO1 n M V₀ V g)
    (hc : ¬ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ ≤ V₀) :
    (E3.mQuot V (conjSubgroup M g) = 1 ∧ rMV M V = (mSub V₀ : ℕ∞)) ∧
      (M ≤ normalizer ((V₀ ⊓ conjSubgroup M g : Subgroup G) : Set G) ∧
        ⁅F11.CTilde M V₀ V, V⁆ ≤ V₀ ⊓ conjSubgroup M g) := by
  have h := hyp65_of_hyp15 h15 hO
  have hV₀K := not_V₀_le_K h hc
  have h1 := fourteen_five_one h15 hO hc
  have hn := relIndex_U_eq_two h h1.1
  have hD := le_normalizer_Z0 h15 h hV₀K hn
  have hD' : M ≤ normalizer ((V₀ ⊓ conjSubgroup M g : Subgroup G) : Set G) := by
    simpa only [Z0Of] using hD
  exact ⟨h1, hD', commutator_cTilde_le h15 h hV₀K hn hD⟩

end FourteenFive

theorem w15Thm145_holds (G : Type) [Group G] [Finite G] : W15Thm145 G := by
  intro M V₀ V h15 g hO hc
  exact FourteenFive.fourteen_five h15 hO hc

end Certified

end CFSG.LocalAnalysis.WeakClosure81
