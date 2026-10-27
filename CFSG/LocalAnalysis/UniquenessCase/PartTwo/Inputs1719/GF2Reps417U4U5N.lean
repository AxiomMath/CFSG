module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Sp4G2NPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UnitaryParabolicU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UnitaryParabolicU5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Normal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem bParam_le_three_mul_of_isU4
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hn : 2 ≤ n) (hU4 : IsU4 ↥L n) : bParam L Y ≤ 3 * n := by
  have hU := k_U4ParabolicGen_holds
  obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hL2₁, hL2₂, hgen, hinv⟩ :=
    hU ↥L n hn hU4 _ (isSylowTwoOf_subgroupOf_inf hcomp hsyl)
  exact bParam_le_of_pair_of_aut_inv hW hLT hcomp hsyl hO2 hfix hgen hperf₁ hperf₂
    (Or.inl hL2₁) (Or.inl hL2₂) hinv (by omega)

theorem bParam_le_three_mul_of_isU5
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hn : 2 ≤ n) (hU5 : IsU5 ↥L n) : bParam L Y ≤ 3 * n := by
  have hU := k_U5ParabolicGen_holds
  obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hSU₁, hL2₂, hgen, hinv⟩ :=
    hU ↥L n hn hU5 _ (isSylowTwoOf_subgroupOf_inf hcomp hsyl)
  exact bParam_le_of_pair_of_aut_inv hW hLT hcomp hsyl hO2 hfix hgen hperf₁ hperf₂
    (Or.inr (Or.inr hSU₁)) (Or.inl hL2₂) hinv (by omega)

theorem w4Lem4_17U4U5N_holds :
    W4Lem4_17U4U5N := by
  intro W _ _ hW Y L T n hLY hTY hLT hcomp hsyl hfix hodd hTN hn hU
  refine bParam_le_of_noO2_of_normal (P := fun X _ => IsU4 X n ∨ IsU5 X n)
    (hP := fun {X X'} _ _ e hh => hh.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e))
    (B := 3 * n) ?_ hW hLY hTY hLT hcomp hsyl hfix hodd hTN hU
  intro U _ _ hu Y' L' T' hLT' hcomp' hsyl' hO2' hfix' _hTN' hPL
  rcases hPL with hU4 | hU5
  · exact bParam_le_three_mul_of_isU4 hu hLT' hcomp' hsyl' hO2' hfix'
      (by omega) hU4
  · exact bParam_le_three_mul_of_isU5 hu hLT' hcomp' hsyl' hO2' hfix'
      (by omega) hU5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
