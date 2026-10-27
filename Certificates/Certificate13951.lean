module

public import CFSG.RankThree.Asc83Table.M22
public import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquaresInputs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.WittDesign
open CFSG.RankThree.Asc83Table (Automizer automizerCongr automizerOfEq)
open CFSG.RankThree.Asc83Table.M22 (x y X Y E GI)
open CFSG.RankThree.PartTwo (invariantPiSubgroups maxInvariantPiSubgroups piCompl piOf)
open CFSG.RankThree.PartTwo.Sec4.Sporadic (map_symm_map map_map_symm image_maxInvariantPiSubgroups
  map_mem_invariantPiSubgroups_iff)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

private theorem cert13951_0 :
    ∀ i : Fin 4, (GI : Perm (Fin 22)) * line i * (GI : Perm (Fin 22))⁻¹ ≠
        line i ∧ (GI : Perm (Fin 22)) * line i * (GI : Perm (Fin 22))⁻¹ ≠ line i ^ 2 := by
  decide +kernel

private theorem cert13951_1 : ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ k l : Fin 4,
    (GI : Perm (Fin 22)) ^ (k : ℕ) * (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ) *
        (X : Perm (Fin 22)) *
      ((GI : Perm (Fin 22)) ^ (k : ℕ) *
        (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ))⁻¹ =
      (X : Perm (Fin 22)) ^ (a : ℕ) * (Y : Perm (Fin 22)) ^ (b : ℕ) := by
  decide +kernel

end CFSG.RankThree.PartTwo.KFacts.KP4

namespace Certificates

open Equiv in
open CFSG.RankThree.Asc83Table.M22 (x y X Y E GI) in
open CFSG.RankThree.PartTwo.KFacts.KP4 in
theorem certificate13951 : (
    ∀ i : Fin 4, (GI : Perm (Fin 22)) * line i * (GI : Perm (Fin 22))⁻¹ ≠
        line i ∧ (GI : Perm (Fin 22)) * line i * (GI : Perm (Fin 22))⁻¹ ≠ line i ^ 2
  ) ∧ (
    ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ k l : Fin 4,
      (GI : Perm (Fin 22)) ^ (k : ℕ) * (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ) *
          (X : Perm (Fin 22)) *
        ((GI : Perm (Fin 22)) ^ (k : ℕ) *
          (CFSG.RankThree.Asc83Table.M22.GJ : Perm (Fin 22)) ^ (l : ℕ))⁻¹ =
        (X : Perm (Fin 22)) ^ (a : ℕ) * (Y : Perm (Fin 22)) ^ (b : ℕ)
  ) := by
  exact ⟨CFSG.RankThree.PartTwo.KFacts.KP4.cert13951_0,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert13951_1⟩

end Certificates
