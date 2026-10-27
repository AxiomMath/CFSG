module

public import CFSG.LocalAnalysis.StandardType.GGReflCentralLift
public import CFSG.RankThree.PartOne.KF4.A2FrameToral
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.RankThree.PartOne.SRC.ProductCover
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


theorem exists_conj_torus_of_a2_frames_of_reflection
    {τ : Tag} {L : Type} [Field L]
    {ψ ψ' : SL(3, L) →* ModGL τ L} {σ σ' : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' σ') (hc : ∀ A B, Commute (ψ A) (ψ' B))
    {ζ : L} (hζ : IsPrimitiveRoot ζ 9) {E : Subgroup (ModGL τ L)} [Finite E]
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E ≤ 3 ^ 3)
    (hEμ : E ≤ (ψ.noncommCoprod ψ' hc).range)
    {w : ModGL τ L} (hwμ : w ∈ (ψ.noncommCoprod ψ' hc).range)
    (hr : GGKGIsReflAt 3 E w) {x : ModGL τ L} (hxE : x ∈ E) (hx : x ≠ 1)
    (hxc : x ∈ Subgroup.centralizer ((ψ.noncommCoprod ψ' hc).range : Set (ModGL τ L))) :
    ∃ g ∈ (ψ.noncommCoprod ψ' hc).range, ∀ y ∈ E, g⁻¹ * y * g ∈ torusGroup τ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfect : Group.IsPerfect (SL(3, L) × SL(3, L)) :=
    CFSG.RankThree.PartOne.SRC.isPerfect_prod
      (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := L) (by norm_num))
      (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := L) (by norm_num))
  have hcomm := ggKGIsReflAt_comap_commute_of_central_fixed (ψ.noncommCoprod ψ' hc)
    (hψ.ker_noncommCoprod_le_center hψ' hc) hperfect (by norm_num)
    hE hcard hEμ hwμ hr hxE hx hxc
  exact hψ.exists_conj_torus_of_comm_preimage hψ' hc hζ hE.2 hEμ hcomm

end CFSG.StandardType

end
