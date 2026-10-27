module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_weylTuple (u : WeylGroup τ) (b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (fun k => rootChar b (u⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ))) v =
      rootChar b (u⁻¹ • v) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : u⁻¹ • v = ∑ i, v i • (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm u⁻¹ (v i) _
  conv_lhs => rw [hv, rootChar_sum]
  rw [hw, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, CTTorus.rootChar_single]

theorem exists_rootDiagUnit_conj
    (u : WeylGroup τ) (b : Fin τ.rank → Lˣ) :
    ∃ b' : Fin τ.rank → Lˣ,
      rootDiagUnit τ b' = canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) L u)⁻¹ ∧
      ∀ v : Fin τ.rank → ℤ, rootChar b' (u • v) = rootChar b v := by
  refine ⟨fun k => rootChar b (u⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)), ?_, fun v => ?_⟩
  · rw [rootDiagUnit_eq_conj_canonicalRep_iff]
    intro v
    rw [rootChar_weylTuple, inv_smul_smul]
  · rw [rootChar_weylTuple, inv_smul_smul]

end CFSG.RankThree.PartOne.KEXC
