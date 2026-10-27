module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeInvol
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsC
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat3
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat4
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi2
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGExc_latticeAt_E6phi
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup Tag.E6 K)} (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : ExcFrame Tag.E6 K p E) (hpq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest Tag.E6 F.w) :
    GGKGLatticeAt p E := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ζu, hζu⟩ :=
    CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
      (by norm_num) hp (by omega)
  let ζ : (AlgebraicClosure K)ˣ := ζu
  have hζ : IsPrimitiveRoot ζ p := hζu
  refine ⟨4, ggKGEp_Q4, ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq,
    ggKGEp_Q4_form, ggKGEp_pi_surjective hp hp5 F hFr hΦ ζ hζ hlong hpq, ?_⟩
  intro w₀ hrefl
  obtain ⟨v, hv, hv2, hactV⟩ :=
    ggKGEp_normalizer_data hp hp5 F hFr hΦ ζ hζ hlong hpq hrefl
  have hvcomm : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v := by
    have h := (Subgroup.mem_centralizer_iff.mp hv) F.w (Set.mem_singleton F.w)
    rw [ggKGEp_eq_w0_of_longest hlong] at h
    exact h.symm
  obtain ⟨w, hwroot, hwformula⟩ :=
    ggKGLat_involution_isRoot hp (by omega) ggKGEp_Q4_form (ggKGEp_mat4 v)
      (ggKGEp_mat4_invariant hvcomm) (ggKGEp_mat4_mul_self hvcomm hv2)
      (ggKGEp_fix_count hp hp5 F hFr hΦ ζ hζ hlong hpq hrefl v hactV) (by norm_num)
  refine ⟨w, hwroot, fun y => ?_⟩
  rw [← hwformula y]
  exact hactV y

end CFSG.StandardType

end
