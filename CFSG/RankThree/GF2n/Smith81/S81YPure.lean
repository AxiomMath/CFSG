module

public import CFSG.RankThree.GF2n.Smith81.S81U6Pure
public import CFSG.RankThree.GF2n.Smith81.S81RPure

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem rho_sub_one_mem_RootPt_or_eq_zero [CharP K 2] {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6)
    (ht : IsTransvec K g) {ξ : Cube K} (hξ : ξ ∈ RootPt σ) :
    (rho K g - 1) ξ ∈ RootPt σ ∨ (rho K g - 1) ξ = 0 := by
  by_cases h0 : (rho K g - 1) ξ = 0
  · exact Or.inr h0
  · refine Or.inl ⟨?_, h0, isPure_rho_sub_one ht hξ.2.2⟩
    rw [mem_Wsub_iff, LinearMap.sub_apply, Module.End.one_apply, map_sub, theta_rho hg,
      mem_Wsub_iff.mp hξ.1]

end CFSG.RankThree.GF2n.Smith81.U6Cube
