module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3IrrCyc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3IrrHess
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer

public section

namespace CFSG.Quasithin.A312U3

open CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory CFSG.Quasithin.A38c15

variable {K : Type} [Field K] [Finite K]

theorem solvable_or_quasisimple_gl3 {G : Subgroup (GL (Fin 3) K)}
    (hG : IsIrreducibleMatrixRep G.subtype) :
    Group.IsSolvable ↥G ∨
      ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ CFSG.IsQuasisimple H ∧
        IsIrreducibleMatrixRep H.subtype ∧
        (∀ M : Matrix (Fin 3) (Fin 3) K,
          (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
            ∃ c : K, M = Matrix.scalar (Fin 3) c) ∧
        (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) ∧ Nat.card (Subgroup.center H) ∣ 3 := by
  rcases irreducible_gl3_reduction hG with ⟨H, hHG, hnorm, hirr, hcyc, -, -⟩ | hmono |
    ⟨-, H, hHG, hnorm, hirr, hcard, hext⟩ | h
  · exact Or.inl (isSolvable_of_cyclic_normal_K hHG hnorm hirr hcyc)
  · exact Or.inl (isSolvable_of_isTransitiveMonomial hmono)
  · exact Or.inl (isSolvable_of_extraspecial27_normal_K hHG hnorm hirr (by rw [hcard]; norm_num)
      hext)
  · exact Or.inr h

end CFSG.Quasithin.A312U3
