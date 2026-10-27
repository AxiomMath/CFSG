module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]

structure FS79Hyp (b t b₁ b₂ : H) (J : Subgroup H) : Prop where
  ord_b : orderOf b = 3
  ord_t : orderOf t = 2
  inv_b : t * b * t⁻¹ = b⁻¹
  J_perm : Nonempty (↥J ≃* Equiv.Perm (Fin 6))
  J_le_cen_b : J ≤ Cen b
  J_le_cen_t : J ≤ Cen t
  N_le_NJ : Nor (Subgroup.zpowers b) ≤ Nor J
  N_eq : setMul (Opp 3 (Nor (Subgroup.zpowers b))) (Subgroup.closure {b, t} ⊔ J) =
    Nor (Subgroup.zpowers b)
  b₁_mem : b₁ ∈ J
  b₂_mem : b₂ ∈ J
  E9 : IsElemAb 3 2 (Subgroup.closure {b₁, b₂})
  mono : ∀ n ∈ J ⊓ Nor (Subgroup.closure {b₁, b₂}), ∀ x ∈ ({b₁, b₂} : Set H),
    n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H)
  N_bi : ∀ x ∈ ({b₁, b₂} : Set H),
    setMul (Opp 3 (Nor (Subgroup.zpowers x)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers x)) = Nor (Subgroup.zpowers x)
  no_two : ∀ R : Subgroup H, IsPGroup 2 R → Subgroup.closure {b, b₁, b₂} ≤ Nor R → R = ⊥
  weak : ∀ h : H, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
    conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b

variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.cen_le_nor (h : FS79Hyp b t b₁ b₂ J) :
    Cen b ≤ Nor (Subgroup.zpowers b) := by
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hx : Commute x b) k).eq.symm

end CFSG.RankThree.PartTwo.Sec21.FF81