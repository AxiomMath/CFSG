module

public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

namespace Ronan134Q

omit [Finite G] in
theorem le_normalizer_sup_of_commutator_le {R R' O : Subgroup G}
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) (hRR' : ⁅R, R'⁆ ≤ O) :
    R ≤ Subgroup.normalizer ((R' ⊔ O : Subgroup G) : Set G) := by
  have key : ∀ g ∈ R, ∀ x ∈ R' ⊔ O, g * x * g⁻¹ ∈ R' ⊔ O := by
    intro g hg x hx
    have hle : R' ⊔ O ≤ (R' ⊔ O).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · have hc : ⁅g, y⁆ ∈ O := hRR' (Subgroup.commutator_mem_commutator hg hy)
        have he : (MulAut.conj g).toMonoidHom y = ⁅g, y⁆ * y := by
          rw [commutatorElement_def]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        show (MulAut.conj g).toMonoidHom y ∈ R' ⊔ O
        rw [he]
        exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hRO hg) y).mp hy)
    exact hle hx
  intro r hr
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key r hr x, fun hx => ?_⟩
  have h := key r⁻¹ (inv_mem hr) _ hx
  simpa [mul_assoc] using h

end Ronan134Q

end CFSG.RankThree.PartTwo.Sec14
