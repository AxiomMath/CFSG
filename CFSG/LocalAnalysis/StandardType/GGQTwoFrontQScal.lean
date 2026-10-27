module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Open Matrix

private theorem qTwoFrontQ_scal_center {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (h4 : 4 ≤ n) {u : Su K 2 f n}
    (hu : u ∈ Subgroup.center (Su K 2 f n)) :
    ∃ c : K, ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun _ => c) := by
  have hu2 : (u : GL (Fin n) K) ∈ StatedSU n (2 ^ f) K := by
    rw [← SUid_eq_statedSU hK n]; exact u.2
  let u' : ↥(StatedSU n (2 ^ f) K) := ⟨(u : GL (Fin n) K), hu2⟩
  have hcenter' : u' ∈ Subgroup.center ↥(StatedSU n (2 ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_center_iff] at hu
    have hg : (g : GL (Fin n) K) ∈ SUid (unitaryInvolution K 2 f) n := by
      rw [SUid_eq_statedSU hK n]; exact g.2
    refine Subtype.coe_injective.eq_iff.mp ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg Subtype.val (hu ⟨(g : GL (Fin n) K), hg⟩)
  have hsc := center_statedSU_le_scalars hK h4 hcenter'
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hsc
  obtain ⟨c, hc⟩ := hsc
  refine ⟨(c : K), ?_⟩
  have hu_eq : (u : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
  rw [hu_eq, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

set_option linter.unusedVariables false in
theorem qTwoFrontQ_ker_scalar {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (h4 : 4 ≤ n) {G : Type} [Group G]
    {ψ : Su K 2 f n →* G} (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {z : Su K 2 f n}
    (hz : ψ z = 1) :
    ∃ c : K, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun _ => c) :=
  qTwoFrontQ_scal_center hK h4 (hker (MonoidHom.mem_ker.mpr hz))

end CFSG.StandardType.QTwo

end
