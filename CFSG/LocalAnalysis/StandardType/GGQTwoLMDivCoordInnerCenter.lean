module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

theorem qTwoLMDivCoordInner_center_scalar {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {m : ℕ} (hm : 4 ≤ m) {u : Su F0 2 1 m}
    (hu : u ∈ Subgroup.center (Su F0 2 1 m)) :
    ∃ c : F0, ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => c := by
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  have hu2 : (u : GL (Fin m) F0) ∈ StatedSU m (2 ^ 1) F0 := by
    rw [← SUid_eq_statedSU hK m]; exact u.2
  let u' : ↥(StatedSU m (2 ^ 1) F0) := ⟨(u : GL (Fin m) F0), hu2⟩
  have hcenter' : u' ∈ Subgroup.center ↥(StatedSU m (2 ^ 1) F0) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_center_iff] at hu
    have hg : (g : GL (Fin m) F0) ∈ SUid (unitaryInvolution F0 2 1) m := by
      rw [SUid_eq_statedSU hK m]; exact g.2
    refine Subtype.coe_injective.eq_iff.mp ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg Subtype.val (hu ⟨(g : GL (Fin m) F0), hg⟩)
  have hsc := center_statedSU_le_scalars hK hm hcenter'
  obtain ⟨c, hc⟩ : (u : GL (Fin m) F0) ∈ StatedScalars (Fin m) F0 := hsc
  refine ⟨(c : F0), ?_⟩
  rw [← hc]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]

theorem qTwoLMDivCoordInner_scalar_central {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ} {u : Su F0 2 1 m} {c : F0}
    (hu : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => c) :
    u ∈ Subgroup.center (Su F0 2 1 m) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  have h1 : (((g * u : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := rfl
  have h2 : (((u * g : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := rfl
  rw [h1, h2, hu, ← Matrix.scalar_apply]
  exact ((Matrix.scalar_commute c (fun r => Commute.all c r) _).eq).symm

end CFSG.StandardType.QTwo

end
