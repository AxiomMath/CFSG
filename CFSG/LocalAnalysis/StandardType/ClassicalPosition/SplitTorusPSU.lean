module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5HypModel

public noncomputable section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

theorem exists_conj_isDiag_PSU
    {F : Type} [Field F] [Finite F] [CharP F 2] {f r p : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hr : 0 < r)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1)
    (E : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) (2 * r)))
    (hE : IsElemAbelian p E) (hcard : p ^ r ≤ Nat.card E) :
    ∃ g : ↥(Unitary.SU (unitaryInvolution F 2 f) (2 * r)),
      ∀ x ∈ E, (Unitary.SUExtras.mat _ _ (g * x * g⁻¹)).IsDiag := by
  have : Fact p.Prime := ⟨hp⟩
  let h : UnitaryFieldData 2 f F := TableBU.unitaryFieldData_of_card hF hf
  let e : hypSU h r 0 ≃* ↥(Unitary.SU (unitaryInvolution F 2 f) (2 * r)) :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  let D : Subgroup (hypSU h r 0) := E.map e.symm.toMonoidHom
  have hD : IsElemAbelian p D := ggIsElemAbelian_map hE e.symm.toMonoidHom
  have hcardD : p ^ r ≤ Nat.card D := by
    rw [show Nat.card D = Nat.card E from Subgroup.card_map_of_injective e.symm.injective]
    exact hcard
  obtain ⟨ζ, hζ⟩ := RelA5.exists_zeta_muSplit hF hpq
  have hζF : IsPrimitiveRoot ((ζ : Fˣ) : F) p := RelA5.isPrimitiveRoot_coe hζ
  obtain ⟨g0, hg0⟩ := exists_conj_hypEntries h hp hp2 hpq hζF hr D hD hcardD
  refine ⟨e g0, ?_⟩
  intro x hx
  have hxD : e.symm x ∈ D := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨t, ht⟩ := hg0 (e.symm x) hxD
  have hcoe := SuSplitRootGen.coe_hypSUEquiv h (by decide)
    (g0 * e.symm x * g0⁻¹)
  have he : e (g0 * e.symm x * g0⁻¹) = e g0 * x * (e g0)⁻¹ := by simp
  rw [he] at hcoe
  change (((e g0 * x * (e g0)⁻¹ : ↥(Unitary.SU (unitaryInvolution F 2 f) (2 * r))) :
    GL (Fin (2 * r)) F) : Matrix (Fin (2 * r)) (Fin (2 * r)) F).IsDiag
  rw [hcoe, ht]
  intro i j hij
  have hne := (CFSG.LieType.SeitzGeneration.hypEquivFin r 0).symm.injective.ne hij
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal, hne]

end CFSG.StandardType.ClassicalPosition
