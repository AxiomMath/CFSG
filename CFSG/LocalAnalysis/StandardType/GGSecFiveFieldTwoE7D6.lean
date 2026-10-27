module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwPin
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameRecog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame
public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore

public section

namespace CFSG.StandardType.FieldTwoE7

open CFSG CFSG.Open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint CFSG.ComponentClassification.CatLeafProof CFSG.StandardType.RankOneXfer

theorem ker_comp_le_center_of_perfect {A B C : Type*} [Group A] [Group B] [Group C]
    (Ψ : A →* B) (hΨ : Ψ.ker ≤ Subgroup.center A) (hA : commutator A = ⊤)
    (σ : B →* C) (hσ : σ.ker ≤ Subgroup.center B) :
    (σ.comp Ψ).ker ≤ Subgroup.center A := by
  intro y hy
  have hyc : Ψ y ∈ Subgroup.center B := hσ hy
  have hk : ∀ z : A, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center A := by
    intro z
    apply hΨ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← (Subgroup.mem_center_iff.mp hyc (Ψ z))]
    group
  have hc : ∀ (z : A) (g : A), g * (y * z * y⁻¹ * z⁻¹) = (y * z * y⁻¹ * z⁻¹) * g :=
    fun z g => Subgroup.mem_center_iff.mp (hk z) g
  let c : A →* Subgroup.center A :=
    { toFun := fun z => ⟨y * z * y⁻¹ * z⁻¹, hk z⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        change y * (u * v) * y⁻¹ * (u * v)⁻¹ = (y * u * y⁻¹ * u⁻¹) * (y * v * y⁻¹ * v⁻¹)
        calc y * (u * v) * y⁻¹ * (u * v)⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹ * v⁻¹) * u⁻¹ := by group
          _ = (y * u * y⁻¹) * u⁻¹ * (y * v * y⁻¹ * v⁻¹) := by
            rw [mul_assoc (y * u * y⁻¹) (y * v * y⁻¹ * v⁻¹) u⁻¹, ← hc v u⁻¹, ← mul_assoc]
          _ = (y * u * y⁻¹ * u⁻¹) * (y * v * y⁻¹ * v⁻¹) := by group) }
  have hker : commutator A ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (c a).2 (c b : A)).symm)
  rw [Subgroup.mem_center_iff]
  intro z
  have hz : c z = 1 := (hker (hA ▸ Subgroup.mem_top z) : z ∈ c.ker)
  have h1 : y * z * y⁻¹ * z⁻¹ = 1 := congrArg Subtype.val hz
  have h2 : y * z = z * y := by
    calc y * z = (y * z * y⁻¹ * z⁻¹) * (z * y) := by group
      _ = z * y := by rw [h1, one_mul]
  exact h2.symm

end CFSG.StandardType.FieldTwoE7
