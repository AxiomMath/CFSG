module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModule
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem center_sl12_zmod2 :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 12) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  have hr1 : r = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) r with rfl | rfl
    · simp at hr
    · rfl
  subst r
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

theorem not_nonempty_mulEquiv_psl12 (hK : Nat.card K = 4) {G : Type*} [Group G]
    {L : Subgroup G} (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    ¬ Nonempty (G ≃* PSL(12, ZMod 2)) := by
  rintro ⟨eG⟩
  letI addCommGroupV : AddCommGroup (Fin 12 → ZMod 2) := inferInstance
  letI moduleV : Module (ZMod 2) (Fin 12 → ZMod 2) := inferInstance
  letI finiteV : Finite (Fin 12 → ZMod 2) := inferInstance
  let pslEquivSL : PSL(12, ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 12) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_sl12_zmod2).trans QuotientGroup.quotientBot
  let ψ : L →* Matrix.SpecialLinearGroup (Fin 12) (ZMod 2) :=
    pslEquivSL.toMonoidHom.comp (eG.toMonoidHom.comp L.subtype)
  let ρ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      ((Fin 12 → ZMod 2) ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)) :=
    (Matrix.SpecialLinearGroup.toLin' (n := Fin 12) (R := ZMod 2)).comp
      (ψ.comp φ.symm.toMonoidHom)
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 : ψ (φ.symm x) = ψ (φ.symm y) :=
      Matrix.SpecialLinearGroup.toLin'_injective hxy
    have h2 : eG (L.subtype (φ.symm x)) = eG (L.subtype (φ.symm y)) :=
      pslEquivSL.injective h1
    have h3 : L.subtype (φ.symm x) = L.subtype (φ.symm y) := eG.injective h2
    exact φ.symm.injective (L.subtype_injective h3)
  have h20 := @twenty_le_finrank_of_injective K _ hK (Fin 12 → ZMod 2)
    addCommGroupV moduleV finiteV ρ hρ
  have hcard : Nat.card (Fin 12 → ZMod 2) =
      2 ^ Module.finrank (ZMod 2) (Fin 12 → ZMod 2) := by
    rw [@Module.natCard_eq_pow_finrank (ZMod 2) (Fin 12 → ZMod 2) _ addCommGroupV moduleV
      (inferInstance : Module.Finite (ZMod 2) (Fin 12 → ZMod 2))]
    rw [Nat.card_zmod]
    rfl
  have h2 : 2 ^ 20 ≤ Nat.card (Fin 12 → ZMod 2) := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h20
  have hcardV : Nat.card (Fin 12 → ZMod 2) = 2 ^ 12 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hcardV] at h2
  norm_num at h2

end CFSG.StandardType.USixTwo
