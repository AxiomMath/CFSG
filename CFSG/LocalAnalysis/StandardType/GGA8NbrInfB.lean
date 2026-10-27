module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrInfDataB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrPlumb

public section

namespace CFSG.StandardType

open Certificates.A8Nbr476 Matrix CFSG.StandardType.A8NbrInf CFSG.StandardType.A8NbrInfB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggA8NbrInfB_false_of_coord {G : Type} [Group G] {Bs : Subgroup G} (L K : Subgroup G)
    (hNT : GGNoTransvection 7 Bs)
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) {a μ : ZMod 7} (ha : a ≠ 0) (hμ : μ ≠ 0)
    (hgen : ∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
      ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gensInfB a μ k)) :
    False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Submonoid M4 :=
    { carrier := {g | ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
        ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) g}
      mul_mem' := by
        rintro g₁ g₂ ⟨φ₁, hφ₁, h₁⟩ ⟨φ₂, hφ₂, h₂⟩
        refine ⟨φ₂ * φ₁, Subgroup.mul_mem _ hφ₂ hφ₁, fun b => ?_⟩
        rw [MulAut.mul_apply, h₂, h₁, Matrix.vecMul_vecMul]
      one_mem' := ⟨1, Subgroup.one_mem _, fun b => by simp⟩ }
  obtain ⟨g, ⟨φ, hφA, hφ⟩, hT⟩ := a8InfB_exists_transv ha hμ S hgen
  obtain ⟨u, w, hu, hw, hwu, hvec⟩ := ggIsTransv_exists_lin hT
  have hlin : ∀ v, ggLin (p := 7) ι φ v = v + (ggA8Nbr_dotForm u v) • w := by
    intro v
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ggLin_apply_ofMul, hφ, hvec]
    rfl
  have htr := ggIsTransvection_of_apply (p := 7) ι hw (ggA8Nbr_dotForm_ne_zero hu)
    (by rw [ggA8Nbr_dotForm_apply]; exact hwu) hlin
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  exact hNT φ (mem_ggAutomizer_iff.mp (hle hφA)) htr

end CFSG.StandardType

end
