module

public import CFSG.Quasithin.MS93.S46R468B

public section

namespace CFSG.Yardstones.M71b2fd3d34b9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
  CFSG.Quasithin.MS93.S46R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideD468_forall_bzero_of_le_sup (c : Hyp46 M T L φ)
    {x μ : Vtx (puAmalgam c.pu.le)} {J₁ J₂ : Subgroup (puAmalgam c.pu.le).Universal}
    (h₁ : J₁ ≤ stab (puAmalgam c.pu.le) x) (h₂ : J₂ ≤ stab (puAmalgam c.pu.le) x)
    (hJ₁ : ∀ k ∈ J₁, ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, k⁆ ∈ bzero c x)
    (hJ₂ : ∀ k ∈ J₂, ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, k⁆ ∈ bzero c x) :
    ∀ k ∈ J₁ ⊔ J₂, ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, k⁆ ∈ bzero c x := by
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ stab (puAmalgam c.pu.le) x ∧
        ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, k⁆ ∈ bzero c x}
      one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro k₁ k₂ ⟨hk₁, hk₁'⟩ ⟨hk₂, hk₂'⟩
        refine ⟨Subgroup.mul_mem _ hk₁ hk₂, fun w hw => ?_⟩
        have e : ⁅w, k₁ * k₂⁆ = ⁅w, k₁⁆ * (k₁ * ⁅w, k₂⁆ * k₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (hk₁' w hw) ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_bzero c x hk₁) _).mp (hk₂' w hw))
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        refine ⟨Subgroup.inv_mem _ hk, fun w hw => ?_⟩
        have e : ⁅w, k⁻¹⁆ = k⁻¹ * ⁅w, k⁆⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c x
          (Subgroup.inv_mem _ hk)) _).mp (Subgroup.inv_mem _ (hk' w hw)) }
  have hle : J₁ ⊔ J₂ ≤ S :=
    sup_le (fun k hk => ⟨h₁ hk, hJ₁ k hk⟩) (fun k hk => ⟨h₂ hk, hJ₂ k hk⟩)
  exact fun k hk => (hle hk).2

end CFSG.Yardstones.M71b2fd3d34b9
