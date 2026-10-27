module

public import CFSG.Quasithin.Background.SmithB51LnModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.B5.Ln

open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Matrix

variable {n : ℕ}

theorem scalars_zmod_two_eq_bot : scalars n (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, -, hc⟩ := hA
  have hc1 : (c : ZMod 2) = 1 := by
    have : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
    exact this c
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hc, hc1]
  simp

theorem proj_zmod_two_injective : Function.Injective (proj n (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_zmod_two_eq_bot]

theorem fieldAut_zmod_two (τ : ZMod 2 ≃+* ZMod 2) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    fieldAut n (ZMod 2) τ (proj n (ZMod 2) g) = proj n (ZMod 2) g := by
  rw [fieldAut_proj]
  congr 1
  have hτ : τ.toRingHom = RingHom.id (ZMod 2) := Subsingleton.elim _ _
  rw [hτ]
  ext i j
  simp

theorem aut_cases (hn : 3 ≤ n) (σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))) :
    ∃ P : GL (Fin n) (ZMod 2),
      (∀ g, mat (σ g) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat g *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) ∨
      (∀ g, mat (σ g) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat g *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  set e := specialLinearGroupEquivStatedSL n (ZMod 2) with he
  set σ' : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) := e.trans (σ.trans e.symm) with hσ'
  set α := descendAut n (ZMod 2) σ' with hα
  obtain ⟨A, τ, ε, hε, hαeq⟩ := (automorphism_generation (K := ZMod 2) hn).2 α
  have hcoe : ∀ x : ↥(StatedSL n (ZMod 2)),
      ((e.symm x : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        mat x := by
    intro x
    conv_rhs => rw [← e.apply_symm_apply x]
    rfl
  have hσx : ∀ x : ↥(StatedSL n (ZMod 2)),
      mat (σ x) = ((σ' (e.symm x) : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro x
    rw [← hcoe (σ x)]
    simp [hσ']
  have hαp : ∀ g, α (proj n (ZMod 2) g) = proj n (ZMod 2) (σ' g) := fun g => descendAut_proj _ _ _ g
  refine ⟨A, ?_⟩
  interval_cases ε
  · left
    intro x
    have h1 := hαp (e.symm x)
    rw [hαeq, pow_zero, mul_one, MulAut.mul_apply, fieldAut_zmod_two, conjAut_proj] at h1
    have h2 := proj_zmod_two_injective h1
    rw [hσx, ← h2, coe_slConjugation, hcoe]
  · right
    intro x
    have h1 := hαp (e.symm x)
    rw [hαeq, pow_one, MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_zmod_two,
      conjAut_proj] at h1
    have h2 := proj_zmod_two_injective h1
    rw [hσx, ← h2, coe_slConjugation]
    congr 2
    rw [dmat, ← hcoe x⁻¹, map_inv]
    rfl

end CFSG.Quasithin.B5.Ln
