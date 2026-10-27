module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Background.G25Dual
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

theorem dual_fix_eq_zero {F : Type*} [Field F] [CharP F 2] (H : Subgroup SL(3, F)) [Finite H]
    (hodd : Odd (Nat.card H)) (hfix : ∀ v : Fin 3 → F, (∀ A ∈ H, A • v = v) → v = 0)
    (f : Fin 3 → F) (hf : ∀ A ∈ H, dualHom F 3 A • f = f) : f = 0 := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hdot : ∀ A ∈ H, ∀ v : Fin 3 → F, f ⬝ᵥ (A • v) = f ⬝ᵥ v := fun A hA v => by
    have := dualHom_smul_dot A f v
    rwa [hf A hA] at this
  have hsum : ∀ v : Fin 3 → F, (∑ A : H, (A : SL(3, F)) • v) = 0 := by
    intro v
    apply hfix
    intro B hB
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨B, hB⟩ : H)) _ _ (fun A => by
      simp [mul_smul])
  have hcard : ((Nat.card H : ℕ) : F) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    push_cast
    rw [show (2 : F) = 0 from CharP.cast_eq_zero F 2]
    ring
  have hv : ∀ v : Fin 3 → F, f ⬝ᵥ v = 0 := by
    intro v
    have h1 : f ⬝ᵥ (∑ A : H, (A : SL(3, F)) • v) = (Nat.card H : F) * (f ⬝ᵥ v) := by
      rw [dotProduct_sum]
      simp only [fun A : H => hdot A A.2 v, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rw [hsum, dotProduct_zero, hcard, one_mul] at h1
    exact h1.symm
  funext i
  have := hv (Pi.single i 1)
  simpa [dotProduct_single] using this

end CFSG.Quasithin.Vol2.Ch11.SecD
