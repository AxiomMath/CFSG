module

public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightGram

public section

namespace CFSG.StandardType

namespace UnitaryCore

open Matrix SpBlocks

variable {Γ : Type*} [Group Γ] [Finite Γ] {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
  [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

theorem eq_one_of_fibres {κ : Type*} [DecidableEq κ] (h5 : HasOrderFiveData Γ)
    (h7 : HasOrderSevenData Γ) (σ : Ω ≃+* Ω) (c : ι → κ) {H : Matrix ι ι Ω} (hHu : IsUnit H)
    (Q : Γ →* Matrix ι ι Ω)
    (hQs : ∀ g k, Splits (Finset.univ.filter fun a => c a = k) (Q g))
    (hform : ∀ g, (Q g)ᵀ * H * (Q g).map σ = H)
    (hsmall : ∀ k, (Finset.univ.filter fun a => c a = k).card ≤ 3 ∨
      ((Finset.univ.filter fun a => c a = k).card ≤ 5 ∧
        Splits (Finset.univ.filter fun a => c a = k) H))
    (g : Γ) : Q g = 1 := by
  apply SpBlocks.eq_one_of_forall_blk_eq_one c (Q g) (fun k => hQs g k)
  intro k
  rcases hsmall k with hI | ⟨hI, hH⟩
  · exact SpBlocks.HasOrderFiveData.blk_eq_one_of_card_le_three h5 _ Q (fun g => hQs g k) hI g
  · exact SpBlocks.HasOrderSevenData.blk_eq_one_of_card_le_five h7 _ Q (fun g => hQs g k) σ
      (fun η hη => UnitaryWeight.ringEquiv_apply_eq_two_pow_of_pow_seven σ hη) hH hHu hform hI g

@[expose] def conjHom {P Q : Matrix ι ι Ω} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (ρ : Γ →* Matrix ι ι Ω) : Γ →* Matrix ι ι Ω where
  toFun g := Q * ρ g * P
  map_one' := by
    rw [map_one, Matrix.mul_one, hQP]
  map_mul' g h := by
    rw [map_mul]
    calc Q * (ρ g * ρ h) * P
        = (Q * ρ g) * (ρ h * P) := by simp only [Matrix.mul_assoc]
      _ = (Q * ρ g) * ((P * Q) * (ρ h * P)) := by rw [hPQ, one_mul]
      _ = ((Q * ρ g) * P) * ((Q * ρ h) * P) := by simp only [Matrix.mul_assoc]

theorem conjHom_apply {P Q : Matrix ι ι Ω} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (ρ : Γ →* Matrix ι ι Ω) (g : Γ) : conjHom hPQ hQP ρ g = Q * ρ g * P :=
  rfl

theorem eq_one_of_conjHom {P Q : Matrix ι ι Ω} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (ρ : Γ →* Matrix ι ι Ω) (g : Γ) (h : conjHom hPQ hQP ρ g = 1) : ρ g = 1 := by
  have h' : Q * ρ g * P = 1 := h
  calc ρ g
      = (P * Q) * ρ g * (P * Q) := by rw [hPQ, one_mul, Matrix.mul_one]
    _ = P * (Q * ρ g * P) * Q := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h', Matrix.mul_one, hPQ]

theorem splits_fibre_of_commute_diagonal {A κ : Type*} [DecidableEq κ] (w : A → ι → Ω)
    {M : Matrix ι ι Ω} (hM : ∀ a, M * diagonal (w a) = diagonal (w a) * M) (c : ι → κ)
    (hc : ∀ α β, (∀ a, w a α = w a β) → c α = c β) (k : κ) :
    Splits (Finset.univ.filter fun α => c α = k) M := by
  apply SpBlocks.splits_fiber_of_forall c (M := M) (k := k)
  intro α β hαβ
  exact hc α β (fun a => congr_fun (SpBlocks.entries_eq_of_commute_diagonal w hM hαβ) a)

lemma diagonal_const_eq_smul_one (c : Ω) :
    diagonal (fun _ : ι => c) = c • (1 : Matrix ι ι Ω) := by
  rw [show (fun _ : ι => c) = c • (fun _ => (1 : Ω)) by funext i; simp]
  rw [Matrix.diagonal_smul, Matrix.diagonal_one]

end UnitaryCore

end CFSG.StandardType
