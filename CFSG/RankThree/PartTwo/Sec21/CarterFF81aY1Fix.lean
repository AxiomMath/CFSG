module

public import CFSG.GroupTheory.MulAutTrivialOnSubgroup

@[expose] public section

namespace CFSG

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {B : Type} [Group B] [Finite B]

theorem MulAut.eq_on_fixed_of_commute_card_nine
    {Y₁ : Subgroup (MulAut B)} {τ t : MulAut B} {C : Subgroup B}
    (hCmem : ∀ v : B, v ∈ C ↔ (τ * t) v = v)
    (hC : IsElemAb 3 2 C)
    (hcop : Nat.Coprime (Nat.card Y₁) 6)
    (hcomm : ∀ y : MulAut B, y ∈ Y₁ → y * (τ * t) = (τ * t) * y) :
    ∀ (y : MulAut B), y ∈ Y₁ → ∀ v : B, v ∈ C → y v = v := by
  have hforward : ∀ (y : MulAut B), y ∈ Y₁ → ∀ v : B, v ∈ C → y v ∈ C := by
    intro y hy v hv
    rw [hCmem]
    calc
      (τ * t) (y v) = ((τ * t) * y) v := (MulAut.mul_apply B (τ * t) y v).symm
      _ = (y * (τ * t)) v := by rw [← hcomm y hy]
      _ = y ((τ * t) v) := MulAut.mul_apply B y (τ * t) v
      _ = y v := by rw [(hCmem v).mp hv]
  have hbackward : ∀ (y : MulAut B), y ∈ Y₁ → ∀ v : B, v ∈ C → y⁻¹ v ∈ C := by
    intro y hy v hv
    have hcomm' : y⁻¹ * (τ * t) = (τ * t) * y⁻¹ :=
      (show Commute y (τ * t) from hcomm y hy).inv_left
    rw [hCmem]
    calc
      (τ * t) (y⁻¹ v) = ((τ * t) * y⁻¹) v := (MulAut.mul_apply B (τ * t) y⁻¹ v).symm
      _ = (y⁻¹ * (τ * t)) v := by rw [← hcomm']
      _ = y⁻¹ ((τ * t) v) := MulAut.mul_apply B y⁻¹ (τ * t) v
      _ = y⁻¹ v := by rw [(hCmem v).mp hv]
  have hpres : ∀ y : MulAut B, y ∈ Y₁ → Subgroup.map y C = C := by
    intro y hy
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact hforward y hy v hv
    · intro v hv
      rw [Subgroup.mem_map]
      exact ⟨y⁻¹ v, hbackward y hy v hv, by simp⟩
  exact fun y hy v hv =>
    MulAut.act_trivial_of_preserves_card_nine (Y := Y₁) (C := C) hcop hC hpres y hy v hv

end CFSG
