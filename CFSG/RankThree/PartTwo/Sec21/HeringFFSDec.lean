module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)

theorem ffs_comm_of_decomp {G : Type*} [Group G] {B T S : Subgroup G}
    (hT : IsElemAbelian 3 T) (hS : IsCyclic S) (hTS : ∀ t ∈ T, ∀ s ∈ S, t * s = s * t)
    (hdec : ∀ b ∈ B, ∃ t ∈ T, ∃ s ∈ S, b = t * s) : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := ↥S)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hx y hy
  obtain ⟨t₁, ht₁, s₁, hs₁, rfl⟩ := hdec x hx
  obtain ⟨t₂, ht₂, s₂, hs₂, rfl⟩ := hdec y hy
  have hA : t₁ * s₁ * (t₂ * s₂) = t₁ * t₂ * (s₁ * s₂) := by
    calc t₁ * s₁ * (t₂ * s₂) = t₁ * (s₁ * t₂) * s₂ := by simp only [mul_assoc]
      _ = t₁ * (t₂ * s₁) * s₂ := by rw [← hTS t₂ ht₂ s₁ hs₁]
      _ = t₁ * t₂ * (s₁ * s₂) := by simp only [mul_assoc]
  have hB : t₂ * s₂ * (t₁ * s₁) = t₂ * t₁ * (s₂ * s₁) := by
    calc t₂ * s₂ * (t₁ * s₁) = t₂ * (s₂ * t₁) * s₁ := by simp only [mul_assoc]
      _ = t₂ * (t₁ * s₂) * s₁ := by rw [← hTS t₁ ht₁ s₂ hs₂]
      _ = t₂ * t₁ * (s₂ * s₁) := by simp only [mul_assoc]
  rw [hA, hB, hTc t₁ ht₁ t₂ ht₂, hSc s₁ hs₁ s₂ hs₂]

theorem ffs_pow_three_of_decomp {G : Type*} [Group G] {B T S : Subgroup G}
    (hT : IsElemAbelian 3 T) (hTS : ∀ t ∈ T, ∀ s ∈ S, t * s = s * t)
    (hdec : ∀ b ∈ B, ∃ t ∈ T, ∃ s ∈ S, b = t * s) :
    ∀ b ∈ B, ∃ s ∈ S, b ^ 3 = s ^ 3 := by
  intro b hb
  obtain ⟨t, ht, s, hs, rfl⟩ := hdec b hb
  refine ⟨s, hs, ?_⟩
  have hc : Commute t s := hTS t ht s hs
  rw [hc.mul_pow, hT.2 t ht, one_mul]

theorem ffs_pow_three_eq_one_of_decomp {G : Type*} [Group G] {B T S : Subgroup G}
    (hT : IsElemAbelian 3 T) (hTS : ∀ t ∈ T, ∀ s ∈ S, t * s = s * t)
    (hdec : ∀ b ∈ B, ∃ t ∈ T, ∃ s ∈ S, b = t * s) (hS3 : ∀ s ∈ S, s ^ 3 = 1) :
    ∀ b ∈ B, b ^ 3 = 1 := by
  intro b hb
  obtain ⟨s, hs, h⟩ := ffs_pow_three_of_decomp hT hTS hdec b hb
  exact h.trans (hS3 s hs)

end CFSG.RankThree.PartTwo.Sec21
