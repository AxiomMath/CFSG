module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinALift
import CFSG.GroupTheory.AbelianHallSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_abelian_complement {N Y B : Subgroup Γ} [N.Normal] (hN2 : IsPGroup 2 N)
    (hNY : N ≤ Y) (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B)) [IsCyclic B]
    {y₁ : Γ} (hy₁ : y₁ ∈ Y) (hcomm : ∀ b ∈ B, y₁ * b * y₁⁻¹ * b⁻¹ ∈ N)
    (hBY : B ⊓ Y = ⊥) (hu : orderOf (QuotientGroup.mk' N y₁) = Nat.card B) :
    ∃ A : Subgroup Γ, B ≤ A ∧ A ≤ Y ⊔ B ∧ IsMulCommutative A ∧ A ⊓ Y ⊔ B = A ∧
      A ⊓ Y ⊓ B = ⊥ ∧ Nonempty (↥(A ⊓ Y) ≃* ↥B) := by
  set Y₁ : Subgroup Γ := N ⊔ zpowers y₁ with hY₁
  have hY₁Y : Y₁ ≤ Y := sup_le hNY ((Subgroup.zpowers_le).2 hy₁)
  have hNtop : normalizer (N : Set Γ) = ⊤ := Subgroup.normalizer_eq_top_iff.2 inferInstance
  have hBN : B ≤ normalizer (N : Set Γ) := hNtop ▸ le_top
  have hY₁N : Y₁ ≤ normalizer (N : Set Γ) := hNtop ▸ le_top
  have hBY₁ : B ≤ normalizer (Y₁ : Set Γ) := le_normalizer_sup_zpowers hcomm
  have hodd₁ : Odd (N.relIndex Y₁) := by
    rw [hY₁, relIndex_sup_zpowers, hu]
    exact hBodd
  obtain ⟨A, hBA, hAle, -, hAab, hNA, hNAY⟩ :=
    CFSG.GroupTheory.exists_abelian_hall_sup hN2 le_sup_left hY₁N hBN hBY₁ hodd₁ hBodd hBab
      (fun x hx y hy => commutator_mem_of_mem_sup hx hy)
      (fun x hx b hb => commutator_mem_of_mem_sup_of_commute hx (hcomm b hb))
  have hdecomp : ∀ a ∈ A, ∃ b ∈ B, ∃ y ∈ A ⊓ Y₁, b * y = a := by
    intro a ha
    have h1 : a ∈ Y₁ ⊔ B := hAle ha
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B Y₁ hBY₁] at h1
    obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_mul.1 h1
    refine ⟨b, hb, y, ⟨?_, hy⟩, rfl⟩
    simpa using A.mul_mem (A.inv_mem (hBA hb)) ha
  have hAY : A ⊓ Y = A ⊓ Y₁ := by
    refine le_antisymm (fun a ha => ?_) (inf_le_inf_left A hY₁Y)
    obtain ⟨b, hb, y, hy, rfl⟩ := hdecomp a ha.1
    have hbY : b ∈ B ⊓ Y := by
      refine ⟨hb, ?_⟩
      simpa using Y.mul_mem ha.2 (Y.inv_mem (hY₁Y hy.2))
    rw [hBY, Subgroup.mem_bot] at hbY
    rw [hbY, one_mul]
    exact hy
  refine ⟨A, hBA, ?_, hAab, ?_, ?_, ?_⟩
  · exact hAle.trans (sup_le_sup_right hY₁Y B)
  · refine le_antisymm (sup_le inf_le_left hBA) fun a ha => ?_
    obtain ⟨b, hb, y, hy, rfl⟩ := hdecomp a ha
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb)
      (Subgroup.mem_sup_left (inf_le_inf_left A hY₁Y hy))
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have : x ∈ B ⊓ Y := ⟨hx.2, hx.1.2⟩
    rwa [hBY, Subgroup.mem_bot] at this
  · have hNC : N ⊓ (A ⊓ Y₁) = ⊥ :=
      eq_bot_iff.2 (hNA ▸ inf_le_inf_left N inf_le_left)
    have hsup : N ⊔ (A ⊓ Y₁) = N ⊔ zpowers y₁ := by rwa [inf_comm] at hNAY
    obtain ⟨hcyc, hcard⟩ := isCyclic_card_of_complement hNC hsup
    have : IsCyclic ↥(A ⊓ Y₁) := hcyc
    rw [hAY]
    exact ⟨mulEquivOfCyclicCardEq (hcard.trans hu)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
