module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57A
import CFSG.RankThree.PartTwo.Sec21.FF81Holt
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem S57.card_cen_conj_le (g x : G) : Nat.card (Cen (g * x * g⁻¹)) ≤ Nat.card (Cen x) := by
  have hle : Cen (g * x * g⁻¹) ≤ (Cen x).map (MulAut.conj g).toMonoidHom := fun y hy => by
    refine ⟨g⁻¹ * y * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp [mul_assoc]⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  exact (Subgroup.card_le_of_le hle).trans_eq
    (Subgroup.card_map_of_injective (MulAut.conj g).injective)

section B

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)
include h5 hJs

theorem FF81Sec5.β_sup_M_le :
    Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
  sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    ((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _))

theorem FF81Sec5.card_β_sup_M :
    Nat.card ↥(Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀) =
      3 * Nat.card (M₅₇ b b₁ b₂ b₃ s₀) := by
  have hc : ∀ x ∈ Subgroup.zpowers (β' b₂ b₃), ∀ y ∈ M₅₇ b b₁ b₂ b₃ s₀, x * y = y * x :=
    fun x hx y hy => by
    have hyβ : y * β' b₂ b₃ = β' b₂ b₃ * y := Subgroup.mem_centralizer_singleton_iff.mp
      (((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)) hy)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right (show Commute y (β' b₂ b₃) from hyβ) k).eq).symm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rw [h5.zpowers_β_inf_M hJs, Subgroup.card_bot, mul_one, Nat.card_zpowers, h5.β_orderOf] at hcard
  exact hcard

theorem FF81Sec5.cen_β_of_conj (h0 : Opp 3 (Cen b) = ⊥)
    (hM : Nat.card (M₅₇ b b₁ b₂ b₃ s₀) = 1451520)
    (hβ : Subgroup.zpowers (β' b₂ b₃) ∈ ConjLines B b) :
    Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ = Cen (β' b₂ b₃) := by
  obtain ⟨-, g, hg⟩ := hβ
  have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers (β' b₂ b₃) := by
    rw [← hg]; exact ⟨b, Subgroup.mem_zpowers b, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgb
  have h1 : Cen (β' b₂ b₃) ≤ Cen (g * b * g⁻¹) := fun x hx => by
    rw [← hk]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.zpow_right
      (show Commute x (β' b₂ b₃) from Subgroup.mem_centralizer_singleton_iff.mp hx) k).eq)
  have hB := h5.basis
  have hL := card_of_model_sp6 hB.hyp.model
  have h3 : Nat.card (Cen b) ≤ 3 * Nat.card L := by
    have hc : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ L, x * y = y * x := fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left
        (show Commute b y from (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hy)).symm)
        i).eq
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
    rw [Nat.card_zpowers, h5.orderOf_b] at hcard
    have hle : Cen b ≤ Subgroup.zpowers b ⊔ L := fun y hy => by
      obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h0 hy
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b i))
        (Subgroup.mem_sup_right hl)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers b ⊓ L) := Nat.card_pos
    calc Nat.card (Cen b) ≤ Nat.card ↥(Subgroup.zpowers b ⊔ L) := Subgroup.card_le_of_le hle
      _ ≤ Nat.card ↥(Subgroup.zpowers b ⊔ L) * Nat.card ↥(Subgroup.zpowers b ⊓ L) :=
        Nat.le_mul_of_pos_right _ hpos
      _ = 3 * Nat.card L := hcard
  refine Subgroup.eq_of_le_of_card_ge (h5.β_sup_M_le hJs) ?_
  rw [h5.card_β_sup_M hJs, hM]
  calc Nat.card (Cen (β' b₂ b₃)) ≤ Nat.card (Cen (g * b * g⁻¹)) := Subgroup.card_le_of_le h1
    _ ≤ Nat.card (Cen b) := S57.card_cen_conj_le g b
    _ ≤ 3 * Nat.card L := h3
    _ = 3 * 1451520 := by rw [hL]

end B

theorem ff81_5_7 (hKF : KF_Sp6Levi) (hKS : KF_Sp6ShortRoot)
    (hKC : KF_Sp6ShortRootCen) (hGL : KF_Sp4CenGL6) (hS6 : KF_Sp6GL6Cen) (h7b : FF81_5_7b) :
    FF81_5_7 := by
  intro hMcL hHolt G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 hfus c
  obtain ⟨h0, c2, c4, -, -⟩ := id c
  have hbig := h5.big hKF hKS
  obtain ⟨hmod, hset⟩ := h5.ff81_5_7a hKF hKC hGL hS6 hMcL hbig c2 c4
  obtain ⟨-, hJs, -, -⟩ := c4
  refine ⟨M₅₇ b b₁ b₂ b₃ s₀, S57.M_le_cenS hJs, hmod, hset, ?_, h5.zpowers_β_inf_M hJs,
    le_sup_right⟩
  by_cases hβ : Subgroup.zpowers (β' b₂ b₃) ∈ ConjLines B b
  · exact h5.cen_β_of_conj hJs h0 (card_of_model_sp6 hmod) hβ
  · exact h7b hHolt G b L B b₁ b₂ b₃ t₀ s₀ h5 hfus c hmod hset hβ

end CFSG.RankThree.PartTwo.Sec21.FF81
