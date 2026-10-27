module

public import CFSG.LocalAnalysis.ZStar.NormalTwo

public section

namespace CFSG

namespace ZStar.CentralizerInduction

open ZStar.TransferReduction

universe u

noncomputable local instance subgroupFintype
    {X : Type u} [Group X] [Fintype X] (H : Subgroup X) : Fintype H :=
  Fintype.ofFinite H

@[expose] def ZStarConclusion (X : Type u) [Group X] [Fintype X] (x : X) : Prop :=
  ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧
    ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ N

theorem centralizer_induction_or_zStar
    {X : Type u} [Group X] [Fintype X] {t w : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (hw1 : w ≠ 1) (hw2 : w * w = 1) (htw : Commute t w) :
    ZStarConclusion X t ∨
      ∃ (H : Subgroup X) (htH : t ∈ H),
        H = Subgroup.centralizer ({w} : Set X) ∧ H ≠ ⊤ ∧
        Nat.card H < Nat.card X ∧
        Isolated (⟨t, htH⟩ : H) ∧
        (⟨t, htH⟩ : H) * ⟨t, htH⟩ = 1 ∧
        ZStarConclusion H (⟨t, htH⟩ : H) := by
  classical
  let H : Subgroup X := Subgroup.centralizer ({w} : Set X)
  have htH : t ∈ H := by
    change t ∈ Subgroup.centralizer ({w} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htw.eq
  by_cases hHtop : H = ⊤
  · left
    have hwcenter : w ∈ Subgroup.center X := by
      have hsubset : ({w} : Set X) ⊆ (Subgroup.center X : Set X) :=
        Subgroup.centralizer_eq_top_iff_subset.mp hHtop
      exact hsubset (Set.mem_singleton w)
    let M : Subgroup X := Subgroup.zpowers w
    have hMcenter : M ≤ Subgroup.center X := by
      exact Subgroup.zpowers_le_of_mem hwcenter
    have hMnormal : M.Normal := by
      constructor
      intro n hn g
      have hcomm : g * n = n * g :=
        Subgroup.mem_center_iff.mp (hMcenter hn) g
      have heq : g * n * g⁻¹ = n := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact hn
    let _ : M.Normal := hMnormal
    have hMtwo : IsPGroup 2 M :=
      isPGroup_zpowers_two_of_sq_eq_one w hw2
    have hMne : M ≠ ⊥ := by
      intro hMbot
      apply hw1
      have hwbot : w ∈ (⊥ : Subgroup X) := by
        rw [← hMbot]
        exact Subgroup.mem_zpowers w
      simpa using hwbot
    have hcard : Nat.card (X ⧸ M) < Nat.card X :=
      ZStar.TransferReduction.card_quotient_lt_of_ne_bot M hMne
    exact zStar_of_terminal_normal_two_quotient ht ht2 hmin M hMtwo
      (by
        intro hqt1 hqisolated hqt2
        exact ih hcard hqisolated hqt2)
  · right
    have hcard : Nat.card H < Nat.card X := by
      have hle : Nat.card H ≤ Nat.card X := Subgroup.card_le_card_group H
      apply lt_of_le_of_ne hle
      intro heq
      exact hHtop ((Subgroup.card_eq_iff_eq_top H).mp heq)
    have hisolatedH : Isolated (⟨t, htH⟩ : H) := by
      intro h hh
      apply Subtype.ext
      exact ht (h : X) (congrArg Subtype.val hh)
    have htH2 : (⟨t, htH⟩ : H) * ⟨t, htH⟩ = 1 := by
      apply Subtype.ext
      exact ht2
    have hih : ZStarConclusion H (⟨t, htH⟩ : H) :=
      ih hcard hisolatedH htH2
    exact ⟨H, htH, rfl, hHtop, hcard, hisolatedH, htH2, hih⟩

end ZStar.CentralizerInduction

end CFSG
