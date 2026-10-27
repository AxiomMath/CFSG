module

public import CFSG.LocalAnalysis.ZStar.TransferReduction

public section

namespace CFSG

namespace ZStar.InductiveTerminal

open ZStar.TransferReduction

universe u

variable {G : Type u} [Group G] [Fintype G]

theorem zStar_of_commutator_terminal_with_ih
    (hterminal :
      ∀ {X : Type u} [Group X] [Fintype X] {x : X},
        Isolated x → x * x = 1 →
        (∀ H : Subgroup X, H.Normal → x ∈ H → H = ⊤) →
        (commutator X = ⊤ ∨ (commutator X).index = 2) →
        (∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
          Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ∃ N : Subgroup Y, N.Normal ∧ Odd (Nat.card N) ∧
            ∀ g : Y, g * y * g⁻¹ * y⁻¹ ∈ N) →
        ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧
          ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ N)
    {t : G} (ht : Isolated t) (ht2 : t * t = 1) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  let rec go (X : Type u) [Group X] [Fintype X] (x : X)
      (hx : Isolated x) (hx2 : x * x = 1) :
      ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧
        ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ N := by
    classical
    by_cases hmin : ∀ H : Subgroup X, H.Normal → x ∈ H → H = ⊤
    · refine hterminal hx hx2 hmin
        (commutator_eq_top_or_index_eq_two_of_no_proper_normal_overgroup
          hx2 hmin) ?_
      intro Y _ _ y hYX hy hy2
      exact go Y y hy hy2
    · push Not at hmin
      obtain ⟨H, hHnormal, hxH, hHne⟩ := hmin
      let _ : H.Normal := hHnormal
      let xH : H := ⟨x, hxH⟩
      have hxH2 : xH * xH = 1 := by
        apply Subtype.ext
        exact hx2
      have hisolatedH : Isolated xH := by
        intro h hh
        apply Subtype.ext
        exact hx (h : X) (congrArg Subtype.val hh)
      have hcard : Nat.card H < Nat.card X := by
        have hle : Nat.card H ≤ Nat.card X := Subgroup.card_le_card_group H
        apply lt_of_le_of_ne hle
        intro heq
        exact hHne ((Subgroup.card_eq_iff_eq_top H).mp heq)
      obtain ⟨K, hKnormal, hKodd, hKcomm⟩ :=
        go H xH hisolatedH hxH2
      let KX : Subgroup X := Subgroup.map H.subtype K
      have hKXH : KX ≤ H := Subgroup.map_subtype_le K
      have hrestrict : KX.subgroupOf H = K := by
        apply Subgroup.map_subtype_inj.mp
        rw [Subgroup.map_subgroupOf_eq_of_le hKXH]
      have hKXnormal : (KX.subgroupOf H).Normal := by
        rw [hrestrict]
        exact hKnormal
      have hKXodd : Odd (Nat.card KX) := by
        rw [show Nat.card KX = Nat.card K by
          exact Subgroup.card_subtype H K]
        exact hKodd
      have hKXcomm :
          ∀ h : H, (h : X) * x * (h : X)⁻¹ * x⁻¹ ∈ KX := by
        intro h
        refine ⟨h * xH * h⁻¹ * xH⁻¹, hKcomm h, ?_⟩
        rfl
      exact normal_overgroup_lifting hx hx2 H KX hxH hKXH
        hKXnormal hKXodd hKXcomm
  termination_by Nat.card X
  decreasing_by
    · exact hYX
    · simpa only [Nat.card_eq_fintype_card] using hcard
  exact go G t ht ht2

end ZStar.InductiveTerminal

end CFSG
