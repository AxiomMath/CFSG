module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem rev_arc_vert (ℓ : Line Γ) (a : ℤ) {k i : ℕ} (hi : i ≤ k) :
    (ℓ.rev.arc a k).vert i = (ℓ.arc (-a - k) k).vert (k - i) := by
  simp only [Line.arc, Line.rev_vert]
  congr 1
  push_cast [Nat.cast_sub hi]
  ring

theorem leftSingular_of_rev_rightSingular {k : ℕ} (hk : 1 ≤ k) (ℓ : Line Γ) (a : ℤ)
    (h : RightSingular Γ G (ℓ.rev.arc a k).vert 0 k) :
    LeftSingular Γ G (ℓ.arc (-a - k) k).vert 0 k := by
  obtain ⟨w, hw, hne, hfix⟩ := h
  refine ⟨w, ?_, ?_, ?_⟩
  · rwa [rev_arc_vert ℓ a le_rfl, Nat.sub_self] at hw
  · have e : k - (k - 1) = 1 := by omega
    rwa [rev_arc_vert ℓ a (Nat.sub_le k 1), e] at hne
  · intro g hg
    refine hfix g ?_
    rw [mem_stabRange] at hg ⊢
    intro m _ hm
    rw [rev_arc_vert ℓ a hm]
    exact hg (k - m) (Nat.zero_le _) (Nat.sub_le _ _)

theorem rightSingular_of_rev_leftSingular {k : ℕ} (hk : 1 ≤ k) (ℓ : Line Γ) (a : ℤ)
    (h : LeftSingular Γ G (ℓ.rev.arc a k).vert 0 k) :
    RightSingular Γ G (ℓ.arc (-a - k) k).vert 0 k := by
  obtain ⟨w, hw, hne, hfix⟩ := h
  refine ⟨w, ?_, ?_, ?_⟩
  · rwa [rev_arc_vert ℓ a (Nat.zero_le _), Nat.sub_zero] at hw
  · rw [Nat.zero_add, rev_arc_vert ℓ a hk] at hne
    exact hne
  · intro g hg
    refine hfix g ?_
    rw [mem_stabRange] at hg ⊢
    intro m _ hm
    rw [rev_arc_vert ℓ a hm]
    exact hg (k - m) (Nat.zero_le _) (Nat.sub_le _ _)

theorem lineSingLe_of_rev {ℓ : Line Γ} {N : ℕ} (h : LineSingLe Γ G ℓ.rev N) :
    LineSingLe Γ G ℓ N := by
  obtain ⟨k, a, hk1, hkN, hs⟩ := h
  refine ⟨k, -a - k, hk1, hkN, ?_⟩
  rcases hs with hR | hL
  · exact Or.inr (leftSingular_of_rev_rightSingular hk1 ℓ a hR)
  · exact Or.inl (rightSingular_of_rev_leftSingular hk1 ℓ a hL)

end CFSG.Quasithin.Fan86
