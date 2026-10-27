module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec3Seven

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def lineK (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (ℓ : Line Γ)
    (i : ℤ) : Subgroup G :=
  nbrStab Γ G (ℓ.vert i)

@[expose] def LS4 (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (ℓ : Line Γ)
    (b : ℤ) : Prop :=
  ∀ g : G, g ∈ lineK Γ G ℓ (b + 1) → g ∈ lineK Γ G ℓ (b + 2) → g ∈ lineK Γ G ℓ (b + 3) →
    g ∈ lineK Γ G ℓ b

@[expose] def RS4 (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (ℓ : Line Γ)
    (b : ℤ) : Prop :=
  ∀ g : G, g ∈ lineK Γ G ℓ (b + 1) → g ∈ lineK Γ G ℓ (b + 2) → g ∈ lineK Γ G ℓ (b + 3) →
    g ∈ lineK Γ G ℓ (b + 4)

theorem arc_vert (ℓ : Line Γ) (d : ℤ) (n m : ℕ) : (ℓ.arc d n).vert m = ℓ.vert (d + m) := rfl

theorem stabRange_four_iff (F : FanTree Γ G) {n i : ℕ} (P : Arc Γ n) (hi : i + 4 ≤ n) (g : G) :
    g ∈ stabRange G P.vert i (i + 4) ↔ g ∈ nbrStab Γ G (P.vert (i + 1)) ∧
      g ∈ nbrStab Γ G (P.vert (i + 2)) ∧ g ∈ nbrStab Γ G (P.vert (i + 3)) := by
  rw [F.mem_stabRange_iff_nbrStab (by omega) (fun m _ hm => P.adj m (by omega))
    (fun m _ hm => P.nb m (by omega))]
  constructor
  · intro h
    exact ⟨h (i + 1) (by omega) (by omega), h (i + 2) (by omega) (by omega),
      h (i + 3) (by omega) (by omega)⟩
  · rintro ⟨h1, h2, h3⟩ m hm1 hm2
    obtain rfl | rfl | rfl : m = i + 1 ∨ m = i + 2 ∨ m = i + 3 := by omega
    exacts [h1, h2, h3]

theorem leftSingular_four_iff (F : FanTree Γ G) {n i : ℕ} (P : Arc Γ n) (hi : i + 4 ≤ n) :
    LeftSingular Γ G P.vert i (i + 4) ↔
      ∀ g : G, g ∈ nbrStab Γ G (P.vert (i + 1)) → g ∈ nbrStab Γ G (P.vert (i + 2)) →
        g ∈ nbrStab Γ G (P.vert (i + 3)) → g ∈ nbrStab Γ G (P.vert i) := by
  have hstab := stabRange_four_iff F P hi
  constructor
  · rintro ⟨w, hw, hwne, hfix⟩ g h1 h2 h3
    have hg : g ∈ stabRange G P.vert i (i + 4) := (hstab g).2 ⟨h1, h2, h3⟩
    have hgw := hfix g hg
    have hg1 : g • P.vert (i + 1) = P.vert (i + 1) :=
      mem_stabRange.1 hg (i + 1) (by omega) (by omega)
    exact F.fix_two_nbrs hw (P.adj i (by omega)) hwne hgw hg1
  · intro H
    obtain ⟨w, hw, hwne⟩ := F.exists_adj_ne (P.vert i) (P.vert (i + 1))
    refine ⟨w, hw, hwne, fun g hg => ?_⟩
    obtain ⟨h1, h2, h3⟩ := (hstab g).1 hg
    exact mem_nbrStab.1 (H g h1 h2 h3) w hw

theorem rightSingular_four_iff (F : FanTree Γ G) {n i : ℕ} (P : Arc Γ n) (hi : i + 4 ≤ n) :
    RightSingular Γ G P.vert i (i + 4) ↔
      ∀ g : G, g ∈ nbrStab Γ G (P.vert (i + 1)) → g ∈ nbrStab Γ G (P.vert (i + 2)) →
        g ∈ nbrStab Γ G (P.vert (i + 3)) → g ∈ nbrStab Γ G (P.vert (i + 4)) := by
  have hstab := stabRange_four_iff F P hi
  have e : i + 4 - 1 = i + 3 := by omega
  have h34 : Γ.Adj (P.vert (i + 4)) (P.vert (i + 3)) := (P.adj (i + 3) (by omega)).symm
  unfold RightSingular
  rw [e]
  constructor
  · rintro ⟨w, hw, hwne, hfix⟩ g h1 h2 h3
    have hg : g ∈ stabRange G P.vert i (i + 4) := (hstab g).2 ⟨h1, h2, h3⟩
    have hgw := hfix g hg
    have hg3 : g • P.vert (i + 3) = P.vert (i + 3) :=
      mem_stabRange.1 hg (i + 3) (by omega) (by omega)
    exact F.fix_two_nbrs hw h34 hwne hgw hg3
  · intro H
    obtain ⟨w, hw, hwne⟩ := F.exists_adj_ne (P.vert (i + 4)) (P.vert (i + 3))
    refine ⟨w, hw, hwne, fun g hg => ?_⟩
    obtain ⟨h1, h2, h3⟩ := (hstab g).1 hg
    exact mem_nbrStab.1 (H g h1 h2 h3) w hw

theorem leftSingular_arc_iff (F : FanTree Γ G) (ℓ : Line Γ) (d : ℤ) {n i : ℕ} (hi : i + 4 ≤ n) :
    LeftSingular Γ G (ℓ.arc d n).vert i (i + 4) ↔ LS4 Γ G ℓ (d + i) := by
  rw [leftSingular_four_iff F (ℓ.arc d n) hi]
  have e1 : d + ((i + 1 : ℕ) : ℤ) = d + i + 1 := by push_cast; ring
  have e2 : d + ((i + 2 : ℕ) : ℤ) = d + i + 2 := by push_cast; ring
  have e3 : d + ((i + 3 : ℕ) : ℤ) = d + i + 3 := by push_cast; ring
  simp only [LS4, lineK, arc_vert, e1, e2, e3]

theorem rightSingular_arc_iff (F : FanTree Γ G) (ℓ : Line Γ) (d : ℤ) {n i : ℕ} (hi : i + 4 ≤ n) :
    RightSingular Γ G (ℓ.arc d n).vert i (i + 4) ↔ RS4 Γ G ℓ (d + i) := by
  rw [rightSingular_four_iff F (ℓ.arc d n) hi]
  have e1 : d + ((i + 1 : ℕ) : ℤ) = d + i + 1 := by push_cast; ring
  have e2 : d + ((i + 2 : ℕ) : ℤ) = d + i + 2 := by push_cast; ring
  have e3 : d + ((i + 3 : ℕ) : ℤ) = d + i + 3 := by push_cast; ring
  have e4 : d + ((i + 4 : ℕ) : ℤ) = d + i + 4 := by push_cast; ring
  simp only [RS4, lineK, arc_vert, e1, e2, e3, e4]

theorem rightSingular_rev_of_leftSingular {k : ℕ} (hk : 1 ≤ k) (P : Arc Γ k)
    (h : LeftSingular Γ G P.vert 0 k) : RightSingular Γ G P.rev.vert 0 k := by
  obtain ⟨w, hw, hwne, hfix⟩ := h
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa using hw
  · rw [Arc.rev_vert, show k - (k - 1) = 1 by omega]
    exact hwne
  · intro g hg
    apply hfix
    rw [mem_stabRange] at hg ⊢
    intro m hm0 hmk
    have := hg (k - m) (by omega) (by omega)
    rwa [Arc.rev_vert, show k - (k - m) = m by omega] at this

end Sec3Seven

end CFSG.Quasithin.Fan86
