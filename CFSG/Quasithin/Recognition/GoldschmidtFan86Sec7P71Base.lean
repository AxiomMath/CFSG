module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tight

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem arc_vert (ℓ : Line Γ) (a : ℤ) (n k : ℕ) : (ℓ.arc a n).vert k = ℓ.vert (a + k) := rfl

theorem exists_valence_five (F : FanTree Γ G) (T : Track Γ G) :
    ∃ c : ℤ, Fan86.valence Γ (T.line.vert c) = 5 := by
  rcases F.valence (T.line.vert 0) with h | h
  · exact ⟨1, valence_three_five F (T.line.adj 0) h⟩
  · exact ⟨0, h⟩

theorem exists_x0 (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (T : Track Γ G) (hT : InXi T) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) :
    ∃ x : G, x ∈ Subgroup.closure
      ({L.z (T.line.vert (c - 4)), L.z (T.line.vert (c + 4))} : Set G) ∧ orderOf x = 5 ∧
        x ∈ MulAction.stabilizer G (T.line.vert c) := by
  obtain ⟨hm4, hp4⟩ := valence_line_pm_four F T h5
  have fs := fixIdx_label F L h40 h62 h63 T hT hm4
  have ft := fixIdx_label F L h40 h62 h63 T hT hp4
  have s_fix : ∀ i : ℤ, c - 8 ≤ i → i ≤ c →
      L.z (T.line.vert (c - 4)) • T.line.vert i = T.line.vert i :=
    fun i h1 h2 => (fs i).2 ⟨by omega, by omega⟩
  have t_fix : ∀ i : ℤ, c ≤ i → i ≤ c + 8 →
      L.z (T.line.vert (c + 4)) • T.line.vert i = T.line.vert i :=
    fun i h1 h2 => (ft i).2 ⟨by omega, by omega⟩
  have s_mov : L.z (T.line.vert (c - 4)) • T.line.vert (c + 1) ≠ T.line.vert (c + 1) :=
    fun h => by have := (fs (c + 1)).1 h; omega
  have t_mov : L.z (T.line.vert (c + 4)) • T.line.vert (c - 1) ≠ T.line.vert (c - 1) :=
    fun h => by have := (ft (c - 1)).1 h; omega
  have h1 : Γ.Adj (T.line.vert c) (T.line.vert (c - 1)) := by
    have := (T.line.adj (c - 1)).symm
    rwa [sub_add_cancel] at this
  have hs : L.z (T.line.vert (c - 4)) ∈ MulAction.stabilizer G (T.line.vert c) :=
    MulAction.mem_stabilizer_iff.2 (s_fix c (by omega) le_rfl)
  have ht : L.z (T.line.vert (c + 4)) ∈ MulAction.stabilizer G (T.line.vert c) :=
    MulAction.mem_stabilizer_iff.2 (t_fix c le_rfl (by omega))
  obtain ⟨x, hx, hxo⟩ := exists_order_five F h5 h1 (T.line.adj c) hs ht
    (L.isCentral _ hm4).2.2.1 (L.isCentral _ hp4).2.2.1 (s_fix (c - 1) (by omega) (by omega))
    s_mov (t_fix (c + 1) (by omega) (by omega)) t_mov
  refine ⟨x, hx, hxo, ?_⟩
  have hle : Subgroup.closure
      ({L.z (T.line.vert (c - 4)), L.z (T.line.vert (c + 4))} : Set G) ≤
      MulAction.stabilizer G (T.line.vert c) := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hy]
      exact hs
    · rw [hy]
      exact ht
  exact hle hx

theorem arcTrans_of_track (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (h65 : Fan65 F) (T : Track Γ G) (hT : InXi T) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) : ArcTrans Γ G := by
  obtain ⟨x₀, hx₀, hx₀o, hx₀stab⟩ := exists_x0 F L h40 h62 h63 T hT h5
  obtain ⟨hm4, hp4⟩ := valence_line_pm_four F T h5
  have hR0 : (T.line.arc (c - 4) 8).vert 0 = T.line.vert (c - 4) := by
    rw [arc_vert]
    simp
  have hR4 : (T.line.arc (c - 4) 8).vert 4 = T.line.vert c := by
    rw [arc_vert]
    congr 1
    push_cast
    ring
  have hR8 : (T.line.arc (c - 4) 8).vert 8 = T.line.vert (c + 4) := by
    rw [arc_vert]
    congr 1
    push_cast
    ring
  have hcent : ∀ g ∈ (T.line.arc (c - 4) 8).stab G, g * x₀ = x₀ * g := by
    intro g hg
    rw [Arc.mem_stab] at hg
    have g0 := hg 0 (by norm_num)
    have g8 := hg 8 (by norm_num)
    rw [hR0] at g0
    rw [hR8] at g8
    have cs : g * L.z (T.line.vert (c - 4)) = L.z (T.line.vert (c - 4)) * g := by
      have := L.equivariant g (T.line.vert (c - 4)) hm4
      rw [g0] at this
      exact (eq_mul_inv_iff_mul_eq.1 this).symm
    have ct : g * L.z (T.line.vert (c + 4)) = L.z (T.line.vert (c + 4)) * g := by
      have := L.equivariant g (T.line.vert (c + 4)) hp4
      rw [g8] at this
      exact (eq_mul_inv_iff_mul_eq.1 this).symm
    have hsub : Subgroup.closure
        ({L.z (T.line.vert (c - 4)), L.z (T.line.vert (c + 4))} : Set G) ≤
        Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · rw [hy]
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact cs
      · rw [hy]
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact ct
    exact Subgroup.mem_centralizer_iff.1 (hsub hx₀) g rfl
  have h5R : Fan86.valence Γ ((T.line.arc (c - 4) 8).vert 4) = 5 := by
    rw [hR4]
    exact h5
  have hK := h65.1 _ h5R x₀ (by rw [hR4]; exact hx₀stab) hx₀o
  exact arcTrans_of_tight F _ h5R (R_tight F _ h5R hcent hK)

theorem exists_moved_arc (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (T : Track Γ G) (hT : InXi T) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) :
    ∃ R : Arc Γ 8, Fan86.valence Γ (R.vert 0) = 5 ∧ L.z (R.vert 0) • R.vert 5 ≠ R.vert 5 := by
  refine ⟨T.line.arc c 8, ?_, ?_⟩
  · rw [arc_vert]
    simpa using h5
  · rw [arc_vert, arc_vert]
    simp only [Nat.cast_zero, add_zero]
    intro h
    have := (fixIdx_label F L h40 h62 h63 T hT h5 (c + ((5 : ℕ) : ℤ))).1 h
    push_cast at this
    omega

end P71

end CFSG.Quasithin.Fan86
