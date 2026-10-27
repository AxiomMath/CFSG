module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Lin

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P63

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

namespace LineData

variable (D : LineData L ℓ j) (F : FanTree Γ G)
include D F

theorem branches {z : G} {m : V} (hm : Γ.Adj (ℓ.vert (j + 1)) m) (hm1 : m ≠ ℓ.vert j)
    (hz1 : z • ℓ.vert (j + 1) = ℓ.vert (j + 1))
    (hzm : z • ℓ.vert (j + 2) = m) {g : G}
    (hg : ∀ i, j + 1 ≤ i → i ≤ j + 4 → g • ℓ.vert i = ℓ.vert i) (hgm : g • ℓ.vert j = m) :
    valence Γ m = 5 ∧ valence Γ (z • ℓ.vert (j + 4)) = 5 ∧
      valence Γ (L.z (ℓ.vert (j + 4)) • z • ℓ.vert (j + 4)) = 5 ∧
      Γ.dist m (ℓ.vert j) = 2 ∧ Γ.dist m (z • ℓ.vert (j + 4)) = 2 ∧
      Γ.dist m (L.z (ℓ.vert (j + 4)) • z • ℓ.vert (j + 4)) = 2 ∧
      Γ.dist (z • ℓ.vert (j + 4)) (L.z (ℓ.vert (j + 4)) • z • ℓ.vert (j + 4)) = 4 := by
  set a := L.z (ℓ.vert (j + 4)) with ha
  set m' := z • ℓ.vert (j + 3) with hm'
  set w₁ := z • ℓ.vert (j + 4) with hw₁
  have hvm : valence Γ m = 5 := F.val5_of_adj_val3 hm D.val
  have hadj3 : Γ.Adj (ℓ.vert (j + 2)) (ℓ.vert (j + 3)) := by
    have := ℓ.adj (j + 2)
    rwa [show j + 2 + 1 = j + 3 by omega] at this
  have hadj4 : Γ.Adj (ℓ.vert (j + 3)) (ℓ.vert (j + 4)) := by
    have := ℓ.adj (j + 3)
    rwa [show j + 3 + 1 = j + 4 by omega] at this
  have hmm' : Γ.Adj m m' := by
    have := (F.adj_smul z _ _).2 hadj3
    rwa [hzm] at this
  have hm'w : Γ.Adj m' w₁ := (F.adj_smul z _ _).2 hadj4
  have hwm : w₁ ≠ m := by
    intro h
    rw [← hzm] at h
    exact ℓ.nb (j + 2) (by
      rw [show j + 2 + 2 = j + 4 by omega]
      exact (MulAction.injective z h).symm)
  have hm'1 : m' ≠ ℓ.vert (j + 1) := by
    intro h
    rw [← hz1] at h
    have := MulAction.injective z h
    exact ℓ.nb (j + 1) (by rw [show j + 1 + 2 = j + 3 by omega]; exact this.symm)
  have br1 : Br Γ m (ℓ.vert (j + 1)) (ℓ.vert j) := ⟨hm.symm, (ℓ.adj j).symm, hm1.symm⟩
  have br2 : Br Γ m m' w₁ := ⟨hmm', hm'w, hwm⟩
  have ham : a • m = m := D.a_fix_m F hm
  have hmov : a • m' ≠ m' := D.moves_nbr_m F hm hg hgm hmm' hm'1
  have hma : Γ.Adj m (a • m') := by
    have := (F.adj_smul a _ _).2 hmm'
    rwa [ham] at this
  have ha1 : a • ℓ.vert (j + 1) = ℓ.vert (j + 1) := D.a_fix F (by omega) (by omega)
  have hm''1 : a • m' ≠ ℓ.vert (j + 1) := by
    intro h
    rw [← ha1] at h
    exact hm'1 (MulAction.injective a h)
  have hw₂ : Γ.Adj (a • m') (a • w₁) := (F.adj_smul a _ _).2 hm'w
  have hw₂m : a • w₁ ≠ m := by
    intro h
    rw [← ham] at h
    exact hwm (MulAction.injective a h)
  have br3 : Br Γ m (a • m') (a • w₁) := ⟨hma, hw₂, hw₂m⟩
  have hv1 := (Br.valence F hvm br2).2
  have hv2 := (Br.valence F hvm br3).2
  refine ⟨hvm, hv1, hv2, Br.dist_two F br1, Br.dist_two F br2, Br.dist_two F br3, ?_⟩
  exact dist_four F br2 br3 (Ne.symm hmov)

end LineData

end P63

end CFSG.Quasithin.Fan86
