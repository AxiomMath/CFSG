module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P63

structure LineData (L : ZLab Γ G) (ℓ : Line Γ) (j : ℤ) : Prop where
  val : valence Γ (ℓ.vert (j + 1)) = 3
  fix : ∀ c i : ℤ, valence Γ (ℓ.vert c) = 5 →
    (L.z (ℓ.vert c) • ℓ.vert i = ℓ.vert i ↔ c - 4 ≤ i ∧ i ≤ c + 4)

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

namespace LineData

variable (D : LineData L ℓ j) (F : FanTree Γ G)
include D F

theorem val_five_j : valence Γ (ℓ.vert j) = 5 := by
  have h1 : valence Γ (ℓ.vert j) ≠ valence Γ (ℓ.vert (j + 1)) := F.alternating _ _ (ℓ.adj j)
  have h2 : valence Γ (ℓ.vert j) = 3 ∨ valence Γ (ℓ.vert j) = 5 := F.valence _
  have := D.val
  omega

theorem val_five_j2 : valence Γ (ℓ.vert (j + 2)) = 5 := by
  rw [ℓ.valence_add_two F j]
  exact D.val_five_j F

theorem val_five_j4 : valence Γ (ℓ.vert (j + 4)) = 5 := by
  have h : valence Γ (ℓ.vert (j + 2 + 2)) = valence Γ (ℓ.vert (j + 2)) :=
    ℓ.valence_add_two F (j + 2)
  rw [show j + 2 + 2 = j + 4 by omega] at h
  rw [h]
  exact D.val_five_j2 F

theorem a_fix {i : ℤ} (h1 : j ≤ i) (h2 : i ≤ j + 8) :
    L.z (ℓ.vert (j + 4)) • ℓ.vert i = ℓ.vert i :=
  (D.fix (j + 4) i (D.val_five_j4 F)).2 ⟨by omega, by omega⟩

theorem a_move : L.z (ℓ.vert (j + 4)) • ℓ.vert (j - 1) ≠ ℓ.vert (j - 1) := fun h => by
  have := ((D.fix (j + 4) (j - 1) (D.val_five_j4 F)).1 h).1
  omega

theorem a_mem_stab_j : L.z (ℓ.vert (j + 4)) ∈ MulAction.stabilizer G (ℓ.vert j) :=
  MulAction.mem_stabilizer_iff.2 (D.a_fix F le_rfl (by omega))

theorem a_not_mem_nbrStab_j : L.z (ℓ.vert (j + 4)) ∉ nbrStab Γ G (ℓ.vert j) := fun hK =>
  D.a_move F (mem_nbrStab.1 hK _ (ℓ.adj_pred j))

end LineData

omit L in
theorem adj_j_j2 (ℓ : Line Γ) (j : ℤ) : Γ.Adj (ℓ.vert (j + 1)) (ℓ.vert (j + 2)) := by
  have := ℓ.adj (j + 1)
  rwa [show j + 1 + 1 = j + 2 by omega] at this

namespace LineData

variable (D : LineData L ℓ j) (F : FanTree Γ G) {m : V}
include D F

theorem nbrSet_lam1 (hm : Γ.Adj (ℓ.vert (j + 1)) m) (hm1 : m ≠ ℓ.vert j)
    (hm2 : m ≠ ℓ.vert (j + 2)) :
    Γ.neighborSet (ℓ.vert (j + 1)) = {ℓ.vert j, ℓ.vert (j + 2), m} :=
  neighborSet_eq_three F D.val (ℓ.adj j).symm (adj_j_j2 ℓ j) hm (ℓ.nb j) hm1.symm hm2.symm

theorem a_fix_m (hm : Γ.Adj (ℓ.vert (j + 1)) m) : L.z (ℓ.vert (j + 4)) • m = m :=
  F.frobenius_two (ℓ.vert (j + 1)) (ℓ.vert j) (ℓ.vert (j + 2)) (ℓ.adj j).symm (adj_j_j2 ℓ j)
    (ℓ.nb j) _ (MulAction.mem_stabilizer_iff.2 (D.a_fix F (by omega) (by omega)))
    (D.a_fix F (by omega) (by omega)) (D.a_fix F (by omega) (by omega)) m hm

theorem a_mem_stab_m (hm : Γ.Adj (ℓ.vert (j + 1)) m) :
    L.z (ℓ.vert (j + 4)) ∈ MulAction.stabilizer G m :=
  MulAction.mem_stabilizer_iff.2 (D.a_fix_m F hm)

theorem exists_swap_arc (h40 : Fan40 F) (hm : Γ.Adj (ℓ.vert (j + 1)) m) (hm1 : m ≠ ℓ.vert j)
    (hm2 : m ≠ ℓ.vert (j + 2)) :
    ∃ g : G, (∀ i, j + 1 ≤ i → i ≤ j + 4 → g • ℓ.vert i = ℓ.vert i) ∧ g • ℓ.vert j = m := by
  obtain ⟨g, hgfix, hgmove⟩ := ℓ.rev.exists_fixer_right' (-(j + 4)) 3 0 3 (by norm_num)
    (lineNSR_of_fan40 h40 ℓ.rev (by norm_num) (by norm_num) (-(j + 4)))
  have hf : ∀ i, j + 1 ≤ i → i ≤ j + 4 → g • ℓ.vert i = ℓ.vert i := by
    intro i h1 h2
    have := hgfix (-i) (by push_cast; omega) (by push_cast; omega)
    simpa using this
  have hmove : g • ℓ.vert j ≠ ℓ.vert j := by
    have e : ℓ.rev.vert (-(j + 4) + ((3 : ℕ) : ℤ) + 1) = ℓ.vert j := by
      rw [Line.rev_vert]
      congr 1
      push_cast
      ring
    rwa [e] at hgmove
  refine ⟨g, hf, ?_⟩
  have hadj : Γ.Adj (ℓ.vert (j + 1)) (g • ℓ.vert j) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj j).symm
    rwa [hf (j + 1) le_rfl (by omega)] at this
  have hmem : g • ℓ.vert j ∈ Γ.neighborSet (ℓ.vert (j + 1)) := hadj
  rw [D.nbrSet_lam1 F hm hm1 hm2] at hmem
  rcases hmem with h | h | h
  · exact absurd h hmove
  · exfalso
    have h2 := hf (j + 2) (by omega) (by omega)
    rw [← h2] at h
    exact ℓ.nb j (MulAction.injective g h)
  · exact h

theorem a_not_mem_nbrStab_m {g : G}
    (hg : ∀ i, j + 1 ≤ i → i ≤ j + 4 → g • ℓ.vert i = ℓ.vert i) (hgm : g • ℓ.vert j = m) :
    L.z (ℓ.vert (j + 4)) ∉ nbrStab Γ G m := by
  intro hK
  have hg4 : g ∈ MulAction.stabilizer G (ℓ.vert (j + 4)) :=
    MulAction.mem_stabilizer_iff.2 (hg _ (by omega) le_rfl)
  have hc := z_comm (L := L) (D.val_five_j4 F) hg4
  have h1 := F.conj_mem_nbrStab_smul g⁻¹ hK
  rw [← hgm, inv_smul_smul] at h1
  have e : g⁻¹ * L.z (ℓ.vert (j + 4)) * g⁻¹⁻¹ = L.z (ℓ.vert (j + 4)) := by
    rw [inv_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  rw [e] at h1
  exact D.a_not_mem_nbrStab_j F h1

theorem moves_nbr_m (hm : Γ.Adj (ℓ.vert (j + 1)) m) {g : G}
    (hg : ∀ i, j + 1 ≤ i → i ≤ j + 4 → g • ℓ.vert i = ℓ.vert i) (hgm : g • ℓ.vert j = m)
    {u : V} (hu : Γ.Adj m u) (hne : u ≠ ℓ.vert (j + 1)) : L.z (ℓ.vert (j + 4)) • u ≠ u :=
  P63.moves_of_fix F (D.a_mem_stab_m F hm) hm.symm hu hne.symm
    (D.a_fix F (by omega) (by omega)) (D.a_not_mem_nbrStab_m F hg hgm)

end LineData

end P63

end CFSG.Quasithin.Fan86
