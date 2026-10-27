module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Orb1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem relIndex_conj (F : FanTree Γ G) (g : G) (p q r : V) :
    (nbrStab Γ G (g • p)).relIndex (nbrStab Γ G (g • q) ⊓ MulAction.stabilizer G (g • r)) =
      (nbrStab Γ G p).relIndex (nbrStab Γ G q ⊓ MulAction.stabilizer G r) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj g).injective
  rw [F.nbrStab_smul, F.nbrStab_smul, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← Subgroup.map_inf _ _ f hinj]
  exact Subgroup.relIndex_map_map_of_injective _ _ hinj

theorem stage_three (F : FanTree Γ G) {v : ℕ → V} (hadj : ∀ j, Γ.Adj (v j) (v (j + 1)))
    (hnb : ∀ j, v j ≠ v (j + 2)) {j : ℕ} (hj : 1 ≤ j) (hv : valence Γ (v j) = 3) :
    (nbrStab Γ G (v j)).relIndex (nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v j)) ≤ 2 := by
  have hadj1 : Γ.Adj (v j) (v (j - 1)) := by
    have := (hadj (j - 1)).symm
    rwa [show j - 1 + 1 = j by omega] at this
  have hle : nbrStab Γ G (v 0) ⊓ MulAction.stabilizer G (v j) ≤
      MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1)) := by
    rintro g ⟨hg0, hgj⟩
    refine ⟨hgj, MulAction.mem_stabilizer_iff.2 ?_⟩
    exact F.ray_fixes hadj hnb (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg0))
      (MulAction.mem_stabilizer_iff.1 hgj) (j - 1) (by omega)
  have hfin : Finite ↥(MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1))) :=
    F.finite_stabilizer_inf (v j) (v (j - 1))
  exact (Subgroup.relIndex_le_of_le_right hle (FanTree.relIndex_ne_zero_of_finite _ _)).trans
    (edge_relIndex_le_two F hv hadj1)

variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

@[expose] def pv (T : Track Γ G) (a : ℤ) (j : ℕ) : V := xv T a (6 - (j : ℤ))

theorem pv_adj (T : Track Γ G) (a : ℤ) (j : ℕ) : Γ.Adj (pv T a j) (pv T a (j + 1)) := by
  have h := xv_adj' T a (5 - (j : ℤ))
  have e1 : (5 : ℤ) - j + 1 = 6 - j := by ring
  have e2 : (5 : ℤ) - j = 6 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2] at h
  exact h

theorem pv_nb (T : Track Γ G) (a : ℤ) (j : ℕ) : pv T a j ≠ pv T a (j + 2) := by
  have h := xv_ne T a (4 - (j : ℤ))
  have e1 : (4 : ℤ) - j + 2 = 6 - j := by ring
  have e2 : (4 : ℤ) - j = 6 - ((j + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2] at h
  exact h.symm

theorem mem_subFixer_iff (T : Track Γ G) (a : ℤ) (g : G) :
    g ∈ T.subFixer (a + 2) (a + 5) ↔ ∀ i : ℤ, 1 ≤ i → i ≤ 4 → g • xv T a i = xv T a i := by
  rw [Track.mem_subFixer]
  constructor
  · intro h i h1 h2
    exact h (a + 1 + i) (by omega) (by omega)
  · intro h j h1 h2
    have h' := h (j - a - 1) (by omega) (by omega)
    have e : a + 1 + (j - a - 1) = j := by ring
    unfold xv at h'
    rwa [e] at h'

theorem subFixer_eq (F : FanTree Γ G) (T : Track Γ G) (a : ℤ) :
    T.subFixer (a + 2) (a + 5) =
      nbrStab Γ G (xv T a 2) ⊓ MulAction.stabilizer G (xv T a 4) := by
  ext g
  rw [mem_subFixer_iff, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨F.fix_two_nbrs (xv_adj' T a 1) (xv_adj T a 2) ?_ (h 1 le_rfl (by norm_num))
      (h 3 (by norm_num) (by norm_num)), MulAction.mem_stabilizer_iff.2 (h 4 (by norm_num)
      le_rfl)⟩
    intro e
    have := xv_inj F T a e
    omega
  · rintro ⟨hK, hs⟩ i h1 h2
    have hg : ∀ j : ℤ, Γ.Adj (xv T a 2) (xv T a j) → g • xv T a j = xv T a j :=
      fun j hj => mem_nbrStab.1 hK _ hj
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact hg 1 (xv_adj' T a 1)
    · exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hK)
    · exact hg 3 (xv_adj T a 2)
    · exact MulAction.mem_stabilizer_iff.1 hs

theorem nOrb_eq_relIndex (F : FanTree Γ G) (T : Track Γ G) (a : ℤ) :
    nOrb T a = (nbrStab Γ G (xv T a 4)).relIndex (T.subFixer (a + 2) (a + 5)) := by
  rw [nOrb, ncard_orbit_eq_relIndex,
    ← Subgroup.inf_relIndex_right (MulAction.stabilizer G (xv T a 5)),
    ← Subgroup.inf_relIndex_right (nbrStab Γ G (xv T a 4))]
  congr 1
  ext g
  constructor
  · rintro ⟨h5, hP⟩
    refine ⟨F.fix_two_nbrs (xv_adj' T a 3) (xv_adj T a 4) ?_
      ((mem_subFixer_iff T a g).1 hP 3 (by norm_num) (by norm_num))
      (MulAction.mem_stabilizer_iff.1 h5), hP⟩
    intro e
    have := xv_inj F T a e
    omega
  · rintro ⟨hK, hP⟩
    exact ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK _ (xv_adj T a 4)), hP⟩

theorem exists_swap_x2_x4 (S : B2Set F L T a) :
    ∃ ρ : G, ρ • xv T a 2 = xv T a 4 ∧ ρ • xv T a 4 = xv T a 2 := by
  have hv3 : valence Γ (xv T a 3) = 3 := by simpa using S.val_odd 1
  have h32 : Γ.Adj (xv T a 3) (xv T a 2) := xv_adj' T a 2
  have h34 : Γ.Adj (xv T a 3) (xv T a 4) := xv_adj T a 3
  have hne : xv T a 2 ≠ xv T a 4 := xv_ne T a 2
  obtain ⟨c, hc, hc2, hc4⟩ := exists_third_neighbor hv3 h32 h34 hne
  have hcadj : Γ.Adj (xv T a 3) c := by
    have : c ∈ Γ.neighborSet (xv T a 3) := by
      rw [hc]
      simp
    exact this
  obtain ⟨y, -, -, hy2, hy4⟩ := P58.exists_swap F S.h40 hv3 h32 h34 hcadj hne hc2 hc4
  exact ⟨y, hy2, hy4⟩

theorem stage_x4 (S : B2Set F L T a) :
    (nbrStab Γ G (xv T a 4)).relIndex
      (nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 4)) = nOrb T a := by
  obtain ⟨g, hg, hgx⟩ := exists_stab_smul_br F S.h40 (d := xv T a 4) (S.val_even 2)
    (xv_br_fwd T a 4) (xv_br_bwd T a 2)
  have h4 : g • xv T a 4 = xv T a 4 := MulAction.mem_stabilizer_iff.1 hg
  have hgx' : g • xv T a 6 = xv T a 2 := hgx
  have hconj := relIndex_conj F g (xv T a 4) (xv T a 6) (xv T a 4)
  rw [h4, hgx'] at hconj
  rw [← hconj, nOrb_eq_relIndex F T a, subFixer_eq F T a]

theorem stage_x2 (S : B2Set F L T a) :
    (nbrStab Γ G (xv T a 2)).relIndex
      (nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 2)) ≤ nOrb T a := by
  obtain ⟨ρ, hρ2, hρ4⟩ := exists_swap_x2_x4 S
  have hle : nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 2) ≤
      nbrStab Γ G (xv T a 4) ⊓ MulAction.stabilizer G (xv T a 2) := by
    rintro g ⟨hg6, hg2⟩
    refine ⟨?_, hg2⟩
    have h0 : g • pv T a 0 = pv T a 0 :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg6)
    have h4 : g • pv T a 4 = pv T a 4 := MulAction.mem_stabilizer_iff.1 hg2
    have hfix := F.ray_fixes (pv_adj T a) (pv_nb T a) h0 h4
    refine F.fix_two_nbrs (xv_adj' T a 3) (xv_adj T a 4) ?_ (hfix 3 (by norm_num))
      (hfix 1 (by norm_num))
    intro e
    have := xv_inj F T a e
    omega
  have hfin : Finite ↥(nbrStab Γ G (xv T a 4) ⊓ MulAction.stabilizer G (xv T a 2)) := by
    have := F.finite_nbrStab (xv T a 4)
    exact Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hmono := Subgroup.relIndex_le_of_le_right hle
    (FanTree.relIndex_ne_zero_of_finite (nbrStab Γ G (xv T a 2)) _)
  have hconj := relIndex_conj F ρ (xv T a 4) (xv T a 2) (xv T a 4)
  rw [hρ4, hρ2] at hconj
  calc (nbrStab Γ G (xv T a 2)).relIndex
        (nbrStab Γ G (xv T a 6) ⊓ MulAction.stabilizer G (xv T a 2))
      ≤ (nbrStab Γ G (xv T a 2)).relIndex
        (nbrStab Γ G (xv T a 4) ⊓ MulAction.stabilizer G (xv T a 2)) := hmono
    _ = (nbrStab Γ G (xv T a 4)).relIndex
        (nbrStab Γ G (xv T a 2) ⊓ MulAction.stabilizer G (xv T a 4)) := hconj
    _ = nOrb T a := by rw [nOrb_eq_relIndex F T a, subFixer_eq F T a]

end P518

end CFSG.Quasithin.Fan86
