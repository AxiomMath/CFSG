module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Edge

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem Track.fixer_le_nbrStab (F : FanTree Γ G) (i : ℤ) :
    T.fixer ≤ nbrStab Γ G (T.line.vert i) := by
  intro g hg w hw
  have hf := (T.mem_fixer).1 hg
  exact F.frobenius_two (T.line.vert i) (T.line.vert (i - 1)) (T.line.vert (i + 1))
    (T.adj_pred i) (T.line.adj i) (T.ne_pred_succ i) g (MulAction.mem_stabilizer_iff.2 (hf i))
    (hf (i - 1)) (hf (i + 1)) w hw

theorem Track.nbrStab_le_subFixer_left (F : FanTree Γ G) (c : ℤ) :
    nbrStab Γ G (T.line.vert c) ≤ T.subFixer c (c + 1) := by
  intro g hg
  refine (T.mem_subFixer).2 fun i h1 h2 => ?_
  by_cases hi : i = c
  · subst hi
    exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg)
  · obtain rfl : i = c + 1 := by omega
    exact hg _ (T.line.adj c)

theorem Track.nbrStab_le_subFixer_right (F : FanTree Γ G) (c : ℤ) :
    nbrStab Γ G (T.line.vert (c + 1)) ≤ T.subFixer c (c + 1) := by
  intro g hg
  refine (T.mem_subFixer).2 fun i h1 h2 => ?_
  by_cases hi : i = c + 1
  · subst hi
    exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg)
  · obtain rfl : i = c := by omega
    exact hg _ (T.line.adj i).symm

theorem FanTree.stabilizer_le_normalizer_omega1 (F : FanTree Γ G) (v : V) :
    MulAction.stabilizer G v ≤ Subgroup.normalizer (omega1 (nbrStab Γ G v) : Set G) := by
  intro g hg
  exact mem_normalizer_omega1
    (fun h hh => nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hg) hh)
    (fun h hh => by
      simpa using nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1
        ((MulAction.stabilizer G v).inv_mem hg)) hh)

theorem fan42_1 (F : FanTree Γ G) (h40 : Fan40 F) (c : ℤ) :
    ¬ omega1 (T.subFixer c (c + 1)) ≤ T.fixer := by
  intro hle
  have hK : ∀ i : ℤ, nbrStab Γ G (T.line.vert i) ≤ T.subFixer c (c + 1) →
      omega1 T.fixer = omega1 (nbrStab Γ G (T.line.vert i)) := fun i hi =>
    omega1_eq_of_le_of_omega1_le (T.fixer_le_nbrStab F i) ((omega1_mono hi).trans hle)
  have e₀ := hK c (T.nbrStab_le_subFixer_left F c)
  have e₁ := hK (c + 1) (T.nbrStab_le_subFixer_right F c)
  have hbot : omega1 T.fixer = ⊥ := by
    refine F.eq_bot_of_locTrans (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.adj c)
      (fun u hu => ⟨(T.mem_fixer).1 (omega1_le _ hu) c, (T.mem_fixer).1 (omega1_le _ hu) (c + 1)⟩)
      le_rfl (fun a b ha hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨g, hg, hgab⟩ := F.loc_trans _ a b ha hb
      refine ⟨g, ?_, MulAction.mem_stabilizer_iff.1 hg, hgab⟩
      rw [e₀]
      exact F.stabilizer_le_normalizer_omega1 _ hg
    · obtain ⟨g, hg, hgab⟩ := F.loc_trans _ a b ha hb
      refine ⟨g, ?_, MulAction.mem_stabilizer_iff.1 hg, hgab⟩
      rw [e₁]
      exact F.stabilizer_le_normalizer_omega1 _ hg
  obtain ⟨x, hx, hx1, hx2⟩ := exists_involution_of_le_edge F (T.line.adj c)
    (F.nbrStab_le_edge _ (T.line.adj c)) (F.nbrStab_ne_bot h40 (T.line.vert c))
  have : x ∈ omega1 T.fixer := by
    rw [e₀]
    exact Subgroup.subset_closure ⟨hx, hx2⟩
  rw [hbot] at this
  exact hx1 (Subgroup.mem_bot.1 this)

end CFSG.Quasithin.Fan86
