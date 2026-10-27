module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankInv
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Seven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankMax

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem inPiStar_of_hasReflections (F : FanTree Γ G) {T : Track Γ G} (hPi : TrackInPi T)
    (hrefl : T.HasReflections) : InPiStar T := by
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have halt : valence Γ (T.line.vert 0) ≠ valence Γ (T.line.vert 1) :=
    F.alternating _ _ (T.line.adj 0)
  obtain ⟨d, hd⟩ : ∃ d : ℤ, valence Γ (T.line.vert d) = 3 := by
    rcases hval (T.line.vert 0) with h0 | h0
    · exact ⟨0, h0⟩
    · exact ⟨1, by have := hval (T.line.vert 1); omega⟩
  obtain ⟨f, hf⟩ := hrefl d
  have hfv : ∀ j, f • T.line.vert j = T.line.vert (2 * d - j) := fun j => by
    have := hf.2 (j - d)
    rwa [show d + (j - d) = j by omega, show d - (j - d) = 2 * d - j by omega] at this
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf.1
  refine ⟨hPi, d, f, hd, mem_normalizer_omega1 (fun h hh => ?_) (fun h hh => ?_), ?_⟩
  · exact (T.conj_mem_fixer_reflect hfv).2 hh
  · have := (T.conj_mem_fixer_reflect hfv).2 hh
    rw [hfinv] at this ⊢
    exact this
  · exact ⟨hf.1, hf.fixes, hf.2 1, hf.2 2⟩

theorem fan48_1 (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (T₀ : Track Γ G)
    (h : T₀.fixer ≠ ⊥) : ∃ T' : Track Γ G, PushReach T₀ T' ∧ InPiStar T' := by
  obtain ⟨T, hT, hne, hYmax, hrc⟩ := exists_maxRank F T₀ h
  have hPi : TrackInPi T := ⟨hne, fun T' hprec hr => hrc T' (PushReach.single hprec) hr⟩
  by_cases hrefl : T.HasReflections
  · exact ⟨T, hT, inPiStar_of_hasReflections F hPi hrefl⟩
  obtain ⟨a, b, hmax⟩ := fan42_2a_max T F h40
  have hα3 : valence Γ (T.line.vert a) = 3 := fan47 T F h40 hPi hmax.1 (Or.inl rfl)
  obtain ⟨hLam, -⟩ := fan45_2_lam T F hne hPi.2 hmax.1 (c := a) (Or.inl rfl)
  obtain ⟨t, y, htL, hyL, ht2, htβ, hyα, hyy⟩ :=
    exists_t_y F (T.line.adj a) (T.line.nb a) hLam hα3 h28
  have hcross : CrossPair (T.line.vert a) (T.line.vert (a + 1)) t y :=
    ⟨MulAction.mem_stabilizer_iff.1 htL.2, htβ, MulAction.mem_stabilizer_iff.1 hyL.2, hyα⟩
  have hab : Γ.Adj (T.line.vert a) (T.line.vert (a + 1)) := T.line.adj a
  have e1 := trackOfPair_vert_one F.adj_smul hab hcross
  have e2 := trackOfPair_vert_two F.adj_smul hab hcross
  have eτ := trackOfPair_τ F.adj_smul hab hcross
  have hlen := trackOfPair_lenTwo F.adj_smul hab hcross ht2 hyy
  generalize trackOfPair F.adj_smul hab hcross = T' at e1 e2 eτ hlen
  have hτ : T'.τ ∈ Subgroup.normalizer (omega1 T.fixer : Set G) := by
    rw [eτ]
    exact Subgroup.mul_mem _ hyL.1 htL.1
  have hY0 : omega1 T.fixer ≠ ⊥ := by
    obtain ⟨x, hx, hx1, hx2⟩ := T.exists_involution_of_fixer_ne_bot F hne
    intro hbot
    have : x ∈ omega1 T.fixer := Subgroup.subset_closure ⟨hx, hx2⟩
    rw [hbot] at this
    exact hx1 (Subgroup.mem_bot.1 this)
  have hYle : omega1 T.fixer ≤ T'.fixer := by
    refine T'.le_fixer_of_normalizer hτ (fun u hu => ?_) (fun u hu => ?_)
    · rw [e1]
      exact (T.mem_fixer).1 (omega1_le _ hu) a
    · rw [e2]
      exact (T.mem_fixer).1 (omega1_le _ hu) (a + 1)
  have hprec : TrackPrec T T' := by
    refine ⟨omega1_le_omega1_of_inv fun x hx hx2 =>
      hYle (Subgroup.subset_closure ⟨hx, hx2⟩), T.line.vert a, T.line.vert (a + 1), hab,
      ⟨a, rfl⟩, ⟨a + 1, rfl⟩, ⟨1, e1⟩, ⟨2, e2⟩⟩
  have hreach : PushReach T T' := PushReach.single hprec
  have hYeq : omega1 T'.fixer = omega1 T.fixer := hYmax T' hreach
  refine ⟨T', hT.trans hreach, ⟨?_, fun T'' hprec' hr => ?_⟩, 1, t, ?_, ?_, hlen⟩
  · intro hbot
    exact hY0 (le_bot_iff.1 (hYle.trans (le_of_eq hbot)))
  · exact absurd (hrc T'' (hreach.trans (PushReach.single hprec')) hr) hrefl
  · rw [e1]
    exact hα3
  · rw [hYeq]
    exact htL.1

end CFSG.Quasithin.Fan86
