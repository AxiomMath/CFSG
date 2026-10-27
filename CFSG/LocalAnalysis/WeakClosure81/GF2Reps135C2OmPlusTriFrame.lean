module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriSwap
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped MatrixGroups

section Frame

variable {F : Type} [Field F]

theorem exists_trialityLevis [Finite F] :
    ∃ x' : (Fin 4 → ℤ) → F → spinGroup (Spin.quadPlus 4 F),
      SimplyLacedLevis (Spin.plusDatum 4 F (by norm_num)) F (edgeD 4) x' ∧
      ∀ k c, x' (sroot k) c = Steinberg.SpinPlus.x 4 F (by norm_num) (sroot k) c ∧
        x' (-sroot k) c = Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot k) c := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum 4 F hn3).isFiniteType
    (Dv := (Spin.plusDatum 4 F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, hx'⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin 4) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := F) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  exact ⟨x', hD, hx'⟩

theorem trialityFrame [CharP F 2] {x' : (Fin 4 → ℤ) → F → spinGroup (Spin.quadPlus 4 F)}
    (hD : SimplyLacedLevis (Spin.plusDatum 4 F (by norm_num)) F (edgeD 4) x')
    (hx' : ∀ k c, x' (sroot k) c = Steinberg.SpinPlus.x 4 F (by norm_num) (sroot k) c ∧
      x' (-sroot k) c = Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot k) c) :
    SimplyLacedFrame (Spin.plusDatum 4 F (by norm_num)) F (edgeD 4)
      (fun k c => Steinberg.SpinPlus.x 4 F (by norm_num) (sroot (triPerm k)) c)
      (fun k c => Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot (triPerm k)) c) := by
  obtain ⟨θ, h01, h10, h12, h21⟩ := exists_sl3BlockSwap (F := F)
  refine ⟨fun i j hij => ?_, fun k => ?_, fun i j hne h1 h2 c d => ?_⟩
  · have hcases : ∀ i j : Fin 4, edgeD 4 i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by decide
    rcases hcases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨l, -, hl⟩ := hD.sl3 (1 : Fin 4) (2 : Fin 4) (by decide)
      refine ⟨l.comp θ, fun c => ?_⟩
      obtain ⟨a1, a2, a3, a4, -, -⟩ := hl c
      exact ⟨(congrArg l (h01 c)).trans (a3.trans (hx' (2 : Fin 4) c).1),
        (congrArg l (h10 c)).trans (a4.trans (hx' (2 : Fin 4) c).2),
        (congrArg l (h12 c)).trans (a1.trans (hx' (1 : Fin 4) c).1),
        (congrArg l (h21 c)).trans (a2.trans (hx' (1 : Fin 4) c).2)⟩
    · obtain ⟨l, -, hl⟩ := hD.sl3 (1 : Fin 4) (3 : Fin 4) (by decide)
      refine ⟨l, fun c => ?_⟩
      obtain ⟨a1, a2, a3, a4, -, -⟩ := hl c
      exact ⟨a1.trans (hx' (1 : Fin 4) c).1, a2.trans (hx' (1 : Fin 4) c).2,
        a3.trans (hx' (3 : Fin 4) c).1, a4.trans (hx' (3 : Fin 4) c).2⟩
    · obtain ⟨l, -, hl⟩ := hD.sl3 (0 : Fin 4) (1 : Fin 4) (by decide)
      refine ⟨l.comp θ, fun c => ?_⟩
      obtain ⟨a1, a2, a3, a4, -, -⟩ := hl c
      exact ⟨(congrArg l (h01 c)).trans (a3.trans (hx' (1 : Fin 4) c).1),
        (congrArg l (h10 c)).trans (a4.trans (hx' (1 : Fin 4) c).2),
        (congrArg l (h12 c)).trans (a1.trans (hx' (0 : Fin 4) c).1),
        (congrArg l (h21 c)).trans (a2.trans (hx' (0 : Fin 4) c).2)⟩
  · obtain ⟨l, -, hl⟩ := hD.sl2 (triPerm k)
    exact ⟨l, fun c => ⟨(hl c).1.trans (hx' _ c).1, (hl c).2.trans (hx' _ c).2⟩⟩
  · have hnadj : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
        triPerm i ≠ triPerm j ∧ ¬ edgeD 4 (triPerm i) (triPerm j) ∧
          ¬ edgeD 4 (triPerm j) (triPerm i) := by decide
    obtain ⟨hne', h1', h2'⟩ := hnadj i j hne h1 h2
    obtain ⟨l, -, hl⟩ := hD.sl2sl2 (triPerm i) (triPerm j) hne' h1' h2'
    have hc : ∀ a b : SL(2, F), Commute (l (a, 1)) (l (1, b)) := fun a b =>
      (show Commute ((a, 1) : SL(2, F) × SL(2, F)) (1, b) by simp [Commute, SemiconjBy]).map l
    obtain ⟨b1, b2, -, -⟩ := hl c
    obtain ⟨-, -, e3, e4⟩ := hl d
    have f1 := (hx' (triPerm i) c).1.symm.trans b1.symm
    have f2 := (hx' (triPerm i) c).2.symm.trans b2.symm
    have f3 := (hx' (triPerm j) d).1.symm.trans e3.symm
    have f4 := (hx' (triPerm j) d).2.symm.trans e4.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f1, f3]; exact hc (tv 0 1 c) (tv 0 1 d)
    · rw [f1, f4]; exact hc (tv 0 1 c) (tv 1 0 d)
    · rw [f2, f3]; exact hc (tv 1 0 c) (tv 0 1 d)
    · rw [f2, f4]; exact hc (tv 1 0 c) (tv 1 0 d)

theorem closure_trialityFrame :
    Subgroup.closure (⋃ k : Fin 4,
      Set.range (fun c : F => Steinberg.SpinPlus.x 4 F (by norm_num) (sroot (triPerm k)) c) ∪
      Set.range (fun c : F => Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot (triPerm k)) c)) =
      ⊤ := by
  have hn3 : 3 ≤ 4 := by norm_num
  have h := ClassicalInvolution.Balance.iSup_rankOne_eq_top (Spin.plusDatum 4 F hn3)
    (Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top 4 F hn3))
  have hpar := Steinberg.SpinPlus.isParametrization (n := 4) (K := F) hn3
  rw [eq_top_iff, ← h]
  refine iSup_le fun k => ?_
  obtain ⟨k', rfl⟩ : ∃ k', triPerm k' = k := ⟨triEquiv.symm k, triEquiv.apply_symm_apply k⟩
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, rfl⟩ := ((hpar _ (ClassicalInvolution.Balance.single_mem_roots _ _)).1 g).1 hg
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k', Or.inl ⟨c, rfl⟩⟩)
  · have hneg := Steinberg.OfCartan.neg_mem_roots (Spin.plusDatum 4 F hn3).isFiniteType
      (ClassicalInvolution.Balance.single_mem_roots (Spin.plusDatum 4 F hn3) (triPerm k'))
    obtain ⟨c, rfl⟩ := ((hpar _ hneg).1 g).1 hg
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k', Or.inr ⟨c, rfl⟩⟩)

end Frame

end CFSG.LocalAnalysis.WeakClosure81
