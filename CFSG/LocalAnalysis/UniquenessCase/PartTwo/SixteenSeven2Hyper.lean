module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_barSub_mem_calABar_of_hyperplanes {M V₁ V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (h1 : V₁ = ⊥) (hAM : A ≤ M) (hAst : A ≤ stabTil V₁ V)
    (hAel : IsElemAbelian 2 A) (hA1 : barSub V₁ V hV A ≠ ⊥)
    (hhyp : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B = 1 →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G)) :
    barSub V₁ V hV A ∈ calABar 2 M V₁ V hV := by
  subst h1
  refine ⟨barSub_mono ⊥ V hV hAM, hA1, isElemAbelian2_barSub hV hAel, ?_⟩
  intro C hC hlt
  have hBA : preBarSub A ⊥ V hV C ≤ A := inf_le_left
  have hBst : preBarSub A ⊥ V hV C ≤ stabTil ⊥ V := hBA.trans hAst
  have hbarB : barSub ⊥ V hV (preBarSub A ⊥ V hV C) = C := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hmB : E3.mQuot A (preBarSub A ⊥ V hV C) = E3.mQuot (barSub ⊥ V hV A) C :=
    (mQuot_barSub_preBarSub_gen hV hAst hC).symm
  generalize hBdef : preBarSub A ⊥ V hV C = B at hBA hBst hbarB hmB
  have hltB : E3.mQuot A B < 2 := by rw [hmB]; exact hlt
  have hpre : preCTilde ⊥ V B hV = preCTilde ⊥ V A hV := by
    rcases (show E3.mQuot A B = 0 ∨ E3.mQuot A B = 1 by omega) with h0 | h1
    · rw [(E3.mQuot_eq_zero_iff (CFSG.Open.IsElemAbelian.isPGroup hAel) hBA).1 h0]
    · rw [preCTilde_bot_eq hV hBst, preCTilde_bot_eq hV hAst]
      exact hhyp B hBA h1
  exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpre)

theorem s16c167_barSub_le_stabSub_wTil {V₀ V L A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAst : A ≤ stabTil V₀ V) (hAW : A ≤ normalizer (wSub V₀ V hV L : Set G)) :
    barSub V₀ V hV A ≤ stabSub (wTil V₀ V hV L) := by
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := (mem_barSub V₀ V hV A φ).1 hφ
  rw [mem_stabSub]
  intro u
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV u
  rw [actTil_mk]
  have hg : (g : G) ∈ normalizer (wSub V₀ V hV L : Set G) := hAW hgA
  have key : ∀ y : IntMod V hV, mkTil V₀ V hV y ∈ wTil V₀ V hV L ↔ y.val ∈ wSub V₀ V hV L := by
    intro y
    change mkTil V₀ V hV y ∈ wTil V₀ V hV L ↔ y.val ∈ preTil V₀ V hV (wTil V₀ V hV L)
    rw [mem_preTil]
    exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨z, hz, hzw⟩ => by
      obtain rfl := IntMod.val_injective hz
      exact hzw⟩
  rw [key (actStab V₀ V hV g x), key x, actStab_apply_val]
  exact (Subgroup.mem_normalizer_iff.1 hg x.val).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
