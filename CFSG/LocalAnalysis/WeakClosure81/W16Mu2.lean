module

public import CFSG.LocalAnalysis.WeakClosure81.W16Mu2Conj
public import CFSG.LocalAnalysis.WeakClosure81.W16Mu2Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Ext
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.WeakClosure81.W162FiveMain
public import CFSG.LocalAnalysis.WeakClosure81.W16Holds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_uniqueMax_of_dataExt (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian p E ∧
      p ^ 3 ≤ Nat.card E ∧ ∀ B : Subgroup G, B ≤ E → Nat.card B = p ^ 2 → UniqueMax D.M B := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hpP D.M
  refine ⟨p, hpP, hp2, E, hEM, hE, ?_, ?_⟩
  · rw [hEcard]
    exact Nat.pow_le_pow_right hpP.pos (hx.three_le p hp)
  · intro B hBE hBcard
    have hB : IsElemAbelian p B := uc22p22n_isElemAbelian_of_le hBE hE
    refine h61 p hp B (hBE.trans hEM) (CFSG.Open.IsElemAbelian.isPGroup hB) ?_
    refine uc22p22n_not_isCyclic_of_card hpP hB ?_
    rw [hBcard]

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem false_of_mBar_eq_two (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h152 : Thm152 G) (h : Cex16 M V₀ V U S)
    (hm : mBar M V₀ V h.hyp.h6.elemAbelian = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hEu : ∀ B : Subgroup G, B ≤ E → Nat.card B = p ^ 2 → UniqueMax M B) : False := by
  have hn : E3.mQuot V (U ⊔ V₀) ≤ 1 := by have := h.n_lt_mBar; omega
  have h2 : 2 ≤ E3.mQuot V V₀ := by
    have := mBar_le_mQuot (M := M) h.hyp.h6.elemAbelian h.hyp.h6.le; omega
  exact false_of_uniqueMax_of_mQuot_le_one hp hp2 h.hyp.h6.elemAbelian h.hyp.h6.le h.le hE hE3
    (hEM.trans h.hyp.h6.normalizer_eq.ge) (hEM.trans h.hyp.h6.le_normalizer₀) hEu h2 hn
    fun _ hx hx0 => h.not_centralizer_le_of_mem_sup h1 h5 h15 hS h152 hx hx0

end Cex16

section Certified

theorem sixteen_two_muTwo_of_inputs {M V₀ V : Subgroup G} (hI : Inputs15Two G) (h1 : W16One G)
    (h15 : W16Fifteen G) (hS : Std15 G) (hyp : Hyp15 M V₀ V)
    (hm : mBar M V₀ V hyp.h6.elemAbelian = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hEu : ∀ B : Subgroup G, B ≤ E → Nat.card B = p ^ 2 → UniqueMax M B) :
    ((mBar M V₀ V hyp.h6.elemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV M V := by
  by_contra hcon
  obtain ⟨U, S, h⟩ := exists_cex16 hyp (by omega) (not_le.1 hcon)
  exact h.false_of_mBar_eq_two h1 (w16Five_of_one h1 (thm152_of_inputs hI hS)) h15 hS
    (thm152_of_inputs hI hS) hm hp hp2 hEM hE hE3 hEu

theorem w3Thm162MuTwo_holds (hI : Inputs15Two G) (h1 : W16One G) (h15 : W16Fifteen G) :
    W3Thm162MuTwo G := by
  intro D V₀ V h hx h61 hV₀ hm
  obtain ⟨p, hp, hp2, E, hEM, hE, hE3, hEu⟩ := exists_elemAbelian_uniqueMax_of_dataExt D hx h61
  exact sixteen_two_muTwo_of_inputs hI h1 h15 (Std15.of_data D) (Hyp15.of_setting h hV₀) hm hp
    hp2 hEM hE hE3 hEu

end Certified

end CFSG.LocalAnalysis.WeakClosure81
