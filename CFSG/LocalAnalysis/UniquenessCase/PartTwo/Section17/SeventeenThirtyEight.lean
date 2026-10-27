module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc2_17_36a_normal {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h17_36a : R17_36aAt D V₀ V) :
    D.M ≤ Subgroup.normalizer (L : Set G) := by
  rw [h17_36a L n c]
  exact TwelveTwentyThree.le_normalizer_conjClosure D.M L

theorem uc2_17_38_cNatModSU3 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h17_35 : R17_35At D V₀ V)
    (h17_36a : R17_36aAt D V₀ V) (h0 : V₀ ≠ ⊥) :
    CNatModSU3 (Vtil V₀ V c.hyp125.isElemAbelian)
      (barSub V₀ V c.hyp125.isElemAbelian L) n := by
  have hP := c.hyp125.pairFacts
  have hgen := (TwelveTwentyThree.ne_and_conjGenerated_of_hyp125 c.hyp125 h0).2
  set W : Type := Vtil V₀ V hP.elemAbelian with hW
  set X : Subgroup (MulAut W) := barSub V₀ V hP.elemAbelian L with hX
  set W' : Subgroup W := CFSG.Quasithin.commSub (⊤ : Subgroup W) X with hW'def
  have h35 : CNatModSU3Sub W W' X n := (h17_35.1 L n c).1
  have hW'ne : W' ≠ ⊥ := by
    obtain ⟨S⟩ := h35
    letI : Field S.K := S.fieldK
    letI : Finite S.K := S.finiteK
    let y : Multiplicative (Fin 3 → S.K) := Multiplicative.ofAdd (fun _ : Fin 3 => (1 : S.K))
    have hy1 : y ≠ 1 := by
      intro h
      have h0 : (fun _ : Fin 3 => (1 : S.K)) = 0 := by
        have h' := congrArg (fun z => Multiplicative.toAdd z) h
        simpa [y] using h'
      have h1 := congrFun h0 0
      simp at h1
    have hne : S.e.symm y ≠ 1 := by
      intro h
      apply hy1
      have h2 := congrArg S.e h
      simpa using h2
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨S.e.symm y, hne⟩
  have hX1 : X ≠ ⊥ := by
    intro hXbot
    apply hW'ne
    rw [hW'def, hXbot, CFSG.Quasithin.commSub_eq_bot_iff]
    intro x _
    simp [CFSG.Quasithin.fixV]
  have hXnorm : ∀ m ∈ Mbar D.M V₀ V hP.elemAbelian,
      ∀ x ∈ X, m * x * m⁻¹ ∈ X :=
    TwelveEighteen.conj_mem_barSub hP.elemAbelian (uc2_17_36a_normal c h17_36a)
  have hWtop : W' = ⊤ := by
    by_contra hne
    obtain ⟨ξ, hξ, w, hw⟩ :=
      exists_commutator_notMem (M := D.M) hP.elemAbelian hP.le_normalizer
        hP.le_normalizer₀ hgen hX1 hXnorm hne
    apply hw
    exact Subgroup.subset_closure ⟨ξ, hξ, w, Subgroup.mem_top w, by rw [mul_comm]⟩
  obtain ⟨S⟩ := h35
  exact ⟨by simpa only [hWtop] using S⟩

theorem seventeen_thirtyeight (D : Data G) (V₀ V : Subgroup G)
    (h1737 : R17_37At D V₀ V) : R17_38At D V₀ V := by
  intro L n c
  by_contra hle
  exact c.counter ⟨h1737 L n c, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
