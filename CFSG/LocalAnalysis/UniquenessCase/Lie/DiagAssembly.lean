module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20u
public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagClassical
public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagExceptional

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

@[expose] def uc22p20uGraphInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ (t : StatedLieTag) (m n : ℕ),
    LieModel (X ⧸ center X) t m 2 n → ∀ (U : Sylow 2 X) (A : Set (MulAut X)),
    (∀ α ∈ A, ∀ x : X, x ∈ (U : Subgroup X) ↔ α x ∈ (U : Subgroup X)) →
    (uc22p20sGraphShape t m n ∧ ∀ α ∈ A, ∀ θ : MulAut (X ⧸ center X),
      (∀ x : X, θ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) →
        CFSG.ASVolI.ChA.IsInnDiagFieldAut _ θ) →
    (⨆ (P : Subgroup X) (_ : normalizer ((U : Subgroup X) : Set X) ≤ P ∧ P ≠ ⊤ ∧
      ∀ α ∈ A, ∀ x : X, x ∈ P ↔ α x ∈ P), P) = ⊤

@[expose] def uc22pdiag_Fam (t : StatedLieTag) (m : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] [IsSimpleGroup M] (n : ℕ), P n → LieModel M t m 2 n →
    uc22pdiag_All M

theorem uc22pdiag_rankTwo_of_families
    (hL4 : uc22pdiag_Fam .PSL 4 (fun n => 2 < n))
    (hU4 : uc22pdiag_Fam .PSU 4 (fun n => 2 ≤ n))
    (hU5 : uc22pdiag_Fam .PSU 5 (fun n => n = 2))
    (hG2 : uc22pdiag_Fam .G2 0 (fun n => 2 < n))
    (hD4 : uc22pdiag_Fam .trialityD4 0 (fun n => 1 ≤ n))
    (hF4 : uc22pdiag_Fam .twistedF4 0 (fun n => 2 < n))
    (hSp6 : uc22pdiag_Fam .PSp 3 (fun n => 2 < n))
    (hO8 : uc22pdiag_Fam .POmegaMinus 4 (fun n => 2 ≤ n)) :
    ∀ (M : Type) [Group M] [Finite M] [IsSimpleGroup M] (t : StatedLieTag) (m n : ℕ),
      LieModel M t m 2 n → uc22p20sRankTwo t m n → uc22pdiag_All M := by
  intro M _ _ _ t m n hM hr
  unfold uc22p20sRankTwo at hr
  rcases hr with ⟨hn, h | h | h | h | h | h | h⟩ | ⟨hn, h | h | h⟩ | ⟨hn, h⟩
  · obtain ⟨rfl, rfl⟩ := h; exact hL4 M n hn hM
  · obtain ⟨rfl, rfl⟩ := h; exact hU4 M n hn.le hM
  · subst h
    have : m = 0 := by
      obtain ⟨-, -, hm⟩ := LieModel.admissible hM
      exact hm.1
    subst this; exact hG2 M n hn hM
  · subst h
    have : m = 0 := by
      obtain ⟨-, -, hm⟩ := LieModel.admissible hM
      exact hm
    subst this; exact hD4 M n (by omega) hM
  · subst h
    have : m = 0 := by
      obtain ⟨-, -, hm⟩ := LieModel.admissible hM
      exact hm.1
    subst this; exact hF4 M n hn hM
  · obtain ⟨rfl, rfl⟩ := h; exact hSp6 M n hn hM
  · obtain ⟨rfl, rfl⟩ := h; exact hO8 M n hn.le hM
  · obtain ⟨rfl, hm | hm⟩ := h
    · subst hm; subst hn; exact hU4 M 2 le_rfl hM
    · subst hm; subst hn; exact hU5 M 2 rfl hM
  · subst h
    have : m = 0 := by
      obtain ⟨-, -, hm⟩ := LieModel.admissible hM
      exact hm
    subst this; exact hD4 M n (by omega) hM
  · obtain ⟨rfl, rfl⟩ := h; exact hO8 M n (by omega) hM
  · subst h
    have : m = 0 := by
      obtain ⟨-, -, hm⟩ := LieModel.admissible hM
      exact hm
    subst this; exact hD4 M n (by omega) hM

section Assembly

theorem uc22p20uDiagramInput_of_graph (h : uc22p20uGraphInput) : uc22p20uDiagramInput := by
  intro X _ _ hqs t m n hmodel U A hA hshape
  rcases hshape with hr | hg
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsSimpleGroup (X ⧸ center X) := hqs.2
    let π : X →* X ⧸ center X := QuotientGroup.mk' (center X)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    let UB : Sylow 2 (X ⧸ center X) := Sylow.mapSurjective (f := π) hπ U
    let AB : Set (MulAut (X ⧸ center X)) :=
      {θ | ∃ α ∈ A, ∀ x, θ (QuotientGroup.mk x) = QuotientGroup.mk (α x)}
    have hUB : (UB : Subgroup (X ⧸ center X)) = (U : Subgroup X).map π := rfl
    have hAB : ∀ β ∈ AB, ∀ y, y ∈ (UB : Subgroup (X ⧸ center X)) ↔ β y ∈ (UB : Subgroup _) := by
      rintro β ⟨α, hα, hβ⟩ y
      have hβ' : β = uc22pdiag_inducedAut α := by
        ext z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        rw [hβ, uc22pdiag_inducedAut_mk]
      rw [hUB, hβ']
      exact uc22pdiag_induced_preserves α U (hA α hα) y
    have hrank := uc22pdiag_rankTwo_of_families
      (fun M _ _ _ n _ h => uc22pdiag_all_psl4 h) (fun M _ _ _ n _ h => uc22pdiag_all_psu4 h)
      (fun M _ _ _ n _ h => uc22pdiag_all_psu5 h) (fun M _ _ _ n _ h => uc22pdiag_all_g2 h)
      (fun M _ _ _ n _ h => uc22pdiag_all_triD4 h) (fun M _ _ _ n _ h => uc22pdiag_all_twF4 h)
      (fun M _ _ _ n _ h => uc22pdiag_all_psp6 h) (fun M _ _ _ n _ h => uc22pdiag_all_pomegaMinus8 h)
    have hjoin : uc22pdiag_join (UB : Subgroup (X ⧸ center X)) AB = ⊤ :=
      hrank _ t m n hmodel hr UB AB hAB
    exact uc22pdiag_join_pullback π hπ (U : Subgroup X) AB A
      (fun α hα x => ⟨uc22pdiag_inducedAut α, ⟨α, hα, fun z => uc22pdiag_inducedAut_mk α z⟩,
        (uc22pdiag_inducedAut_mk α x).symm⟩)
      (hUB ▸ hjoin)
  · exact h X hqs t m n hmodel U A hA hg

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.UC22
