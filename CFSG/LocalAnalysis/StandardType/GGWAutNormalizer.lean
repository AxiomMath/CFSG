module

public import CFSG.LocalAnalysis.StandardType.GGWAutNormSym
public import CFSG.LocalAnalysis.StandardType.GGWAutNormImprim
public import CFSG.LocalAnalysis.StandardType.GGWAutNormOrth
public import CFSG.LocalAnalysis.StandardType.GGWAutE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWAut_normalizer_pm (hK : GGReflClassOmegaInput) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (hn : 5 ≤ Module.finrank (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) (hneg : ∀ r ∈ R, ¬ ∀ v, r v = -v)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrefl : ∃ t ∈ R, GGLinRefl t := by
    by_contra hno
    push Not at hno
    have hbot : R = ⊥ := by
      rw [hgen, eq_bot_iff, Subgroup.closure_le]
      rintro t ⟨htR, ht⟩
      exact absurd ht (hno t htR)
    have : Nontrivial V := Module.finrank_pos_iff (R := ZMod 3) (M := V) |>.mp (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({v} : Set V)
    have hWfin : Module.finrank (ZMod 3) W = 1 := finrank_span_singleton hv
    have hWinv : ∀ b ∈ R, ∀ w ∈ W, b w ∈ W := by
      intro b hb w hw
      have hb1 : b = 1 := by
        rw [hbot] at hb
        exact Subgroup.mem_bot.mp hb
      rw [hb1]
      simpa using hw
    rcases habs.1 W hWinv with hW | hW
    · have hvW : v ∈ W := Submodule.subset_span (by simp)
      rw [hW] at hvW
      exact hv (by simpa using hvW)
    · have : Module.finrank (ZMod 3) V = 1 := by rw [← hWfin, hW, finrank_top]
      omega
  by_cases h9 : 9 ≤ Module.finrank (ZMod 3) V
  · rcases hK.1 3 (by norm_num) V (Module.finrank (ZMod 3) V) rfl h9 R habs hgen with
      h1 | h2 | h3 | h4 | h5
    · exact ggWAut_imprim_norm hn R habs hgen h1 hneg ha
    · obtain ⟨r, hr, hrneg⟩ := ggWAut_SL_neg_mem R h2.1 hrefl
      exact absurd hrneg (hneg r hr)
    · exact ggWAut_orth_norm (by omega) R habs hgen h3.1 hneg ha
    · obtain ⟨-, e, he⟩ := h4
      exact ggWAut_sym_norm (by omega) R hgen habs e he ha
    · obtain ⟨-, e, he⟩ := h5
      exact ggWAut_sym_norm (by omega) R hgen habs e he ha
  · rcases hK.2 V (Module.finrank (ZMod 3) V) rfl hn (by omega) R habs hgen with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact ggWAut_imprim_norm hn R habs hgen h1 hneg ha
    · obtain ⟨r, hr, hrneg⟩ := ggWAut_SL_neg_mem R h2.1 hrefl
      exact absurd hrneg (hneg r hr)
    · exact ggWAut_orth_norm (by omega) R habs hgen h3.1 hneg ha
    · obtain ⟨-, e, he⟩ := h4
      exact ggWAut_sym_norm (by omega) R hgen habs e he ha
    · obtain ⟨-, e, he⟩ := h5
      exact ggWAut_sym_norm (by omega) R hgen habs e he ha
    · obtain ⟨-, hW⟩ := h6
      exact ggWAut_E_norm ggQ2WeylInner_E7 R habs hW ha
    · obtain ⟨-, hW⟩ := h7
      exact ggWAut_E_norm ggQ2WeylInner_E8 R habs hW ha

end CFSG.StandardType

end
