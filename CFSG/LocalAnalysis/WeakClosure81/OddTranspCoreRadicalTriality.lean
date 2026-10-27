module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
import CFSG.GroupTheory.CenterOfTrivialCentralizer
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalOrth
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarOrthTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem radicalOutcome_of_isTrialityOddTransp {W : Type} [Group W] {t : W}
    (h : IsTrialityOddTransp W t) : RadicalOutcome W t := by
  obtain ⟨ε, hdata⟩ := h
  obtain ⟨f, F, hF, hFin, hcard, e, hrank⟩ := hdata.orth
  have hZ : Subgroup.center ↥(ε.ker ⊔ Subgroup.zpowers t) = ⊥ :=
    CFSG.GroupTheory.center_eq_bot_of_le_of_centralizer_eq_bot le_sup_left
      hdata.centralizer_ker
  have ht : t ∈ ε.ker ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have horth : IsOrthReflection ↥(ε.ker ⊔ Subgroup.zpowers t) 8 f ⟨t, ht⟩ := by
    refine Or.inl ⟨4, by norm_num, by norm_num, F, hF, hFin, hcard, e, ?_⟩
    exact hrank
  have h2F : 2 ≤ Nat.card F := by
    have hlt : 1 < Nat.card F :=
      @Finite.one_lt_card F hFin (@Field.toNontrivial F hF)
    omega
  have hf0 : f ≠ 0 := by
    intro hf
    rw [hf, pow_zero] at hcard
    omega
  rcases (by omega : f = 1 ∨ 2 ≤ f) with hf | hf
  · have horth1 : IsOrthReflection ↥(ε.ker ⊔ Subgroup.zpowers t) 8 1 ⟨t, ht⟩ := by
      simpa [hf] using horth
    exact RadicalOutcome.of_le ht
      (Or.inl (CFSG.LocalAnalysis.WeakClosure81.CoreStar.hasCoreStar_of_isOrthReflection_two
        hZ (m := 8) (by norm_num) horth1))
  · exact RadicalOutcome.of_le ht (radicalOutcome_of_isOrthReflection hZ hf horth)

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
