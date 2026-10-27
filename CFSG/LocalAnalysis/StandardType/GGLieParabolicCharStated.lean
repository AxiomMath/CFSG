module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharLin
import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharSp
import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharUni
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.StandardType

open CFSG.Open

theorem ggNormalizerOvergroupsChar_of_statedClassicalModel_psl {K : Type} [Group K] {n p f : ℕ}
    (h : StatedClassicalModel K .PSL n p f) : GGNormalizerOvergroupsChar p K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Or.inl ⟨by decide, h⟩)
  have : Fact p.Prime := ⟨h.1.1⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  exact GGNormalizerOvergroupsChar.of_mulEquiv e
    (ggNormalizerOvergroupsChar_projectiveSL p (by have := h.1.2.2.1; omega))

theorem ggNormalizerOvergroupsChar_of_statedClassicalModel_psp {K : Type} [Group K] {n p f : ℕ}
    (h : StatedClassicalModel K .PSp n p f) : GGNormalizerOvergroupsChar p K := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hadm.1⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  exact GGNormalizerOvergroupsChar.of_mulEquiv e
    (ggNormalizerOvergroupsChar_statedProjSp p (by have := hadm.2.2.1; omega))

theorem ggNormalizerOvergroupsChar_of_statedClassicalModel_psu {K : Type} [Group K] {n p f : ℕ}
    (h : StatedClassicalModel K .PSU n p f) : GGNormalizerOvergroupsChar p K := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    ⟨hadm.1, hadm.2.1, by rw [hF, ← pow_mul, mul_comm]⟩
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := r) (ε := ε) hU
  exact GGNormalizerOvergroupsChar.of_mulEquiv
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj hU hR (by omega)).symm)
    (ggNormalizerOvergroupsChar_hypPSU hU (by omega) hε)

end CFSG.StandardType
