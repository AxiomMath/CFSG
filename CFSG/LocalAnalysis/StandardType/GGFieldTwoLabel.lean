module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ftl_eq_of_ggLabelIso_twA5 {lab : LargeEvenLabel} {f : ℕ}
    (h : GGLabelIso lab ⟨.twA, 5, f⟩) : lab = ⟨.twA, 5, f⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggFieldTwo_twA5_n_eq_one
    {K : Type} [Group K] {labK : LargeEvenLabel} {n' : ℕ}
    (hΛK : LargeEvenInLambda2 labK) (hK1 : labK.n = 1)
    (hhK : GGHasLabel labK (K ⧸ Subgroup.center K))
    (hl : GGHasLabel ⟨.twA, 5, n'⟩ (K ⧸ Subgroup.center K)) : n' = 1 := by
  have hn' : 1 ≤ n' := by
    by_contra hlt
    have hn0 : n' = 0 := by omega
    rw [hn0] at hl
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeUnitary] at hl
    obtain ⟨K', hf, hfin, hcard, -⟩ := hl
    haveI : Field K' := hf
    haveI : Finite K' := hfin
    have h2 : 1 < Nat.card K' := Finite.one_lt_card
    norm_num at hcard
    omega
  have hΛ' : LargeEvenInLambda2 ⟨.twA, 5, n'⟩ := by
    dsimp only [LargeEvenInLambda2]
    exact ⟨hn', by norm_num, by omega⟩
  have hIso : GGLabelIso labK ⟨.twA, 5, n'⟩ :=
    ggLabelRigidInput_holds labK ⟨.twA, 5, n'⟩ (K ⧸ Subgroup.center K) hΛK hΛ' hhK hl
  have hEq := ftl_eq_of_ggLabelIso_twA5 hIso
  have hnn : labK.n = n' := by rw [hEq]
  omega

end CFSG.StandardType

end
