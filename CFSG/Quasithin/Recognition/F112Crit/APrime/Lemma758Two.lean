module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758M
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758MFacts
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758Block
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758W
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Corollary762

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem ConfigA.not_le_normalizer_pCoreOf_inf (hA : ConfigA G₀ G₁ G₂ T L E) :
    ¬ G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G) := by
  intro hD
  have h2 := hA.relIndex_pCoreOf_inf hA.relIndex_pCoreOf_T.le
  have hM := hA.parabolicA_conjClosure hD (hA.relIndex_conjClosure_pCoreOf h2 hD)
  obtain ⟨W, r, hWD, hW, hWn, hQ₂W, hQ₁W, hr, hr1, hrD, -, -⟩ := hM.exists_block hA.toAmalgamS3
  exact hA.false_of_elemAbelian hWD hW hWn hQ₂W hQ₁W hr hr1 hrD

theorem ConfigA.false (hA : ConfigA G₀ G₁ G₂ T L E) : False :=
  hA.false_of_not_le_normalizer hA.not_le_normalizer_pCoreOf_inf

end CFSG.Quasithin.F112Crit.APrime

end
