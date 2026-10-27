module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearFaithful
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.StandardType.LinearFieldFix

theorem ggRawFieldFixStd_linear {l : ℕ} (hl : 2 ≤ l) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} :
    GGRawFieldFixStd p ⟨.A, l, n / p⟩ (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K))) := by
  intro _ _ f hf hord
  obtain ⟨σ, hσ⟩ := exists_induced hf
  have hd : 3 ≤ l + 1 := by omega
  have hσord : orderOf σ = p :=
    (orderOf_eq_of_mk_matAct (by omega) (slMapStable (l + 1) K) hσ).trans hord
  obtain ⟨-, hcard⟩ := card_fixedPoints_field hn hK σ
  have hk : Nat.card (fixF σ) = 2 ^ (n / p) := by rw [card_fixF, hcard, hσord]
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
  exact ⟨fixF σ, inferInstance, inferInstance, hk, isSimpleGroup_proj hd _,
    exists_noncomm_proj hd _, (subfieldEquiv hd hn hK hσ).symm, ggFixGeom_linear hd hn hK hσ⟩

theorem ggFieldFixKnown_linear : GGFieldFixKnown GGFieldFixLinearLabel := by
  intro p lab _ _ hlab hS
  obtain ⟨⟨-, -, hrow⟩, hA⟩ := hS
  have hl4 : 4 ≤ lab.rank := by
    rcases hrow with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> rw [hA] at h <;> cases h
    · rcases h with h | h <;> rw [hA] at h <;> cases h
    · rw [hA] at h; cases h
    · rw [hA] at h; cases h
    · exact h
    · rw [hA] at h; cases h
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hA hl4 hn
  subst hA
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all
    (fun K _ _ hK => ggRawFieldFixStd_linear (by omega) hn hK) hQ

end CFSG.StandardType

end
