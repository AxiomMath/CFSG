module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePFinal
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_candidate
    (hLB : GGLBalanceInput) {B Bs L D J N : Subgroup G} {x b' : G}
    (hc : GGConfig 3 B Bs x L D J) (hL : GGInnerDiagOn Bs L) (hKi : GGInnerDiagOn Bs N)
    (hn : GGNbr 3 B x D J b' N) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJN : J ≤ N)
    (hpJ : 3 ∣ Nat.card ↥J) (hcard : Nat.card ↥Bs = 3 ^ 6)
    (hJlab : GGHasLabel ⟨.twA, 4, 1⟩ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥N ⧸ Subgroup.center ↥N) ∧
      QTwoDeletedUnitaryCandidate 5 lab := by
  obtain ⟨labN, hΛN, hhasN, -⟩ := largeEvenMarking_exists_hasLabel hKi
  have hΛJ : LargeEvenInLambda2 (⟨.twA, 4, 1⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    simp
  have hregime : GGRegimeDeletedUnitary1836 3 (Nat.card ↥Bs) ⟨.twA, 4, 1⟩ labN := by
    rw [hcard]
    exact ggRegimeDeletedUnitary1836_of (d := 5) (by norm_num) labN
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
    ggTablePRow_delU_of_config hc hL hKi hn hI1 hJN hpJ hLB hΛJ hΛN hregime hJlab hhasN
  refine ⟨labK', hΛK', hhasK', ?_⟩
  have hiso := ggLabelRigidInput_holds _ _ _ hΛJ hΛJ' hJlab hhasJ'
  have hlabJ' : labJ' = ⟨.twA, 4, 1⟩ := ggLabelIso_twA_left (le_refl 4) hiso
  rw [hlabJ'] at hrow
  exact ggQTwoDUnit_tablePRow (d := 5) (by norm_num) hrow

omit [Finite G] in
theorem ggQTwoDUnitSix_label_J {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : n = 5) {J : Subgroup G} {θ : Su K 2 1 n →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = J) : GGHasLabel ⟨.twA, 4, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  subst hn
  exact qtwoDB18_label_of_chart hK (by norm_num) hθ hθr

end CFSG.StandardType.QTwo

end
