module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoXhat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoYhat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] def UniqueTwoLocalKy : Prop :=
  ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → t.Ky ≤ H → H ≤ c.S.M

theorem normalizer_le_of_uniqueTwoLocalKy (hP1 : t.UniqueTwoLocalKy) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hKT : t.Ky ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.normalizer (T : Set G) ≤ c.S.M :=
  hP1 _ ⟨T, hT1, hT, rfl⟩ hKT

@[expose] def CaseTwoG1 : Prop :=
  ∀ p : ℕ, p ∈ c.sig →
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p →
    t.PairNormalizerLe p →
    ¬ t.InducesAlternating → Subgroup.centralizer (t.Z : Set G) ≤ c.S.M →
    CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) ≤ 1 → t.Oz ≤ c.S.M

@[expose] def CaseTwoG2 : Prop :=
  ∀ p : ℕ, p ∈ c.sig →
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p →
    t.PairNormalizerLe p →
    ¬ t.InducesAlternating → Subgroup.centralizer (t.Z : Set G) ≤ c.S.M →
    CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) ≤ 1 → t.Oz ≤ c.S.M →
    ((∃ ℓ f : ℕ, ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel t.Xhat .PSL 3 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel t.Xhat .PSU 3 ℓ f)) →
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M

theorem caseTwoResidual_of_G1_G2 (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hG1 : t.CaseTwoG1) (hG2 : t.CaseTwoG2) : t.CaseTwoResidual := by
  intro p hp h76 hN hIIa hZ hrank
  have hO := hG1 p hp h76 hN hIIa hZ hrank
  rcases t.Xhat_cases hK32 hGA hSp hK332 hOut hp hN hZ with h | h | h | h
  · exact t.centralizer_y_le_of_K11 hK11 hK32 hGA hSp hK332 hOut hp hN hZ hO (Or.inl h)
  · exact hG2 p hp h76 hN hIIa hZ hrank hO (Or.inl h)
  · exact hG2 p hp h76 hN hIIa hZ hrank hO (Or.inr h)
  · exact t.centralizer_y_le_of_K11 hK11 hK32 hGA hSp hK332 hOut hp hN hZ hO (Or.inr h)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
