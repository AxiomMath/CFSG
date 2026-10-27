module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.S13K.CommDistinct

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

@[expose] def KtLift {G : Type} [Group G] (p : ℕ) (E : Subgroup G) (t : MulAut E)
    (K : Subgroup G) : Prop :=
  IsKt p E t K ∧ CFSG.IsQuasisimple ↥K ∧ Subgroup.center ↥K = ⊥ ∧ autMovedInG E t ≤ K ∧
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ K ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t

theorem ktLift_of_liftAt {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E}
    (h : KFLiftAt p E t) : KtLift p E t (kZero p E t) :=
  ⟨h.isKt, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

@[expose] def KFCommDistinctX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, ∀ K_s K_t : Subgroup G,
    KtLift p E s K_s → KtLift p E t K_t → (E ≠ A ∨ HasTwoSub E K_s ∨ HasTwoSub E K_t) →
    s * t = t * s → ∀ e ∈ autFixedInG E s ⊓ autFixedInG E t, e ≠ 1 →
    ∀ I₁ ∈ thetaComponentsAt p e, ∀ I₂ ∈ thetaComponentsAt p e, I₁ ≠ I₂ →
      K_s ≤ I₁ → K_t ≤ I₂ → K_s ≤ Subgroup.centralizer (K_t : Set G)

theorem KFCommDistinctX.toKFCommDistinct (h : KFCommDistinctX) : KFCommDistinct :=
  fun G _ _ p A c L E h12 hF hF13 hT s hs t ht hLs hLt hspl hst e he he1 I₁ hI₁ I₂ hI₂ hne hK₁
      hK₂ =>
    h G p A c L E h12 hF hF13 hT s hs t ht (kZero p E s) (kZero p E t) (ktLift_of_liftAt hLs)
      (ktLift_of_liftAt hLt) hspl hst e he he1 I₁ hI₁ I₂ hI₂ hne hK₁ hK₂

end CFSG.RankThree.PartOne.K1320X
