module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace F08

@[expose] def R869NPair (D : Data G) : Prop :=
  ∀ K : Subgroup G, K ∈ calC D.M → (conjSetOf D.M K).ncard = 2 → ∀ n : ℕ, 2 < n →
    IsPowTwo n → IsL2 (Bar2 K) n → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M →
      Nat.card A = r →
        (conjClosure D.M K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 (conjClosure D.M K) =
          conjClosure D.M K → normalizer (A : Set G) ≤ D.M

theorem R869NPair_of_R869N (D : Data G) (h : R869N D) : R869NPair D := by
  intro K hK hc2 n _ _ _ r hr hr2 A hAM hA hcov
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  exact h _ hXM hMX hprod (uc22p2214_not_thin_pair hK hc2) r hr hr2 A hAM hA hcov

end F08

end CFSG.LocalAnalysis.UniquenessCase.UC22
