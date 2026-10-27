module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeR
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S20_14N (D : Data G) : Prop :=
  H1930 D → ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M →
    ∀ H ∈ hSet D.T D.M, p ∣ Nat.card ↥(H ⊓ D.M) →
      ∃ m n : ℕ, 2 < m ∧ m ≤ 4 ∧ 2 < n ∧
        CFSG.Open.IsQuasisimple (Bar2 (Opp p H)) ∧
        LieModel (Bar2 (Opp p H) ⧸ Subgroup.center (Bar2 (Opp p H))) .PSL m 2 n ∧
        ¬ 2 ^ n ≡ 1 [MOD p] ∧
        Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 (H ⊓ D.M)))) ≃*
          CFSG.Open.StatedSL (m - 1) (GaloisField 2 n))

theorem s22Fin3R_of_s20_14N {D : Data G} {Ch : Choice2011 G} (h2014 : S20_14N D)
    (hA : S22FinA D Ch) : S22Fin3R D Ch := by
  intro _ _ _ h1930 c p hp _ _ _ _ _ _ _ hsp H hH hZH hVH hpH _
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨m, f, hm, hm4, hf, hQ, hLie, h1, e⟩ := h2014 h1930 p hpP hp2 hsp H hH hpH
  refine ⟨m, f, hm, hm4, hf, h1, e, fun hm3 hk1 hYC eY => ?_⟩
  subst hm3
  obtain ⟨A, hBA, -, hAc, -, hAYB, eA⟩ := hA h1930 c p hp H hH hZH hVH hk1 f hf hQ hLie hYC eY
  exact ⟨A, hBA, hAc, hAYB, eA⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
