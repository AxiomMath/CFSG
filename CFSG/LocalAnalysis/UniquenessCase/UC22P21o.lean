module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21n

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def Core227Hat (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → ∀ i, p ∈ piSet (preN D (Nb i)) →
      ∀ g ∈ normalizer (proofS D : Set G), g ∉ normalizer (proofEiHat D (preN D (Nb i)) : Set G) →
        preN D (Nb i) ≤ centralizer
          ((proofEiHat D (preN D (Nb i))).map (MulAut.conj g).toMonoidHom : Set G)

@[expose] def S22_2_finHat (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → mbarImage D.M D.U (proofN D) ≠ ⊥ → D.sig = D.sig1 → Cl22_5_1 D Nb →
    p ∈ piSet (proofN D) → Cl22_6Hat D Nb → normalizer (proofS D : Set G) ≤ D.M → False

theorem uc22p21o_s22_2_of_steps_hat (D : Data G) (Ch : Choice2011 G) (hsig : D.sig.Nonempty)
    (h3_1 : S22_3_1 D Ch) (h3_2 : S22_3_2 D Ch) (h4 : S22_4 D Ch) (h5_1 : S22_5_1 D Ch) (h5_2 : S22_5_2 D Ch)
    (h6 : S22_6Hat D Ch) (h7 : S22_7 D Ch) (hfin : S22_2_finHat D Ch) : S22_2 D Ch := by
  intro h1930 c hle
  let cc : Ctx22c D Ch := { c with hCle := hle }
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨m, Nb, hNb⟩ := h3_2 h1930 cc
  exact hfin h1930 cc p hp m Nb hNb (h3_1 h1930 cc).1 (h4 h1930 cc) (h5_1 h1930 cc m Nb hNb)
    (h5_2 h1930 cc p hp) (h6 h1930 cc m Nb hNb) (h7 h1930 cc)

end CFSG.LocalAnalysis.UniquenessCase.UC22
