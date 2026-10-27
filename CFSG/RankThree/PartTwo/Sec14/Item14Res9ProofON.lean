module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofFix
public import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofDescFix

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step143HJMemFixON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb →
        ∀ (b' d' : G) (Lb' X : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb' ∈ lA A b' →
          Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2) →
          d' ∈ A → d' ≠ 1 → IsThreeCentralIn Lb' d' → a ∈ Subgroup.closure {b', d'} →
          X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) →
          delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤
            pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
              pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
                ⨆ (D' : Subgroup G) (_ : IsHyperplane A D' ∧ a ∈ D'), lB A D' →
          (∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
            lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) →
          delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
            pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
              pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
          Subgroup.centralizer ({a} : Set G) ≤
            Subgroup.normalizer
              ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) :
                Set G) →
          Subgroup.zpowers a = Subgroup.zpowers d' →
          (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
            CFSG.Blueprint.NativeSporadic.ON →
          ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
            (∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
              ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) →
            ¬ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
              lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) →
            ∀ R : Subgroup G,
              R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
                Subgroup.centralizer (D : Set G) →
              ¬ 3 ∣ Nat.card R → A ≤ Subgroup.normalizer (R : Set G) → R = ⁅R, A⁆ →
                R ≤ qBound A (lB A) D

theorem step143HJMemFixL_of_on (hbal : Step143Balance) (hON : Step143HJMemFixON) :
    Step143HJMemFixL := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc b' d' Lb' X hb'Ω hLb' hJ2 hd'A hd'1 hd'3
    hab' hXΔ hLD hΔ hN hda h𝒳 htype D hD haD hα hβ R hRN hR3 hAR hRR
  rcases htype with hON' | hA6A6
  · exact hON G A c L h a ha ha1 hΩ B b d Lb hB haB hc b' d' Lb' X hb'Ω hLb' hJ2 hd'A hd'1 hd'3
      hab' hXΔ (Res9Fix.delta_le_sup_iSup hbal h ha ha1 hΩ) hLD hΔ hN hda h𝒳 hON' D hD haD hα hβ R
      hRN hR3 hAR hRR
  · exact Res9Fix.le_qBound_of_centralProduct hbal h ha ha1 hΩ hXΔ hLD hN h𝒳 hA6A6 hD haD hα hβ
      hRN hR3 hRR

end CFSG.RankThree.PartTwo.Sec14
