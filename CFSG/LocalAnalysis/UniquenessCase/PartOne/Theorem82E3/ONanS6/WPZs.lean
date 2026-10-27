module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

@[expose] def G0 (c : Ctx82E3 D) (P J : Subgroup G) : Subgroup G := J ⊔ zSub P c.L

@[expose] noncomputable def Z0 (c : Ctx82E3 D) (P J : Subgroup G) : Subgroup ↥(G0 c P J) :=
  (zSub P c.L).subgroupOf (G0 c P J)

@[expose] noncomputable def Xcl (c : Ctx82E3 D) (P J : Subgroup G) : Subgroup ↥(G0 c P J) :=
  Subgroup.normalClosure ((Z0 c P J : Subgroup ↥(G0 c P J)) : Set ↥(G0 c P J))

@[expose] noncomputable def Xbar (c : Ctx82E3 D) (P J : Subgroup G) :
    Subgroup (↥(G0 c P J) ⧸ CFSG.pPrimeCore 3 ↥(G0 c P J)) :=
  Subgroup.normalClosure
    (((Z0 c P J).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0 c P J))) :
        Subgroup (↥(G0 c P J) ⧸ CFSG.pPrimeCore 3 ↥(G0 c P J))) :
      Set (↥(G0 c P J) ⧸ CFSG.pPrimeCore 3 ↥(G0 c P J)))

abbrev Jtilde (J : Subgroup G) : Type := J ⧸ aschbacherSolvableCore 3 J

abbrev J0 (J : Subgroup G) : Type :=
  Jtilde J ⧸ Subgroup.center (Jtilde J)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem small_models_excluded {J : Subgroup G} (hK9f : K9Five) (hdvd : 1080 ∣ Nat.card (J0 J))
    (hiso : Nonempty (J0 J ≃* Xbar c P J)) :
    ¬ Nonempty (Xbar c P J ≃* CFSG.Assembly.RankThreeEven.projSU 3 3 1) ∧
      ¬ CFSG.Blueprint.ChevalleyExceptionalModel (Xbar c P J) .G2 3 1 := by
  have hcard : 1080 ∣ Nat.card (Xbar c P J) := by
    obtain ⟨e⟩ := hiso
    rwa [Nat.card_congr e.toEquiv] at hdvd
  have h5 : 5 ∣ Nat.card (Xbar c P J) := (by norm_num : 5 ∣ 1080).trans hcard
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv] at h5
    exact hK9f.1 h5
  · intro hm
    exact hK9f.2 (Xbar c P J) hm h5

theorem g2_rank_excluded {J : Subgroup G} (hK9r : K9G2Rank) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (Xbar c P J) .G2 3 f)
    (hXbar : CFSG.Open.pRank 3 (Xbar c P J) ≤ 3) : False := by
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Xbar c P J)) := hK9r _ f hf hmodel
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (Xbar c P J)] at h4
  omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
