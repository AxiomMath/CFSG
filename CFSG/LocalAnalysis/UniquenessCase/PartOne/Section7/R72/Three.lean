module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp R72Shape)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (Sec7Hyp QuotK7 ImageModK LKQuot7 IsReeType)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (Gls3ConclusionPlus)

variable {G : Type} [Group G] [Finite G]

theorem imageModK_opp_eq_generalizedFitting_of_not_dvd_index (k : Sec7Core4 G)
    {H : Subgroup G} (hH : k.Config H)
    (hidx : ¬ k.p ∣ (CFSG.generalizedFitting (QuotK7 k.p H)).index) :
    ImageModK k.p H (Opp k.p H) = CFSG.generalizedFitting (QuotK7 k.p H) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  haveI := (k.isSimpleGroup_generalizedFitting_quotient hH).2.2.1
  exact imageModK_opp_eq_generalizedFitting k hH fun _ _ hx =>
    CFSG.Semidihedral.Local.mem_of_pow_eq_one_of_index _ hidx hx

theorem r72Shape_three
    (hR3 : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) →
      K.index = 3 → IsReeType X 1)
    (hM11 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M11 ≃*
      (TauCeti.CFSGIndex.sporadic .M11).Group))
    (k : Sec7Core4 G) (hk3 : k.p = 3) {H : Subgroup G} (hH : k.Config H)
    {P : Subgroup (QuotK7 k.p H)}
    (hG : Gls3ConclusionPlus (QuotK7 k.p H) (CFSG.generalizedFitting (QuotK7 k.p H)) P)
    (hRee : ∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting (QuotK7 k.p H)) (.reeG2 m)) :
    R72Shape k.p (LKQuot7 k.p H) := by
  obtain ⟨-, -, hFn, hFc⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  have hL : ¬ 3 ∣ (CFSG.generalizedFitting (QuotK7 k.p H)).index →
      ImageModK k.p H (Opp k.p H) = CFSG.generalizedFitting (QuotK7 k.p H) := fun h =>
    imageModK_opp_eq_generalizedFitting_of_not_dvd_index k hH (by rwa [← hk3] at h)
  obtain ⟨-, -, hrows⟩ := hG
  rcases hrows with ⟨q, hq3, ⟨hv, ⟨e⟩⟩, hidx, -⟩ | ⟨q, hq3, ⟨hv, ⟨e⟩⟩, hidx, -⟩ | ⟨m, hiso, -⟩ |
      ⟨hiso, hidx, -⟩ | ⟨⟨φ, -⟩, hidx, -⟩ | ⟨⟨hv, ⟨e⟩⟩, ⟨j, hj⟩, -⟩ | ⟨⟨f⟩, hKtop, -⟩
  ·
    refine r72Shape_lkQuot7_of_eq (hL hidx) (Or.inl ⟨q.exponent, ?_⟩)
    have h := (CFSG.Models.lieModel_A 1 q hv e).toBlueprint (by decide)
    rwa [hq3, ← hk3] at h
  ·
    refine r72Shape_lkQuot7_of_eq (hL hidx) (Or.inr (Or.inl ?_))
    have h := (CFSG.Models.lieModel_twistedA 2 q hv e).toBlueprint (by decide)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    rw [hc, hq3, ← hk3] at h
    exact ⟨_, h⟩
  ·
    exact absurd hiso (hRee m)
  ·
    exact r72Shape_lkQuot7_of_eq_top (imageModK_opp_eq_top k hH ⟨1, by rw [hidx, hk3, pow_one]⟩)
      (Or.inr (Or.inr (Or.inl ⟨hk3, Or.inl (hR3 _ _ hFn hFc hiso hidx)⟩)))
  ·
    refine r72Shape_lkQuot7_of_eq (hL hidx) (Or.inl ⟨2, ?_⟩)
    have h : CFSG.Blueprint.LieModel ↥(CFSG.generalizedFitting (QuotK7 k.p H)) .PSL 2 3 2 :=
      Or.inl ⟨by decide,
        CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
          ⟨φ⟩⟩
    rwa [← hk3] at h
  ·
    have hidx : ¬ 3 ∣ (CFSG.generalizedFitting (QuotK7 k.p H)).index := by
      rw [hj]
      exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    exact r72Shape_lkQuot7_of_eq (hL hidx) (Or.inr (Or.inr (Or.inl ⟨hk3, Or.inr (Or.inr
      ((CFSG.Models.lieModel_A 2 _ hv e).toBlueprint (by decide)))⟩)))
  ·
    have hidx : ¬ 3 ∣ (CFSG.generalizedFitting (QuotK7 k.p H)).index := by
      rw [hKtop, Subgroup.index_top]
      norm_num
    exact r72Shape_lkQuot7_of_eq (hL hidx) (Or.inr (Or.inr (Or.inl ⟨hk3, Or.inr (Or.inl
      ⟨f.trans hM11.some.symm⟩)⟩)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
