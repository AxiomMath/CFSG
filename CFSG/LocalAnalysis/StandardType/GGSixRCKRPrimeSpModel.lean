module

public import CFSG.LocalAnalysis.StandardType.GGPinnedReturnDefs
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.Timmesfeld.Transvection.QTwoSp
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedSp)


theorem rckSp_finite (n g : ℕ) : Finite (ggU .PSp n g).K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show Finite (StatedSp n (GaloisField 2 g))
  infer_instance

theorem rckSp_isPerfect {n g : ℕ} (hg : 0 < g) (hng : 3 ≤ n ∨ 2 ≤ g) :
    Group.IsPerfect (ggU .PSp n g).K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show Group.IsPerfect (StatedSp n (GaloisField 2 g))
  rcases Nat.lt_or_ge g 2 with h1 | h2
  · obtain rfl : g = 1 := by omega
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n _
      (Or.inr (Or.inr ⟨?_, hng.resolve_right (by omega)⟩))
    rw [GaloisField.card (p := 2) (n := 1) (by norm_num)]
    norm_num
  · have h4 : 4 ≤ Nat.card (GaloisField 2 g) := by
      rw [GaloisField.card (p := 2) (n := g) (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) h2
    let : Fintype (GaloisField 2 g) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 g))) (n := 4)
      (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
    exact CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n _ (Or.inl ⟨s, hs⟩)

theorem rckSp_oddCentralSplit (n g : ℕ) :
    CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .PSp n g).K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_statedSp n (GaloisField 2 g)

theorem rckSp_standardReturnAt
    {n g : ℕ} (hn : 2 ≤ n) (hg : 0 < g) (hng : 3 ≤ n ∨ 2 ≤ g) :
    StandardReturnAt (ggU .PSp n g) g := by
  refine Or.inl ⟨.PSp, n, Or.inr (Or.inr (Or.inl rfl)), ⟨Nat.prime_two, hg, hn, ?_⟩, rfl⟩
  rintro h
  obtain ⟨rfl, h2⟩ := Prod.mk.inj h
  have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (hng.resolve_left (by omega))
  omega

theorem rckSp_exists_longRoot {n : ℕ} (hn : 1 ≤ n) (g : ℕ) :
    ∃ β ∈ (ggU .PSp n g).D.roots, GGLongRoot (ggU .PSp n g).D β := by
  have hrank : (ggU .PSp n g).D.rank = n := rfl
  obtain ⟨β, hβ, hmax⟩ :=
    CFSG.StandardType.exists_maxHeight (D := (ggU .PSp n g).D) (by rw [hrank]; omega)
  exact ⟨β, hβ, 1, β, hβ, hmax, by rw [map_one, Module.End.one_apply]⟩

theorem rckSp_nonempty_equiv (n : ℕ) {K : Type} [Field K] {g : ℕ} (e : K ≃+* GaloisField 2 g) :
    Nonempty (StatedSp n K ≃* (ggU .PSp n g).K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show Nonempty (StatedSp n K ≃* StatedSp n (GaloisField 2 g))
  let eK : StatedSp n K ≃* TauCeti.GLSymplectic (Fin n) K :=
    MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := K))
  let eF : StatedSp n (GaloisField 2 g) ≃*
      TauCeti.GLSymplectic (Fin n) (GaloisField 2 g) :=
    MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n)
        (K := GaloisField 2 g))
  exact ⟨eK.trans ((CFSG.Timmesfeld.Transvection.QTwo.glSympRingEquiv n e).trans eF.symm)⟩

end CFSG.StandardType.RCKRP

end
