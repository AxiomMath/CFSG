module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import Certificates.Certificate9504
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

namespace F5

@[expose] def K5Gen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
    ∀ S : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ →
      (⨆ (U : Subgroup Y) (_ : U ≤ S) (_ : ¬ IsCyclic U), Subgroup.normalizer (U : Set Y)) = ⊤

end F5

open CFSG.Blueprint CFSG.SectionRank CFSG.AGLEmbedding.R3 in
private theorem glbWeakCore_ON_eq_top [Finite NativeSporadic.ON]
    [Fact (Nat.Prime 3)] (T : Sylow 3 NativeSporadic.ON) :
    CFSG.Open.GLBWeakCore 3 (T : Subgroup NativeSporadic.ON) = ⊤ :=
  CFSG.AGLEmbedding.weakCoreOfTC NativeSporadic.ON 3
    (tcGenDatum_of_check (spec3 154) (D := ONThree.tcSpec) Nat.prime_three
      Certificates.certificate9504.1) T

theorem k5Gen_holds : F5.K5Gen := by
  intro Y _ _ hY S hS
  obtain ⟨e⟩ := (show Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.ON) from hY)
  haveI : Finite CFSG.Blueprint.NativeSporadic.ON := Finite.of_equiv Y e.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (S.map (e : Y →* CFSG.Blueprint.NativeSporadic.ON)) =
      3 ^ (Nat.card CFSG.Blueprint.NativeSporadic.ON).factorization 3 := by
    rw [Subgroup.card_map_of_injective e.injective, CFSG.ABGLocalTools.IsSylowOf.card_eq hS,
      Subgroup.card_top, Nat.card_congr e.toEquiv]
  let f : CFSG.Blueprint.NativeSporadic.ON →* Y := e.symm
  have hTS : ((Sylow.ofCard _ hcard : Sylow 3 _) : Subgroup _).map f = S := by
    rw [Sylow.coe_ofCard]
    ext x
    simp only [Subgroup.mem_map]
    refine ⟨fun ⟨_, ⟨z, hz, hzy⟩, hyx⟩ => ?_, fun hx => ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩⟩
    rw [← hyx, ← hzy]
    simpa [f] using hz
  have hW : CFSG.Open.GLBWeakCore 3 S = ⊤ := by
    have h1 := CFSG.AGLEmbedding.map_glbWeakCore_le Nat.prime_three f e.symm.injective
      ((Sylow.ofCard _ hcard : Sylow 3 _) : Subgroup _)
    rw [glbWeakCore_ON_eq_top, Subgroup.map_top_of_surjective f e.symm.surjective, hTS] at h1
    exact eq_top_iff.mpr h1
  rw [eq_top_iff, ← hW, CFSG.PreuniquenessRankFour.Helpers.weakCore_le_iff]
  intro Q hQS hQ2 _
  refine le_iSup₂_of_le Q hQS (le_iSup_of_le (fun hc => ?_) le_rfl)
  have := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hc
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
