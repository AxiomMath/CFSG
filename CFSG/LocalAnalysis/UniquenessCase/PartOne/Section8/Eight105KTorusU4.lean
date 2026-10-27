module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusDefs
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Lines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Rank
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

private theorem d8VecHom_injective_four {K : Type} [Field K] {p : ℕ} :
    Function.Injective (CFSG.RankThree.PartOne.KFU.d8VecHom (p := p) (K := K) 4) := by
  intro v w h
  have h0 : ((v.1 : rootsOfUnity p K) : Kˣ) = ((w.1 : rootsOfUnity p K) : Kˣ) := by
    have := congrFun h 0
    simpa [CFSG.RankThree.PartOne.KFU.d8VecHom, CFSG.RankThree.PartOne.KFU.d8Vec,
      CFSG.RankThree.PartOne.KFU.d8Cls, CFSG.RankThree.PartOne.KFU.d8Ev] using this
  have h1 : ((v.2 : rootsOfUnity p K) : Kˣ) = ((w.2 : rootsOfUnity p K) : Kˣ) := by
    have := congrFun h 1
    simpa [CFSG.RankThree.PartOne.KFU.d8VecHom, CFSG.RankThree.PartOne.KFU.d8Vec,
      CFSG.RankThree.PartOne.KFU.d8Cls, CFSG.RankThree.PartOne.KFU.d8Ev] using this
  exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)

omit [CharP F 2] in
private theorem card_d8Tor_three_four (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    Nat.card (d8Tor 3 F 4) = 9 := by
  have hinj : Function.Injective
      (CFSG.RankThree.PartOne.KFU.diagUHom.comp
        (CFSG.RankThree.PartOne.KFU.d8VecHom (p := 3) (K := F) 4)) := by
    intro x y hxy
    exact d8VecHom_injective_four (CFSG.RankThree.PartOne.KFU.diagU_injective hxy)
  have h1 : Nat.card (d8Tor 3 F 4) = Nat.card (D8Mod 3 F) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [h1, Nat.card_prod,
    CFSG.RankThree.PartTwo.Sec21.U4Lines.card_rootsOfUnity_three hbe hF]

theorem u4_torusFacts_d8Tor (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    TorusFacts (GL (Fin 4) F) (SU (unitaryInvolution F 2 b) 4) (d8Tor 3 F 4) b := by
  have hμ := CFSG.RankThree.PartTwo.Sec21.U4Lines.card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  intro B₀ hB₀
  rcases (u4_notationB_d8Tor_iff hb hbe hF hω).mp hB₀ with hB₀ | hB₀
  · subst B₀
    refine ⟨zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)),
      (u4_line_le_kOf hb hbe hF hω).1, (u4_notationB_d8Tor_iff hb hbe hF hω).mpr (Or.inr rfl),
      u4_line_four_ne_three hω, ?_, ?_⟩
    · intro Y hY
      rcases (u4_notationB_d8Tor_iff hb hbe hF hω).mp hY with hY | hY
      · exact Or.inl hY
      · exact Or.inr hY
    · intro p hp hpq
      exact ⟨u4_exists_centP hb hF hω hp hpq (Or.inl rfl),
        u4_two_le_pRank hb hF hω hp hpq⟩
  · subst B₀
    refine ⟨zpowers (torusD ((ω, ω) : D8Mod 3 F)),
      (u4_line_le_kOf hb hbe hF hω).2, (u4_notationB_d8Tor_iff hb hbe hF hω).mpr (Or.inl rfl),
      (u4_line_four_ne_three hω).symm, ?_, ?_⟩
    · intro Y hY
      rcases (u4_notationB_d8Tor_iff hb hbe hF hω).mp hY with hY | hY
      · exact Or.inr hY
      · exact Or.inl hY
    · intro p hp hpq
      refine ⟨u4_exists_centP hb hF hω hp hpq (Or.inr rfl), ?_⟩
      have h := u4_two_le_pRank hb hF hω hp hpq
      rwa [sup_comm] at h

theorem u4_torusAt (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    TorusAt (GL (Fin 4) F) (SU (unitaryInvolution F 2 b) 4) b := by
  intro E hE hEab hE9
  have hexp : ∀ x ∈ E.subgroupOf (SU (unitaryInvolution F 2 b) 4), x ^ 3 = 1 := by
    intro x hx
    refine Subtype.ext ?_
    simpa using hEab.2 (x : GL (Fin 4) F) (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_into_d8Tor_su (n := 4)
    (Or.inl rfl) CFSG.RankThree.PartOne.KFU.d8Comb_four hF Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartTwo.Sec21.three_dvd_two_pow_sub_one hbe)
    (E.subgroupOf (SU (unitaryInvolution F 2 b) 4)) hexp
  have hle : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL (MulAut.conj g) E ≤ d8Tor 3 F 4 := by
    rw [CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj g hE]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hE hx⟩ hx
  have hcard := card_d8Tor_three_four (F := F) (b := b) hbe hF
  have hmap : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL (MulAut.conj g) E = d8Tor 3 F 4 := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact le_of_eq (by rw [hcard, CFSG.RankThree.PartTwo.Sec21.U4Lines.card_mapL _ hE, hE9])
  have hconj : E.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom = d8Tor 3 F 4 := by
    rw [← CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj g hE]
    exact hmap
  exact TorusFacts.of_conj (g := (g : GL (Fin 4) F)) g.2 hE (by
    rw [hconj]
    exact u4_torusFacts_d8Tor hb hbe hF)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
