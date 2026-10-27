module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.FixedSpan
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlusTwo
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open CFSG.Open Matrix

theorem sylowFixedLine_of_isPGroup {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Field K] [Finite K] [CharP K 2] {Γ : Subgroup (GL ι K)} (U : Subgroup ↥Γ)
    (hU : IsPGroup 2 ↥U) (e : ι → K)
    (hfix : ∀ v : ι → K,
      (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) → v ∈ Submodule.span K {e}) :
    SylowFixedLine Γ e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨x, hx⟩ := KTabA.exists_fixed_sylow_eq_span 2 U hU e hfix S
  refine ⟨x, fun v => (hx v).trans ?_⟩
  rw [Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem sylowFixedLine_minus (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    SylowFixedLine (StatedOmega (StatedQuadMinus 2 K b c)) (e1M K) := by
  obtain ⟨U, hU, hfix⟩ := KTabA.exists_fixedLine_statedOmega_minus_single (K := K) le_rfl hirr
  exact sylowFixedLine_of_isPGroup U hU _ hfix

theorem sylowFixedLine_plus (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    SylowFixedLine (StatedOmega (StatedQuadPlus 2 K)) (e1P K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU, hfix⟩ :=
    KTabA.exists_fixedLine_statedOmega_plus_two_single (K := K) 2 (by omega)
  exact sylowFixedLine_of_isPGroup U hU _ hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
