module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H

open CFSG.Open

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem commute_of_mem_natImage_statedScalars {Γ : Subgroup (GL ι K)}
    {g x : MulAut (StdMod ι K)} (hg : g ∈ natImage (StatedScalars ι K)) (hx : x ∈ natImage Γ) :
    Commute g x := by
  obtain ⟨⟨_, u, rfl⟩, rfl⟩ := hg
  obtain ⟨⟨A, -⟩, rfl⟩ := hx
  change matHom (Matrix.GeneralLinearGroup.scalar ι u) * matHom A =
    matHom A * matHom (Matrix.GeneralLinearGroup.scalar ι u)
  rw [← map_mul, ← map_mul, Matrix.GeneralLinearGroup.scalar_commute]

theorem natImage_statedScalars_le_natNorm (Γ : Subgroup (GL ι K)) :
    natImage (StatedScalars ι K) ≤ natNorm Γ := fun _ hg =>
  Subgroup.centralizer_le_normalizer (natImage Γ : Set (MulAut (StdMod ι K)))
    (Subgroup.mem_centralizer_iff.mpr fun _ hx =>
      (commute_of_mem_natImage_statedScalars hg hx).eq.symm)

end CFSG.Quasithin.H
