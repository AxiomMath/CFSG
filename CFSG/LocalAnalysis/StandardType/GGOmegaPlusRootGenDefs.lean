module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction

variable {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}

@[expose] noncomputable def omPlusTorusGL (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* GL (Fin m ⊕ Fin m) K :=
  (OmegaPilot.diagOmega K m).comp (MonoidHom.compLeft (TableBSymp.zmodPowHom hζ) (Fin m))

theorem omPlusTorusGL_apply (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    omPlusTorusGL hζ f = OmegaPilot.diagOmega K m fun j => TableBSymp.zmodPowHom hζ (f j) :=
  rfl

theorem omPlusTorusGL_eq_spTorusGL (hζ : ζ ^ p = 1) :
    omPlusTorusGL (K := K) (m := m) hζ = TableBSymp.spTorusGL hζ :=
  rfl

theorem omPlusTorusGL_mem [Finite K] [CharP K 2] (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    omPlusTorusGL hζ f ∈ StatedOmega (StatedQuadPlus m K) := by
  rw [omPlusTorusGL_apply]
  exact F4Pilot.diagOmega_mem_statedOmega _

@[expose] noncomputable def omPlusTorus [Finite K] [CharP K 2] (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K) :=
  (omPlusTorusGL hζ).codRestrict _ (omPlusTorusGL_mem hζ)

@[simp] theorem coe_omPlusTorus [Finite K] [CharP K 2] (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    (omPlusTorus hζ f : GL (Fin m ⊕ Fin m) K) = omPlusTorusGL hζ f :=
  rfl

variable (m) in
abbrev OmPlusIdx : Type := {ij : Fin m × Fin m // ij.1 < ij.2} × Bool

variable (p) in
@[expose] def omPlusRefl (x : OmPlusIdx m) : MulAut (Fin m → Multiplicative (ZMod p)) :=
  cond x.2
    (SpCoord.sgnAut x.1.1.1 * SpCoord.sgnAut x.1.1.2 *
      SpCoord.permAut (Equiv.swap x.1.1.1 x.1.1.2))
    (SpCoord.permAut (Equiv.swap x.1.1.1 x.1.1.2))

variable (p) in
theorem omPlusRefl_false {i j : Fin m} (hij : i < j) :
    omPlusRefl p (⟨(i, j), hij⟩, false) = SpCoord.permAut (Equiv.swap i j) :=
  rfl

variable (p) in
theorem omPlusRefl_true {i j : Fin m} (hij : i < j) :
    omPlusRefl p (⟨(i, j), hij⟩, true) =
      SpCoord.sgnAut i * SpCoord.sgnAut j * SpCoord.permAut (Equiv.swap i j) :=
  rfl

variable (K) in
@[expose] noncomputable def omPlusBlock (x : OmPlusIdx m) : Subgroup (GL (Fin m ⊕ Fin m) K) :=
  cond x.2
    ((OmegaPilot.siegelBlockGL K {x.1.1.1, x.1.1.2}).map
      (MulAut.conj (OmegaPilot.flipGL K {x.1.1.2})).toMonoidHom)
    (OmegaPilot.siegelBlockGL K {x.1.1.1, x.1.1.2})

variable (K) in
theorem omPlusBlock_false {i j : Fin m} (hij : i < j) :
    omPlusBlock K (⟨(i, j), hij⟩, false) = OmegaPilot.siegelBlockGL K {i, j} :=
  rfl

variable (K) in
theorem omPlusBlock_true {i j : Fin m} (hij : i < j) :
    omPlusBlock K (⟨(i, j), hij⟩, true) =
      (OmegaPilot.siegelBlockGL K {i, j}).map
        (MulAut.conj (OmegaPilot.flipGL K {j})).toMonoidHom :=
  rfl

theorem omPlusBlock_le [Finite K] (hK : 4 ≤ Nat.card K) (x : OmPlusIdx m) :
    omPlusBlock K x ≤ StatedOmega (StatedQuadPlus m K) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  have h2 : 2 ≤ ({i, j} : Finset (Fin m)).card := by
    rw [Finset.card_pair (ne_of_lt hij)]
  have hle := OmegaPilot.siegelBlockGL_le_statedOmega hK h2
  cases s
  · rw [omPlusBlock_false]
    exact hle
  · rw [omPlusBlock_true]
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (OmegaPilot.flipGL_mem_normalizer {j}) y).mp (hle hy)

end CFSG.StandardType

end
