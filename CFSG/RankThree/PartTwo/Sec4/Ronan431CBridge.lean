module

public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.Assembly.GL83LieDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431C

open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

theorem nonempty_projSL_equiv_lieA {r f : ℕ} (hf : 1 ≤ f)
    (hv : (TauCeti.LieTypeIndex.A r ⟨2, f, Nat.prime_two, hf⟩).Valid) :
    Nonempty (projSL (r + 1) (GaloisField 2 f) ≃*
      (TauCeti.CFSGIndex.lie ⟨.A r ⟨2, f, Nat.prime_two, hf⟩, hv⟩).Group) := by
  haveI : Fact (Nat.Prime (⟨2, f, Nat.prime_two, hf⟩ : TauCeti.PrimePower).p) := ⟨Nat.prime_two⟩
  exact ⟨(CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL r _ hv).symm⟩

theorem nonempty_projSU_equiv_lieTwistedA {r f : ℕ} (hf : 1 ≤ f)
    (hv : (TauCeti.LieTypeIndex.twistedA r ⟨2, f, Nat.prime_two, hf⟩).Valid) :
    Nonempty (projSU (r + 1) 2 f ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA r ⟨2, f, Nat.prime_two, hf⟩, hv⟩).Group) := by
  haveI : Fact (Nat.Prime (⟨2, f, Nat.prime_two, hf⟩ : TauCeti.PrimePower).p) := ⟨Nat.prime_two⟩
  exact ⟨(CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU r _ hv).symm⟩

theorem nonempty_projSp_two_equiv_lieB2 {f : ℕ} (hf : 1 ≤ f)
    (hv : (TauCeti.LieTypeIndex.B 2 ⟨2, f, Nat.prime_two, hf⟩).Valid) :
    Nonempty (projSp 2 (GaloisField 2 f) ≃*
      (TauCeti.CFSGIndex.lie ⟨.B 2 ⟨2, f, Nat.prime_two, hf⟩, hv⟩).Group) := by
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj hv
    (k := GaloisField 2 f) (by rw [GaloisField.card 2 f (by omega), TauCeti.PrimePower.card_def])
  exact ⟨(CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 f)).trans e⟩

theorem nonempty_projSp_equiv_lieB {r f : ℕ} (hr : 3 ≤ r) (hf : 1 ≤ f)
    (hv : (TauCeti.LieTypeIndex.B r ⟨2, f, Nat.prime_two, hf⟩).Valid) :
    Nonempty (projSp r (GaloisField 2 f) ≃*
      (TauCeti.CFSGIndex.lie ⟨.B r ⟨2, f, Nat.prime_two, hf⟩, hv⟩).Group) :=
  (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.nonempty_typeBGroupEquivProjSp r f hr _ hv rfl
    rfl).map MulEquiv.symm

theorem nonempty_projOmegaMinus_equiv_lieTwistedD {m f : ℕ} (hf : 1 ≤ f) {b c : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (hv : (TauCeti.LieTypeIndex.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩).Valid) :
    Nonempty (projOmegaMinus m (GaloisField 2 f) b c ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩).Group) := by
  have hm : 3 ≤ m := by
    have h := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    simp only at h
    omega
  let θ : projOmegaMinus m (GaloisField 2 f) b c ≃*
      StatedProj (StatedOmega (StatedQuadMinus (m + 1) (GaloisField 2 f) b c)) :=
    CFSG.Open.StatedAPI.mapMkEquivStatedProj
      (StatedOmega (StatedQuadMinus (m + 1) (GaloisField 2 f) b c))
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      (m + 1) ⟨2, f, Nat.prime_two, hf⟩ hv
  have hK : Nat.card (GaloisField 2 f) = TauCeti.ValidLieTypeIndex.fieldOrder
      ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩ := by
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic
          ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩ = 2 from
        TauCeti.LieTypeIndex.characteristic_twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩,
      show TauCeti.ValidLieTypeIndex.fieldExponent
          ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩ = f from
        TauCeti.LieTypeIndex.fieldExponent_twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩,
      GaloisField.card 2 f (by omega)]
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
    ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩ (GaloisField 2 f) hK
  have _ : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨.twistedD (m + 1) ⟨2, f, Nat.prime_two, hf⟩, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := m + 1)
    (by omega) (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hbc) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := m + 1) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  exact ⟨((θ.trans e1).trans e2).trans eT.symm⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan431C
