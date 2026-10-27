module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.Quasithin.Recognition.RuTypeJ47l
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421Final
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.Recognition.RuTypeJ36f
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F431.F45

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Cosets

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem smul_xv_iff' (c : α.Completion Y) (k : c.G0) :
    k • c.xv = c.xv ↔ (k : Y) ∈ c.φ1.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left]

theorem smul_lv_iff' (c : α.Completion Y) (k : c.G0) :
    k • c.lv = c.lv ↔ (k : Y) ∈ c.φ2.range := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]

end Cosets

section Wiring


theorem sup_eq_TA : twoF4H ⊔ twoF4N = TA := J47.sup_twoF4H_N.trans twoF4M_eq_titsA

@[expose] noncomputable def phiA : ↥TA →* twoF4Setting.ι.G0 where
  toFun x := ⟨⟨x.1, by rw [sup_eq_TA]; exact x.2⟩, by
    rw [twoF4Setting.ι.gen]
    exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def toPerm (k : twoF4Setting.ι.G0) : Equiv.Perm (Fin 1755) :=
  Subtype.val (Subtype.val k)

theorem toPerm_phiA (x : ↥TA) : toPerm (phiA x) = x.1 := rfl

theorem phiA_injective : Function.Injective phiA := fun x y h =>
  Subtype.ext (by simpa [toPerm_phiA] using congrArg toPerm h)

theorem phiA_surjective : Function.Surjective phiA := by
  rintro ⟨⟨σ, hσ⟩, hg⟩
  exact ⟨⟨σ, by rw [← sup_eq_TA]; exact hσ⟩, rfl⟩

theorem mem_range_φ1_iff (k : twoF4Setting.ι.G0) :
    ((k : twoF4Setting.Yb) ∈ twoF4Setting.ι.φ1.range) ↔ toPerm k ∈ twoF4H := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [toPerm, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem mem_range_φ2_iff (k : twoF4Setting.ι.G0) :
    ((k : twoF4Setting.Yb) ∈ twoF4Setting.ι.φ2.range) ↔ toPerm k ∈ twoF4N := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [toPerm, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩


theorem xdatum_oct (h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925)) :
    XDatum twoF4Setting phiA octGraph (Sum.inl 0 : Vtx) (Sum.inr 0 : Vtx) where
  inj := phiA_injective
  N_eq := (MonoidHom.range_eq_top.2 phiA_surjective).symm
  dec g := by
    obtain ⟨y, rfl⟩ := phiA_surjective g
    exact ⟨y, 1, one_smul _ _, one_smul _ _, (mul_one _).symm⟩
  stab1 y := by
    rw [smul_xv_iff', mem_range_φ1_iff, smul_inl, Sum.inl.injEq]
    exact J47.mem_twoF4H_iff y.2
  stab2 y := by
    rw [smul_lv_iff', mem_range_φ2_iff, smul_inr, Sum.inr.injEq, lineHom_eq_iff]
    exact J47.mem_twoF4N_iff y.2
  disj y z := by
    rw [smul_inl, smul_inr]
    exact Sum.inl_ne_inr
  noadj1 y z := by
    rw [smul_inl, smul_inl]
    exact fun h => h
  noadj2 y z := by
    rw [smul_inr, smul_inr]
    exact fun h => h
  adj12 := h00

end Wiring

end CFSG.Quasithin.H13.F45Ru
