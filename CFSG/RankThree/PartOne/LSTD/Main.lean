module

public import CFSG.RankThree.PartOne.LSTD.MainAux
public import CFSG.RankThree.PartOne.LSTD.Frame
public import CFSG.RankThree.PartOne.LSTD.Transport
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.CTP.Frame1214
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.R12Final
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.RankThree.PartOne.LSTD.Cls
public import CFSG.RankThree.PartOne.LSTD.StdFam
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.CTP

variable {f : ℕ} {K : Type} [Field K]

theorem nonempty_lfam_of_iso {G : Type} [Group G] [Finite K] (hU : UnitaryFieldData 2 f K)
    (h5 : 5 ∣ 2 ^ f + 1) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) {L E K' : Subgroup G} {b : G}
    (hbL : b ∈ L) (hbE : b ∈ E) (hb1 : b ≠ 1) (hKL : K' ≤ L)
    (ε : ↥L ≃* StatedProj (unitarySU 2 f K 5))
    (hε : ∀ x : ↥L, (x : G) ∈ E ⊓ L ↔ ε x ∈ torusBar K f)
    (hKperf : Group.IsPerfect ↥K') (hKb : K' ≤ Subgroup.centralizer ({b} : Set G))
    (hKcard : Nat.card ↥K' = Nat.card ↥(unitarySU 2 f K 3)) :
    Nonempty (LFam L (E ⊓ L) f b K') := by
  classical
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hFb : b ∈ E ⊓ L := ⟨hbE, hbL⟩
  have hxT : ε b' ∈ torusBar K f := (hε b').mp hFb
  have hx1 : ε b' ≠ 1 := fun h => hb1 (by
    have := ε.injective (h.trans (map_one ε).symm)
    exact congrArg Subtype.val this)
  set X : Subgroup (StatedProj (unitarySU 2 f K 5)) := (K'.subgroupOf L).map ε.toMonoidHom with hX
  have hKLperf : Group.IsPerfect ↥(K'.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  have hXperf : Group.IsPerfect ↥X := by
    have e := Subgroup.equivMapOfInjective (K'.subgroupOf L) ε.toMonoidHom ε.injective
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hXc : X ≤ Subgroup.centralizer ({ε b'} : Set (StatedProj (unitarySU 2 f K 5))) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hKb (Subgroup.mem_subgroupOf.mp hk))
    have h1 : k * b' = b' * k := Subtype.ext hc
    show ε k * ε b' = ε b' * ε k
    rw [← map_mul, ← map_mul, h1]
  have hXcard : Nat.card ↥X = Nat.card ↥(unitarySU 2 f K 3) := by
    rw [hX, Subgroup.card_map_of_injective ε.injective, ← hKcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  obtain ⟨τ, hτb, hτX⟩ := classify_b hU h5 hζ hxT hx1 X hXperf hXc hXcard
  set g := Wmodel hU τ with hg
  let ε' : ↥L ≃* StatedProj (unitarySU 2 f K 5) := ε.trans (MulAut.conj g)
  have hε'val : ∀ y, ε' y = g * ε y * g⁻¹ := fun y => rfl
  have hε' : ∀ x : ↥L, (x : G) ∈ E ⊓ L ↔ ε' x ∈ torusBar K f := by
    intro x
    rw [hε x, hε'val]
    exact Subgroup.mem_normalizer_iff.mp (Wmodel_mem_normalizer hU h5 τ) (ε x)
  have hb₀T : ε' b' ∈ torusBar K f := (hε' b').mp hFb
  have hb₀J : ε' b' ∈ Jfun hU 3 4 := hτb
  have hb₀1 : ε' b' ≠ 1 := fun h => hb1 (by
    have := ε'.injective (h.trans (map_one ε').symm)
    exact congrArg Subtype.val this)
  let S := stdLFam hU h5 hζ ⟨hb₀T, hb₀J⟩ hb₀1
  let θ : StatedProj (unitarySU 2 f K 5) →* G := L.subtype.comp ε'.symm.toMonoidHom
  have hθinj : Function.Injective θ := Subtype.val_injective.comp ε'.symm.injective
  have hθε : ∀ y : ↥L, θ (ε' y) = (y : G) := fun y => by simp [θ]
  have hL : (⊤ : Subgroup (StatedProj (unitarySU 2 f K 5))).map θ = L := by
    ext y
    constructor
    · rintro ⟨p, -, rfl⟩
      exact (ε'.symm p).2
    · intro hy
      exact ⟨ε' ⟨y, hy⟩, trivial, hθε ⟨y, hy⟩⟩
  have hB : (torusBar K f).map θ = E ⊓ L := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hε' (ε'.symm p)).mpr (by simpa using hp)
    · intro hy
      exact ⟨ε' ⟨y, hy.2⟩, (hε' ⟨y, hy.2⟩).mp hy, hθε ⟨y, hy.2⟩⟩
  have hb : θ (ε' b') = b := hθε b'
  have hK : (Jfun hU 0 1 ⊔ Jfun hU 1 2).map θ = K' := by
    rw [← hτX]
    unfold conjBy
    rw [hX, Subgroup.map_map, Subgroup.map_map]
    have hcomp : (θ.comp (MulAut.conj g).toMonoidHom).comp ε.toMonoidHom = L.subtype :=
      MonoidHom.ext fun y => hθε y
    rw [hcomp]
    exact Subgroup.map_subgroupOf_eq_of_le hKL
  have key : ∀ (L₁ B₁ K₁ : Subgroup G) (b₁ : G), L₁ = L → B₁ = E ⊓ L → b₁ = b → K₁ = K' →
      LFam L₁ B₁ f b₁ K₁ → Nonempty (LFam L (E ⊓ L) f b K') := by
    rintro _ _ _ _ rfl rfl rfl rfl S
    exact ⟨S⟩
  exact key _ _ _ _ hL hB hb hK (LFam.map S θ hθinj)

theorem lStd_of_inputs (h107 h109 : Prop) :
    LStd (CFSG.Open.GriessAllModelsStatement) h107 h109 := by
  intro hGA _ _ G _ _ A c L E ctx f₀ hf1 h5 h25 hmodL b K I hLay
  have hh := ctx.hyp
  have hG : Sec12TwoGeneric 5 c L E := by
    rcases ctx.facts.two with hG | hS
    · exact hG
    · exact absurd (by rw [hS.center_card]) ctx.ten.2.2
  have hcore := KFOUT3.table_core_of hh hG
  obtain ⟨K₀, hKf, hKfin, hU, hζ, ε, hε⟩ := exists_r12iso hcore hGA hf1 h5 h25 hmodL
  obtain ⟨hbA, hbL, hb1⟩ := hLay.b_mem
  have hbE : b ∈ E := hh.A_le_E hbA
  have hKle : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [hLay.K_eq]
    exact Subgroup.map_subtype_le _
  have hKperf : Group.IsPerfect ↥K := hLay.K_qs.1
  have hmod3 : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 f₀ := by
    have := hLay.K_model.1 f₀ hf1 h5 (Or.inr hmodL)
    simpa using this
  have hKc : Subgroup.center ↥K = ⊥ :=
    psuThree_center_trivial hGA (even_of_five_dvd h5) hKperf hmod3
  have hKcard := card_eq_su_three hKc (even_of_five_dvd h5) hf1 hmod3 hU
  exact nonempty_lfam_of_iso hU h5 hζ hbL hbE hb1 (hKle.trans inf_le_left) ε hε hKperf
    (hKle.trans inf_le_right) hKcard

end CFSG.RankThree.PartOne.LSTD
