module

public import CFSG.Quasithin.Background.SimsF5Ah
public import CFSG.Quasithin.Background.SimsF5ModelO2
public import CFSG.Quasithin.Background.SimsF5Ctx
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A1cTransferVariants
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
public import CFSG.Quasithin.Background.SimsF5Ai
public import CFSG.Quasithin.Background.SimsF5Main
public import CFSG.Quasithin.Background.SimsF5Phi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutHalf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut

section SubgroupOf

variable {X : Type*} [Group X]

theorem mc_pCoreOf_subgroupOf {p : ℕ} {H K : Subgroup X} (hHK : H ≤ K) :
    pCoreOf p (H.subgroupOf K) = (pCoreOf p H).subgroupOf K := by
  let e : ↥(H.subgroupOf K) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHK
  have he := CFSG.pCore_map_iso p e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, rfl⟩
    rw [← he]
    exact ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [← he] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    have h1 : ((e y : ↥H) : X) = (w : X) := congrArg Subtype.val hyw
    have h2 : (w : X) = (x : X) := hwx
    exact h1.trans h2

theorem mc_centerOf_subgroupOf {A K : Subgroup X} (hAK : A ≤ K) :
    centerOf (A.subgroupOf K) = (centerOf A).subgroupOf K := by
  ext x
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => ?_⟩
    have := hc ⟨a, hAK ha⟩ ha
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => Subtype.ext (hc a ha)⟩

theorem mc_normalizer_subgroupOf {B K : Subgroup X} (hBK : B ≤ K) :
    Subgroup.normalizer ((B.subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (K ⊓ Subgroup.normalizer (B : Set X)).subgroupOf K := by
  ext g
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨g.2, fun b => ?_⟩
    constructor
    · intro hb
      have := (h ⟨b, hBK hb⟩).1 hb
      simpa using this
    · intro hb
      have hbK : b ∈ K := by
        have : (g : X)⁻¹ * ((g : X) * b * (g : X)⁻¹) * (g : X) = b := by group
        rw [← this]
        exact K.mul_mem (K.mul_mem (K.inv_mem g.2) (hBK hb)) g.2
      have := (h ⟨b, hbK⟩).2 hb
      simpa using this
  · rintro ⟨-, h⟩ b
    have := h (b : X)
    simpa using this

end SubgroupOf

section Model


@[expose] noncomputable def modelJ1 : ↥P1h →* ↥MDot :=
  (Subgroup.inclusion (inf_le_left : M0Dot ≤ MDot)).comp (lamA.toMonoidHom.comp P1h.subtype)

@[expose] noncomputable def modelJ2 : ↥P2h →* ↥MDot :=
  (Subgroup.inclusion (inf_le_left : M0Dot ≤ MDot)).comp (lamA.toMonoidHom.comp P2h.subtype)

theorem modelJ1_apply (x : ↥P1h) : ((modelJ1 x : ↥MDot) : GL6) = ((lamA x : ↥M0Dot) : GL6) := rfl

theorem modelJ2_apply (x : ↥P2h) : ((modelJ2 x : ↥MDot) : GL6) = ((lamA x : ↥M0Dot) : GL6) := rfl

theorem modelJ1_injective : Function.Injective modelJ1 := fun x y h => by
  have h' : ((modelJ1 x : ↥MDot) : GL6) = ((modelJ1 y : ↥MDot) : GL6) := congrArg Subtype.val h
  rw [modelJ1_apply, modelJ1_apply] at h'
  exact Subtype.ext (lamA.injective (Subtype.ext h'))

theorem modelJ2_injective : Function.Injective modelJ2 := fun x y h => by
  have h' : ((modelJ2 x : ↥MDot) : GL6) = ((modelJ2 y : ↥MDot) : GL6) := congrArg Subtype.val h
  rw [modelJ2_apply, modelJ2_apply] at h'
  exact Subtype.ext (lamA.injective (Subtype.ext h'))

theorem mc_exists_lamA {g : GL6} (hg : g ∈ M0Dot) : ∃ a : Ah, ((lamA a : ↥M0Dot) : GL6) = g :=
  ⟨lamA.symm ⟨g, hg⟩, by simp⟩

theorem modelJ1_range : modelJ1.range = M1Dot.subgroupOf MDot := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, rfl⟩
    rw [modelJ1_apply]
    exact (lamA_mem_M1Dot x).2 x.2
  · intro hg
    obtain ⟨a, ha⟩ := mc_exists_lamA (M1Dot_le_M0Dot hg)
    have haP : a ∈ P1h := (lamA_mem_M1Dot a).1 (ha ▸ hg)
    exact ⟨⟨a, haP⟩, Subtype.ext (by rw [modelJ1_apply]; exact ha)⟩

theorem modelJ2_range : modelJ2.range = M2Dot.subgroupOf MDot := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, rfl⟩
    rw [modelJ2_apply]
    exact (lamA_mem_M2Dot x).2 x.2
  · intro hg
    obtain ⟨a, ha⟩ := mc_exists_lamA (M2Dot_le_M0Dot hg)
    have haP : a ∈ P2h := (lamA_mem_M2Dot a).1 (ha ▸ hg)
    exact ⟨⟨a, haP⟩, Subtype.ext (by rw [modelJ2_apply]; exact ha)⟩

theorem modelJ_B (b : ↥Bh) :
    modelJ1 (Subgroup.inclusion Bh_le_P1h b) = modelJ2 (Subgroup.inclusion Bh_le_P2h b) := rfl

theorem modelJ_I : ∀ g ∈ M1Dot.subgroupOf MDot ⊓ M2Dot.subgroupOf MDot,
    ∃ b : ↥Bh, modelJ1 (Subgroup.inclusion Bh_le_P1h b) = g := by
  intro g hg
  have h1 : (g : GL6) ∈ M1Dot := hg.1
  have h2 : (g : GL6) ∈ M2Dot := hg.2
  obtain ⟨a, ha⟩ := mc_exists_lamA (M1Dot_le_M0Dot h1)
  have haP1 : a ∈ P1h := (lamA_mem_M1Dot a).1 (ha ▸ h1)
  have haP2 : a ∈ P2h := (lamA_mem_M2Dot a).1 (ha ▸ h2)
  exact ⟨⟨a, haP1, haP2⟩, Subtype.ext (by rw [modelJ1_apply]; exact ha)⟩

@[expose] noncomputable def modelIso : AutIso (M1Dot.subgroupOf MDot) (M2Dot.subgroupOf MDot) :=
  autIsoOfHoms modelJ1 modelJ2 modelJ1_injective modelJ2_injective modelJ1_range modelJ2_range
    modelJ_B modelJ_I

@[expose] noncomputable def zDotM : ↥MDot := ⟨zDot, zDot_mem_GDot.1⟩

theorem modelIso_toG_xB : modelIso.toG xB = zDotM := by
  apply Subtype.ext
  show ((lamA xA : ↥M0Dot) : GL6) = zDot
  exact lamA_xA

theorem modelCtx_res : pResidual 2 ↥MDot = ⊤ :=
  pResidual_two_eq_top isSimpleGroup_MDot exists_noncomm_MDot

theorem modelCtx_cz : Subgroup.centralizer ({zDotM} : Set ↥MDot) ≤ M1Dot.subgroupOf MDot := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  refine ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.1 hg
  exact congrArg Subtype.val this

theorem mc_mem_zpowers_of_mul_self {Y : Type*} [Group Y] {a x : Y} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := hx
  show a ^ k = 1 ∨ a ^ k = a
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  have hk' : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, ha2, one_zpow, mul_one]
  rw [hk']
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h <;> rw [h] <;> simp

theorem mc_zDot_ne_one : zDot ≠ 1 := fun h => by
  have := congrArg (fun g : GL6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0) h
  revert this
  simp only [zDot, eJ]
  decide

theorem mc_normalizer_zpowers_zDot :
    MDot ⊓ Subgroup.normalizer ((Subgroup.zpowers zDot : Subgroup GL6) : Set GL6) = M1Dot := by
  have hz2 : zDot * zDot = 1 := zDot_mul_self
  ext g
  simp only [M1Dot, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hg, h⟩
    refine ⟨hg, ?_⟩
    have hmem : g * zDot * g⁻¹ ∈ Subgroup.zpowers zDot := (h zDot).1 (Subgroup.mem_zpowers zDot)
    have hz1 : zDot ≠ 1 := mc_zDot_ne_one
    rcases (mc_mem_zpowers_of_mul_self hz2 hmem) with h1 | h1
    · exfalso
      apply hz1
      have : zDot = g⁻¹ * (g * zDot * g⁻¹) * g := by group
      rw [this, h1]
      group
    · calc g * zDot = g * zDot * g⁻¹ * g := by group
        _ = zDot * g := by rw [h1]
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun n => ?_⟩
    have hconj : ∀ k : ℤ, g * zDot ^ k * g⁻¹ = zDot ^ k := fun k => by
      rw [← conj_zpow, show g * zDot * g⁻¹ = zDot by rw [hc]; group]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hconj k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : n = g⁻¹ * (g * n * g⁻¹) * g := by group
      rw [this, ← hk, show g⁻¹ * zDot ^ k * g = zDot ^ k from by
        rw [show g⁻¹ * zDot ^ k * g = g⁻¹ * (g * zDot ^ k * g⁻¹) * g by
          rw [hconj k]] ; group]

theorem modelCtx_N1 :
    Subgroup.normalizer (centerOf (pCoreOf 2 (M1Dot.subgroupOf MDot)) : Set ↥MDot) =
      M1Dot.subgroupOf MDot := by
  have hQ : Q1Dot ≤ MDot := (Subgroup.map_subtype_le _).trans (inf_le_left : M1Dot ≤ MDot)
  rw [mc_pCoreOf_subgroupOf (H := M1Dot) (K := MDot) inf_le_left, show pCoreOf 2 M1Dot = Q1Dot from rfl,
    mc_centerOf_subgroupOf hQ, centerOf_Q1Dot,
    mc_normalizer_subgroupOf (Subgroup.zpowers_le.2 zDot_mem_GDot.1),
    mc_normalizer_zpowers_zDot]

theorem modelCtx_N2 :
    Subgroup.normalizer (centerOf (pCoreOf 2 (M2Dot.subgroupOf MDot)) : Set ↥MDot) =
      M2Dot.subgroupOf MDot := by
  have hQ : Q2Dot ≤ MDot := Q2Dot_le_GDot.trans inf_le_left
  have hab : centerOf Q2Dot = Q2Dot := by
    refine le_antisymm inf_le_left fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := isEn_Q2Dot.1 ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  rw [mc_pCoreOf_subgroupOf (H := M2Dot) (K := MDot) inf_le_left, pCoreOf_M2Dot, mc_centerOf_subgroupOf hQ, hab,
    mc_normalizer_subgroupOf hQ, MDot_inf_normalizer_Q2Dot]

@[expose] noncomputable def modelCtx :
    AutCtx ↥MDot (M1Dot.subgroupOf MDot) (M2Dot.subgroupOf MDot) zDotM :=
  autCtxOf modelIso modelIso_toG_xB modelCtx_res modelCtx_cz modelCtx_N1 modelCtx_N2

theorem modelCtx_phi1 (x : ↥P1h) :
    (((modelCtx.iso.phi1 x : ↥MDot)) : GL6) = ((lamA x : ↥M0Dot) : GL6) := rfl

theorem modelCtx_phi2 (x : ↥P2h) :
    (((modelCtx.iso.phi2 x : ↥MDot)) : GL6) = ((lamA x : ↥M0Dot) : GL6) := rfl

theorem modelCtx_toG (b : ↥Bh) :
    ((modelCtx.iso.toG b : ↥MDot) : GL6) = ((lamA b : ↥M0Dot) : GL6) := rfl

end Model

end CFSG.Quasithin.SimsF5
