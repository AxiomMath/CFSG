module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.GH74.GLS.TwoThin.G.Cover
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.E2.CaseIINoComp
import CFSG.GH74.GLS.Bg.Rank
import CFSG.GH74.GLS.C3.Layer1.BackLeaves
import CFSG.GH74.GLS.C3.Layer1.Split
import CFSG.GH74.GLS.C3.Layer3.Main
import CFSG.GH74.GLS.IVK.A7.Glue
import CFSG.GH74.GLS.IVK.L2.BN
import CFSG.GH74.GLS.IVK.L2.BorelFive
import CFSG.GH74.GLS.IVK.L2.Lemma114
import CFSG.GH74.GLS.IVK.L2.Lemma12k
import CFSG.GH74.GLS.IVK.L2.Lemma13fc
import CFSG.GH74.GLS.IVK.L2.Lemma14f
import CFSG.GH74.GLS.IVK.L2.Lemma14j
import CFSG.GH74.GLS.IVK.L2.Lemma19b
import CFSG.GH74.GLS.IVK.Lifted.Outer14
import CFSG.GH74.GLS.IVK.Prod.Lemma31
import CFSG.GH74.GLS.IVK.Proofs
import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
import CFSG.GH74.GLS.IVK.Statements
import CFSG.GH74.GLS.SP.Local.SPLUniqInv
import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.Generic.Front.Final
import CFSG.GH74.Generic.FrontEnd
import CFSG.GH74.Generic.S1.LinFull
import CFSG.LieType.Multipliers.L34CenterExponent
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwo
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Bridge.TableSurj
import CFSG.Sporadic.HN.LevelChainSpec
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.McL
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.StronglyEmbedded.MatrixGroups.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
import CFSG.Walter.J1.Inv
import Certificates.Certificate3085Base
import Certificates.Certificate5007
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.QTwo

open CFSG
open CFSG.Open

theorem qtwoDB7_diag_torus {Y : Type} [Group Y] [Finite Y] {τ : Y} (hτ : τ ^ 3 = 1)
    {A : Subgroup Y} (hA : CFSG.IsComponent A)
    (h01 : A ≠ A.map (MulAut.conj τ).toMonoidHom)
    (h02 : A ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom)
    (h12 : A.map (MulAut.conj τ).toMonoidHom ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom)
    {Jb : Type} [Group Jb] (hJnab : ∃ a b : Jb, a * b ≠ b * a)
    (φ : ↥A →* Jb) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center ↥A)
    {r : ℕ} (hT : GGTorusLift 3 r (Jb ⧸ Subgroup.center Jb)) :
    ∃ E U : Subgroup Y, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Y) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (3 * r) := by
  classical
  have hJbnt : Nontrivial (Jb ⧸ Subgroup.center Jb) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    obtain ⟨a, b, hab⟩ := hJnab
    have ha : a ∈ Subgroup.center Jb := by rw [htop]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm
  haveI := hJbnt
  let ψ : ↥A →* Jb ⧸ Subgroup.center Jb :=
    (QuotientGroup.mk' (Subgroup.center Jb)).comp φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Jb) z
    obtain ⟨a, rfl⟩ := hφ y
    exact ⟨a, rfl⟩
  have hker_le : ψ.ker ≤ Subgroup.center ↥A :=
    CFSG.GH74.GLS.TwoThin.ker_le_center_of_surjective hA.1 ψ hψ
  have hcenter_le : Subgroup.center ↥A ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change (φ x : Jb ⧸ Subgroup.center Jb) = 1
    rw [QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_center_iff]
    intro j
    obtain ⟨y, rfl⟩ := hφ j
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hx y
  have hker_eq : ψ.ker = Subgroup.center ↥A := le_antisymm hker_le hcenter_le
  obtain ⟨U0, E0, hU0ne, hU0p, hE0norm, hE0el, hE0card, hE0disj⟩ :=
    hT ↥A ψ hψ hker_le hA.1.1.commutator_eq_top
  rw [hker_eq] at hE0disj
  let c1 : Y →* Y := (MulAut.conj τ).toMonoidHom
  let c2 : Y →* Y := (MulAut.conj (τ ^ 2)).toMonoidHom
  let A1 : Subgroup Y := A.map c1
  let A2 : Subgroup Y := A.map c2
  let Ey : Subgroup Y := E0.map A.subtype
  let U : Subgroup Y := U0.map A.subtype
  let E1 : Subgroup Y := Ey.map c1
  let E2 : Subgroup Y := Ey.map c2
  let F : Subgroup Y := Ey ⊔ (E1 ⊔ E2)
  let ZA : Subgroup Y := (Subgroup.center ↥A).map A.subtype
  have hA1 : IsComponent A1 :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj τ) hA
  have hA2 : IsComponent A2 :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (τ ^ 2)) hA
  have hcommA_A1 : ∀ x ∈ A, ∀ y ∈ A1, x * y = y * x :=
    fun x hx y hy => CFSG.StandardType.ggCommute_of_isComponent_ne hA1 hA h01 hx hy
  have hcommA_A2 : ∀ x ∈ A, ∀ y ∈ A2, x * y = y * x :=
    fun x hx y hy => CFSG.StandardType.ggCommute_of_isComponent_ne hA2 hA h02 hx hy
  have hcommA1_A2 : ∀ x ∈ A1, ∀ y ∈ A2, x * y = y * x :=
    fun x hx y hy => CFSG.StandardType.ggCommute_of_isComponent_ne hA2 hA1 h12 hx hy
  have hEyA : Ey ≤ A := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact e.2
  have hE1A1 : E1 ≤ A1 := Subgroup.map_mono hEyA
  have hE2A2 : E2 ≤ A2 := Subgroup.map_mono hEyA
  have hU_le_A : U ≤ A := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact u.2
  have hZA : Ey ⊓ ZA = ⊥ := by
    show (E0.map A.subtype) ⊓ ((Subgroup.center ↥A).map A.subtype) = ⊥
    rw [← Subgroup.map_inf E0 (Subgroup.center ↥A) A.subtype A.subtype_injective, hE0disj,
      Subgroup.map_bot]
  have hZA_le : A ⊓ (A1 ⊔ A2) ≤ ZA := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Y) * x = x * (g : Y)
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (CFSG.mem_sup_of_commute (fun a ha b hb => hcommA1_A2 a ha b hb)).mp hx.2
    calc (g : Y) * (u * v) = ((g : Y) * u) * v := by group
      _ = (u * (g : Y)) * v := by rw [hcommA_A1 g g.2 u hu]
      _ = u * ((g : Y) * v) := by group
      _ = u * (v * (g : Y)) := by rw [hcommA_A2 g g.2 v hv]
      _ = (u * v) * (g : Y) := by group
  have hE12A12 : E1 ⊔ E2 ≤ A1 ⊔ A2 :=
    sup_le (fun x hx => Subgroup.mem_sup_left (hE1A1 hx))
      (fun x hx => Subgroup.mem_sup_right (hE2A2 hx))
  have hEyE1 : Ey ⊓ E1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : x ∈ ZA := hZA_le ⟨hEyA hx.1, Subgroup.mem_sup_left (hE1A1 hx.2)⟩
    have hxbot : x ∈ Ey ⊓ ZA := ⟨hx.1, hxZ⟩
    rw [hZA] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  have hEy_sup : Ey ⊓ (E1 ⊔ E2) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : x ∈ ZA := hZA_le ⟨hEyA hx.1, hE12A12 hx.2⟩
    have hxbot : x ∈ Ey ⊓ ZA := ⟨hx.1, hxZ⟩
    rw [hZA] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  have hc11 : ∀ x : Y, c1 (c1 x) = c2 x := by
    intro x
    calc c1 (c1 x) = ((MulAut.conj τ) * (MulAut.conj τ)) x := rfl
      _ = (MulAut.conj (τ * τ)) x := by
            rw [← map_mul (f := (MulAut.conj : Y →* MulAut Y)) τ τ]
      _ = c2 x := by
            show (MulAut.conj (τ * τ)) x = (MulAut.conj (τ ^ 2)) x
            rw [pow_two]
  have hE2_eq : E2 = E1.map c1 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨c1 y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, hc11 y⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨z, hz, (hc11 z).symm⟩
  have hE1E2 : E1 ⊓ E2 = ⊥ := by
    rw [hE2_eq]
    show Ey.map c1 ⊓ E1.map c1 = ⊥
    rw [← Subgroup.map_inf Ey E1 c1 (MulAut.conj τ).injective, hEyE1, Subgroup.map_bot]
  have hEyel : CFSG.Open.IsElemAbelian 3 Ey := CFSG.Open.IsElemAbelian.map hE0el A.subtype
  have hE1el : CFSG.Open.IsElemAbelian 3 E1 := CFSG.Open.IsElemAbelian.map hEyel c1
  have hE2el : CFSG.Open.IsElemAbelian 3 E2 := CFSG.Open.IsElemAbelian.map hEyel c2
  have hEycard : Nat.card Ey = 3 ^ r := by
    show Nat.card (E0.map A.subtype) = 3 ^ r
    rw [Subgroup.card_subtype A E0, hE0card]
  have hE1card : Nat.card E1 = 3 ^ r := by
    show Nat.card (Ey.map c1) = 3 ^ r
    rw [Subgroup.card_map_of_injective (f := c1) (MulAut.conj τ).injective, hEycard]
  have hE2card : Nat.card E2 = 3 ^ r := by
    show Nat.card (Ey.map c2) = 3 ^ r
    rw [Subgroup.card_map_of_injective (f := c2) (MulAut.conj (τ ^ 2)).injective, hEycard]
  have hcommEy_E1 : ∀ a ∈ Ey, ∀ b ∈ E1, a * b = b * a :=
    fun a ha b hb => hcommA_A1 a (hEyA ha) b (hE1A1 hb)
  have hcommEy_E2 : ∀ a ∈ Ey, ∀ b ∈ E2, a * b = b * a :=
    fun a ha b hb => hcommA_A2 a (hEyA ha) b (hE2A2 hb)
  have hcommE1_E2 : ∀ a ∈ E1, ∀ b ∈ E2, a * b = b * a :=
    fun a ha b hb => hcommA1_A2 a (hE1A1 ha) b (hE2A2 hb)
  have hcommEy_sup : ∀ a ∈ Ey, ∀ b ∈ E1 ⊔ E2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (CFSG.mem_sup_of_commute (fun x hx y hy => hcommE1_E2 x hx y hy)).mp hb
    calc a * (u * v) = (a * u) * v := by group
      _ = (u * a) * v := by rw [hcommEy_E1 a ha u hu]
      _ = u * (a * v) := by group
      _ = u * (v * a) := by rw [hcommEy_E2 a ha v hv]
      _ = (u * v) * a := by group
  have hE1supE2el : CFSG.Open.IsElemAbelian 3 (E1 ⊔ E2) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE1el hE2el hcommE1_E2
  have hFel : CFSG.Open.IsElemAbelian 3 F :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEyel hE1supE2el hcommEy_sup
  have hEy_norm : Ey ≤ Subgroup.normalizer (U : Set Y) :=
    (Subgroup.map_mono hE0norm).trans (Subgroup.le_normalizer_map A.subtype)
  have hE1_cent : E1 ≤ Subgroup.centralizer (U : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommA_A1 y (hU_le_A hy) x (hE1A1 hx)
  have hE2_cent : E2 ≤ Subgroup.centralizer (U : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommA_A2 y (hU_le_A hy) x (hE2A2 hx)
  have hFnorm : F ≤ Subgroup.normalizer (U : Set Y) :=
    sup_le hEy_norm (sup_le (hE1_cent.trans (Subgroup.centralizer_le_normalizer _))
      (hE2_cent.trans (Subgroup.centralizer_le_normalizer _)))
  have hUp : IsPGroup 2 U := hU0p.map A.subtype
  have hUne : U ≠ ⊥ := by
    intro hbot
    exact hU0ne ((Subgroup.map_eq_bot_iff_of_injective U0 A.subtype_injective).mp hbot)
  have hcard1 : Nat.card F = Nat.card Ey * Nat.card ↥(E1 ⊔ E2) :=
    CFSG.card_sup_eq_mul_of_commute Ey (E1 ⊔ E2) hcommEy_sup hEy_sup
  have hcard2 : Nat.card ↥(E1 ⊔ E2) = Nat.card E1 * Nat.card E2 :=
    CFSG.card_sup_eq_mul_of_commute E1 E2 hcommE1_E2 hE1E2
  have hFcard : Nat.card F = 3 ^ (3 * r) := by
    rw [hcard1, hcard2, hEycard, hE1card, hE2card]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  exact ⟨F, U, hUne, hUp, hFnorm, hFel, hFcard⟩

end CFSG.StandardType.QTwo

end
