module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeFrame
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralMax
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
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

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
  CFSG.ClassicalInvolution CFSG.HardMathSupport.Lang.Coordinator

namespace ExcFrames

local instance threeFact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance threeNeZero : NeZero (3 : ℕ) := ⟨by norm_num⟩

theorem zetaVec_cartanChar {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin TwistTag.E6.tag.rank → ZMod 3) :
    cartanChar (τ := TwistTag.E6.tag)
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x) =
      TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
        (frameCoord TwistTag.E6.tag 3 x) := by
  funext j
  simp only [cartanChar, TableBExc.E6Three.zetaVec, frameCoord]
  conv_rhs => rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have hsymm : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
    rw [Tag.symmetrizedCartan]
    simp only [Tag.symmetrizer, TwistTag.tag]
    exact one_mul _
  rw [hsymm]
  have hc : TwistTag.E6.tag.cartan i j = TwistTag.E6.tag.cartan j i := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [hc, TableBExc.E6Three.zmodPowHom_zpow]

private theorem three_dvd_two_pow_sub_one_of_not_dvd_add_one {f : ℕ}
    (h3 : ¬ 3 ∣ 2 ^ f + 1) : 3 ∣ 2 ^ f - 1 := by
  have hfe : Even f := Nat.not_odd_iff_even.mp fun hodd =>
    h3 (UnitaryCenter.three_dvd_two_pow_add_one_of_odd hodd)
  obtain ⟨m, rfl⟩ := hfe
  have h4 : 3 ∣ 4 ^ m - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 m
  have hqeq : 2 ^ (m + m) = 4 ^ m := by
    rw [pow_add, ← mul_pow]
    norm_num
  rwa [hqeq]

theorem zeta_pow_frobQ_eq_self {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {f : ℕ}
    (h3 : ¬ 3 ∣ 2 ^ f + 1) : ζ ^ (2 ^ f) = ζ := by
  obtain ⟨k, hk⟩ := three_dvd_two_pow_sub_one_of_not_dvd_add_one h3
  have hpos : 0 < 2 ^ f := Nat.two_pow_pos f
  have hq : 2 ^ f = 3 * k + 1 := by omega
  rw [hq, pow_add, pow_mul, hζ, one_pow, one_mul, pow_one]

private theorem frobQ_apply_e6 {f : ℕ} (c : GaloisField 2 (2 * f)) :
    frobQ 2 f c = c ^ (2 ^ f) := by
  rw [frobQ]
  exact iterateFrobenius_def 2 f c

private theorem frobQ_frobQ_e6 {f : ℕ} (hf : 1 ≤ f) (c : GaloisField 2 (2 * f)) :
    frobQ 2 f (frobQ 2 f c) = c := by
  rw [frobQ_apply_e6, frobQ_apply_e6, ← pow_mul, ← pow_add]
  classical
  have : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have h := FiniteField.pow_card c
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * f) (by omega)] at h
  rw [show f + f = 2 * f by ring]
  exact h

section Membership


theorem rootDiagUnit_compatDiag_mem_compatTorus {q : ℕ} {K : Type} [Field K] [Finite K]
    {σ : K →+* K} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (h3 : Nat.gcd 3 (q + 1) = 1)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ) :
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u) ∈
      compatTorus (t := TwistTag.E6) σ := by
  obtain ⟨c, hc, hcb⟩ :=
    exists_compat_zpowMatrix_eq hK (σ := σ) hσ h3 (fun i => compatDiag_perm u i)
  rw [← hcb]
  change rootDiagUnit TwistTag.E6.tag
      (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c) ∈ compatTorus (t := TwistTag.E6) σ
  rw [← CFSG.RankThree.PartOne.TCX.Tri.torusCoordHom_eq_rootDiagUnit
    (τ := TwistTag.E6.tag) (K := K) c]
  exact (mem_compatTorus σ).2 ⟨c, hc, rfl⟩

theorem twE6ThreeTheta_add (s t : Fin Tag.F4.rank → ZMod 3) :
    twE6ThreeTheta (s + t) = twE6ThreeTheta s + twE6ThreeTheta t := by
  funext i
  simp [twE6ThreeTheta_apply, Pi.add_apply]

theorem twE6ThreeTheta_zero : twE6ThreeTheta (0 : Fin Tag.F4.rank → ZMod 3) = 0 := by
  funext i
  rw [twE6ThreeTheta_apply]
  simp

private def f4Equiv : Fin 4 ≃ Fin Tag.F4.rank := finCongr (by decide)

theorem exists_twE6ThreeTheta_eq (x : Fin Tag.E6.rank → ZMod 3)
    (h0 : x (e6Idx 0) = x e6Five) (h2 : x (e6Idx 2) = x e6Four) :
    ∃ s : Fin Tag.F4.rank → ZMod 3, twE6ThreeTheta s = x := by
  let rep : Fin Tag.F4.rank → Fin Tag.E6.rank :=
    fun a => e6Idx (![0, 2, 3, 1] (f4Equiv.symm a))
  refine ⟨fun a => x (rep a), ?_⟩
  funext i
  rw [twE6ThreeTheta_apply]
  obtain ⟨k, rfl⟩ := e6Equiv.surjective i
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · change x (rep (e6OrbitIdx (e6Equiv (4 : Fin 6)))) = x (e6Equiv (4 : Fin 6))
    have h4 : e6OrbitIdx (e6Equiv (4 : Fin 6)) = f4Equiv (1 : Fin 4) := by decide
    rw [h4]
    have hr : rep (f4Equiv (1 : Fin 4)) = e6Idx 2 := by decide
    rw [hr, show e6Equiv (4 : Fin 6) = e6Four from rfl, h2]
  · change x (rep (e6OrbitIdx (e6Equiv (5 : Fin 6)))) = x (e6Equiv (5 : Fin 6))
    have h5 : e6OrbitIdx (e6Equiv (5 : Fin 6)) = f4Equiv (0 : Fin 4) := by decide
    rw [h5]
    have hr : rep (f4Equiv (0 : Fin 4)) = e6Idx 0 := by decide
    rw [hr, show e6Equiv (5 : Fin 6) = e6Five from rfl, ← h0]

theorem frameDiag_theta_mem_compatTorus {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeTheta s) ∈
      compatTorus (t := TwistTag.E6) (frobQ 2 f) := by
  let v : Fin TwistTag.E6.tag.rank → ZMod 3 :=
    show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeFrame s
  let b : Fin TwistTag.E6.tag.rank → (GaloisField 2 (2 * f))ˣ :=
    TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ v
  have hframe : ∀ i : Fin TwistTag.E6.tag.rank, v (TwistTag.E6.perm i) = v i := by
    intro i
    exact twE6ThreeFrame_perm s i
  have hb : ∀ i : Fin TwistTag.E6.tag.rank, b (TwistTag.E6.perm i) = b i := by
    intro i
    show TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ v
        (TwistTag.E6.perm i) = TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ v i
    rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply, hframe i]
  have hbcompat : ∀ i : Fin TwistTag.E6.tag.rank,
      b (TwistTag.E6.perm i) = Units.map (frobQ 2 f).toMonoidHom (b i) := by
    intro i
    rw [hb i]
    refine Units.ext ?_
    change (b i : GaloisField 2 (2 * f)) = (frobQ 2 f) ((b i : GaloisField 2 (2 * f)))
    have hq : (frobQ 2 f) ((b i : GaloisField 2 (2 * f))) =
        (b i : GaloisField 2 (2 * f)) ^ (2 ^ f) := frobQ_apply_e6 _
    rw [hq]
    have hbval : (b i : GaloisField 2 (2 * f)) = ζ ^ ((v i).val) := by
      simp [b, TableBExc.E6Three.zetaVec_apply]
    rw [hbval]
    have hζq : ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) = ↑ζ :=
      congrArg Units.val (zeta_pow_frobQ_eq_self hζ h3)
    exact (calc
      ((↑ζ : GaloisField 2 (2 * f)) ^ (v i).val) ^ (2 ^ f)
          = (↑ζ : GaloisField 2 (2 * f)) ^ ((v i).val * 2 ^ f) :=
            (pow_mul _ _ _).symm
      _ = (↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f * (v i).val) := by ring
      _ = ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) ^ (v i).val := pow_mul _ _ _
      _ = (↑ζ : GaloisField 2 (2 * f)) ^ (v i).val := by rw [hζq]).symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := frobQ 2 f) hbcompat
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have hg : Nat.gcd 3 (2 ^ f + 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have hmem := rootDiagUnit_compatDiag_mem_compatTorus (q := 2 ^ f) hK
    (frobQ_apply_e6) hg u
  rw [hu] at hmem
  change rootDiagUnit TwistTag.E6.tag b ∈ compatTorus (t := TwistTag.E6) (frobQ 2 f)
  exact hmem


private theorem frameCoord_theta_fun (s : Fin Tag.F4.rank → ZMod 3) :
    frameCoord TwistTag.E6.tag 3
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta s i) = twE6ThreeFrame s := rfl

theorem frameDiag_theta_mem_torus {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeTheta s) ∈
      graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  have hσsurj : Function.Surjective (frobQ 2 f) :=
    Function.RightInverse.surjective fun c => frobQ_frobQ_e6 hf c
  rw [graphFixedRootTorus_eq_compatTorus (t := TwistTag.E6) (K := GaloisField 2 (2 * f))
    (σ := frobQ 2 f) hσsurj]
  exact frameDiag_theta_mem_compatTorus hf h3 hζ s

theorem frameDiag_theta_mem_C0 {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeTheta s) ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) :=
  compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := GaloisField 2 (2 * f))
    (σ := frobQ 2 f) (frameDiag_theta_mem_compatTorus hf h3 hζ s)

@[expose] noncomputable def twE6ThreeFrameHom {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    (ζ : (GaloisField 2 (2 * f))ˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) where
  toFun s :=
    ⟨frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (fun i : Fin TwistTag.E6.tag.rank =>
          twE6ThreeTheta (Multiplicative.toAdd s) i),
      frameDiag_theta_mem_C0 hf h3 hζ (Multiplicative.toAdd s)⟩
  map_one' := by
    apply Subtype.ext
    change frameDiag (τ := TwistTag.E6.tag) ζ hζ
      (fun i : Fin TwistTag.E6.tag.rank =>
        twE6ThreeTheta (Multiplicative.toAdd (1 : Multiplicative (Fin Tag.F4.rank → ZMod 3))) i) = 1
    rw [toAdd_one]
    have h : (fun i : Fin TwistTag.E6.tag.rank =>
        twE6ThreeTheta (0 : Fin Tag.F4.rank → ZMod 3) i) = 0 := by
      funext i
      rw [twE6ThreeTheta_zero]
      rfl
    rw [h, frameDiag_zero]
  map_mul' := fun s t => by
    apply Subtype.ext
    change frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (fun i : Fin TwistTag.E6.tag.rank =>
          twE6ThreeTheta (Multiplicative.toAdd (s * t)) i) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (fun i : Fin TwistTag.E6.tag.rank =>
            twE6ThreeTheta (Multiplicative.toAdd s) i) *
        frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (fun i : Fin TwistTag.E6.tag.rank =>
            twE6ThreeTheta (Multiplicative.toAdd t) i)
    rw [toAdd_mul]
    have h : (fun i : Fin TwistTag.E6.tag.rank =>
          twE6ThreeTheta (Multiplicative.toAdd s + Multiplicative.toAdd t) i) =
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta (Multiplicative.toAdd s) i) +
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta (Multiplicative.toAdd t) i) := by
      funext i
      rw [twE6ThreeTheta_add]
      rfl
    rw [h, frameDiag_add]

theorem twE6ThreeFrameHom_injective {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (twE6ThreeFrameHom hf h3 ζ hζ) := by
  intro s t hst
  have hval : frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta (Multiplicative.toAdd s) i) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta (Multiplicative.toAdd t) i) :=
    congrArg Subtype.val hst
  have hb : TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeFrame (Multiplicative.toAdd s)) =
      TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeFrame (Multiplicative.toAdd t)) := by
    apply rootDiagUnit_injective
    simpa [frameDiag, frameCoord_theta_fun] using hval
  have hframe : (show Fin TwistTag.E6.tag.rank → ZMod 3 from
        twE6ThreeFrame (Multiplicative.toAdd s)) =
      (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeFrame (Multiplicative.toAdd t)) :=
    TableBExc.E6Three.zetaVec_injective hζo hζ hb
  exact Multiplicative.toAdd.injective (twE6ThreeFrame_injective hframe)

theorem twE6ThreeFrameHom_apply {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    ((twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
          (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeFrame s)) := rfl

theorem twE6ThreeFrameHom_mem_torus {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.F4.rank → ZMod 3) :
    ((twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  rw [show ((twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (show Fin TwistTag.E6.tag.rank → ZMod 3 from twE6ThreeTheta s) from rfl]
  exact frameDiag_theta_mem_torus hf h3 hζ s

theorem exists_threeFrame {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    ∃ (ζ : (GaloisField 2 (2 * f))ˣ) (hζ : ζ ^ 3 = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      orderOf ζ = 3 ∧ Function.Injective ι₀ ∧
      (∀ s, ((ι₀ (Multiplicative.ofAdd s) : _) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s))) ∧
      (∀ s, ((ι₀ (Multiplicative.ofAdd s) : _) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ∧
      (∀ h : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
          graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) →
        h ^ 3 = 1 → h ∈ ι₀.range) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : (GaloisField 2 (2 * f))ˣ, orderOf ζ = 3 := by
    refine TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 (2 * f)) (p := 3) ?_
    rw [TwE6Toral.card_galoisField_two_mul f hf]
    have h4 : 3 ∣ 4 ^ f - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
    convert h4 using 2
    have h2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul]; ring_nf
    have h4' : 4 ^ f = 2 ^ (2 * f) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h2, h4']
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hq : ζ ^ (2 ^ f) = ζ := zeta_pow_frobQ_eq_self hζ h3
  let ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    twE6ThreeFrameHom hf h3 ζ hζ
  refine ⟨ζ, hζ, ι₀, hζo, twE6ThreeFrameHom_injective hf h3 hζo hζ, ?_, ?_, ?_⟩
  · intro s
    exact twE6ThreeFrameHom_apply hf h3 hζ s
  · intro s
    exact twE6ThreeFrameHom_mem_torus hf h3 hζ s
  · intro h hH h3h
    have hσsurj : Function.Surjective (frobQ 2 f) :=
      Function.RightInverse.surjective fun c => frobQ_frobQ_e6 hf c
    have hHc : (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        compatTorus (t := TwistTag.E6) (frobQ 2 f) := by
      rw [← graphFixedRootTorus_eq_compatTorus (t := TwistTag.E6)
        (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f) hσsurj]
      exact hH
    obtain ⟨c, hc, hct⟩ :=
      (mem_compatTorus (t := TwistTag.E6) (K := GaloisField 2 (2 * f))
        (σ := frobQ 2 f)).1 hHc
    have hroot : (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        rootDiagUnit TwistTag.E6.tag (cartanChar (τ := TwistTag.E6.tag) c) := by
      rw [← hct, CFSG.RankThree.PartOne.TCX.Tri.torusCoordHom_eq_rootDiagUnit
        (τ := TwistTag.E6.tag) (K := GaloisField 2 (2 * f)) c]
      rfl
    have hv3 : (rootDiagUnit TwistTag.E6.tag
        (cartanChar (τ := TwistTag.E6.tag) c)) ^ 3 = 1 := by
      rw [← hroot]
      exact congrArg Subtype.val h3h
    have hcart3 : (cartanChar (τ := TwistTag.E6.tag) c) ^ 3 = 1 := by
      apply rootDiagUnit_injective
      simpa [rootDiagUnit_pow, rootDiagUnit_one] using hv3
    have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      TwE6Toral.card_galoisField_two_mul f hf
    have hg : Nat.gcd 3 (2 ^ f + 1) = 1 :=
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have hc3 : c ^ 3 = 1 := by
      have hcart : cartanChar (τ := TwistTag.E6.tag) c =
          zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan c := rfl
      have hA : zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan (c ^ 3) = 1 := by
        have h1 : zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan (c ^ 3) =
            (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan c) ^ 3 := by
          rw [map_pow]
        rw [h1, ← hcart]
        exact hcart3
      have hmem : c ^ 3 ∈
          compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
            (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker :=
        ⟨pow_mem hc 3, hA⟩
      have hcard := card_compat_inf_ker_E6_of_card (K := GaloisField 2 (2 * f))
        (q := 2 ^ f) hK (frobQ_apply_e6)
      have hcard1 : Nat.card ↥(compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
          (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker) = 1 := by
        rw [hcard, hg]
      have hbot : compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
          (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker = ⊥ :=
        Subgroup.card_eq_one.1 hcard1
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hc3
    have hxfix : ∀ i, x (TwistTag.E6.perm i) = x i := by
      intro i
      have h1 : c (TwistTag.E6.perm i) = Units.map (frobQ 2 f).toMonoidHom (c i) := hc i
      rw [← hx] at h1
      have h2 : TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x
          (TwistTag.E6.perm i) = TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i := by
        rw [h1]
        refine Units.ext ?_
        change (frobQ 2 f) ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
            GaloisField 2 (2 * f))) =
          (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
            GaloisField 2 (2 * f))
        have hq' : (frobQ 2 f)
            ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
              GaloisField 2 (2 * f))) =
            ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
              GaloisField 2 (2 * f))) ^ (2 ^ f) := frobQ_apply_e6 _
        rw [hq']
        have hval : (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
            GaloisField 2 (2 * f)) = ζ ^ (x i).val := by
          simp [TableBExc.E6Three.zetaVec_apply]
        rw [hval]
        have hζq : ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) = ↑ζ :=
          congrArg Units.val hq
        exact (calc
          ((↑ζ : GaloisField 2 (2 * f)) ^ (x i).val) ^ (2 ^ f)
              = (↑ζ : GaloisField 2 (2 * f)) ^ ((x i).val * 2 ^ f) :=
                (pow_mul _ _ _).symm
          _ = (↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f * (x i).val) := by ring
          _ = ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) ^ (x i).val := pow_mul _ _ _
          _ = (↑ζ : GaloisField 2 (2 * f)) ^ (x i).val := by rw [hζq])
      have hzi : zmodPowHom ζ hζ (Multiplicative.ofAdd (x (TwistTag.E6.perm i))) =
          zmodPowHom ζ hζ (Multiplicative.ofAdd (x i)) := h2
      exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ hzi)
    have hx0 : x (e6Idx 0) = x e6Five := by
      have hp0 : e6Perm 0 = e6Five := by decide
      have h := hxfix 0
      rw [show TwistTag.E6.perm 0 = e6Perm 0 from rfl, hp0,
        show (0 : Fin TwistTag.E6.tag.rank) = e6Idx 0 from rfl] at h
      exact h.symm
    have hx2 : x (e6Idx 2) = x e6Four := by
      have hp2 : e6Perm 2 = e6Four := by decide
      have h := hxfix 2
      rw [show TwistTag.E6.perm 2 = e6Perm 2 from rfl, hp2,
        show (2 : Fin TwistTag.E6.tag.rank) = e6Idx 2 from rfl] at h
      exact h.symm
    obtain ⟨s, hs⟩ := exists_twE6ThreeTheta_eq x hx0 hx2
    refine ⟨Multiplicative.ofAdd s, ?_⟩
    apply Subtype.ext
    rw [show (ι₀ (Multiplicative.ofAdd s) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta s i) from rfl]
    rw [show (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta s i) =
        (fun i : Fin TwistTag.E6.tag.rank => x i) from by
      funext i; rw [hs]]
    change rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
          (frameCoord TwistTag.E6.tag 3 (fun i : Fin TwistTag.E6.tag.rank => x i))) = ↑h
    change rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
          (frameCoord TwistTag.E6.tag 3 x)) = ↑h
    rw [← zetaVec_cartanChar hζ x, hx]
    exact hroot.symm

end Membership

end ExcFrames

end CFSG.StandardType
