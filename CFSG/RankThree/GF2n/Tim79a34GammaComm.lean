module

public import CFSG.RankThree.GF2n.Tim79a34GammaCoords
public import CFSG.RankThree.GF2n.Tim79a34GammaEigen
public import CFSG.Sporadic.ThSchreier.Row
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec68Stmt
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Linear.TwoCentres
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
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
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec34Centre
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
open Matrix
open scoped commutatorElement

section Proj

variable {n : ℕ}

@[expose] noncomputable def prAB (a b : Fin n ⊕ Fin n → GaloisField 2 1) :
    (Fin n ⊕ Fin n → GaloisField 2 1) →+ (Fin n ⊕ Fin n → GaloisField 2 1) :=
  AddMonoidHom.mk' (fun z => z + spForm b z • a + spForm a z • b) fun z z' => by
    simp only [spForm_add_right, add_smul]
    abel

theorem prAB_apply (a b z : Fin n ⊕ Fin n → GaloisField 2 1) :
    prAB a b z = z + spForm b z • a + spForm a z • b := rfl

theorem spForm_prAB_left {a b : Fin n ⊕ Fin n → GaloisField 2 1} (hab : spForm a b = 1)
    (z : Fin n ⊕ Fin n → GaloisField 2 1) : spForm a (prAB a b z) = 0 := by
  rw [prAB_apply, spForm_add_right, spForm_add_right, spForm_smul_right', spForm_smul_right',
    spForm_self, hab, mul_zero, add_zero, mul_one]
  exact gf2_add_self _

theorem spForm_prAB_right {a b : Fin n ⊕ Fin n → GaloisField 2 1} (hab : spForm a b = 1)
    (z : Fin n ⊕ Fin n → GaloisField 2 1) : spForm b (prAB a b z) = 0 := by
  rw [prAB_apply, spForm_add_right, spForm_add_right, spForm_smul_right', spForm_smul_right',
    spForm_self, spForm_comm a b, hab, mul_zero, add_zero]
  ring

theorem prAB_smul_a {a b : Fin n ⊕ Fin n → GaloisField 2 1} (hab : spForm a b = 1)
    (k : GaloisField 2 1) : prAB a b (k • a) = 0 := by
  rw [prAB_apply, spForm_smul_right', spForm_smul_right', spForm_self, spForm_comm a b, hab]
  module

theorem prAB_of_perp {a b e : Fin n ⊕ Fin n → GaloisField 2 1} (hae : spForm a e = 0)
    (hbe : spForm b e = 0) : prAB a b e = e := by
  rw [prAB_apply, hae, hbe, zero_smul, zero_smul, add_zero, add_zero]

theorem prAB_idem {a b : Fin n ⊕ Fin n → GaloisField 2 1} (hab : spForm a b = 1)
    (z : Fin n ⊕ Fin n → GaloisField 2 1) : prAB a b (prAB a b z) = prAB a b z :=
  prAB_of_perp (spForm_prAB_left hab z) (spForm_prAB_right hab z)

theorem eq_prAB_add {a b z : Fin n ⊕ Fin n → GaloisField 2 1} (hae : spForm a z = 0) :
    z = prAB a b z + spForm b z • a := by
  rw [prAB_apply, hae, zero_smul, add_zero, add_assoc, ← add_smul, gf2_add_self, zero_smul,
    add_zero]

theorem prAB_trans {a b y : Fin n ⊕ Fin n → GaloisField 2 1} (hay : spForm a y = 0)
    (hby : spForm b y = 0) (z : Fin n ⊕ Fin n → GaloisField 2 1) :
    prAB a b (z + spForm y z • y) = prAB a b z + spForm y (prAB a b z) • y := by
  have hya : spForm y a = 0 := spForm_eq_zero_comm hay
  have hyb : spForm y b = 0 := spForm_eq_zero_comm hby
  simp only [prAB_apply, spForm_add_right, spForm_smul_right', hay, hby, hya, hyb, mul_zero,
    add_zero]
  abel

end Proj

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

section Cfg

variable {n : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem psi_mem_P_iff (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    (v : Fin n ⊕ Fin n → GaloisField 2 1) : ψG v ∈ P ↔ spForm a v = 0 :=
  (h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1 v

omit [Finite G] in
theorem psi_mem_W (v : Fin n ⊕ Fin n → GaloisField 2 1) : ψG v ∈ wOf V H :=
  (Additive.toMul (ψ v)).2

theorem P_le_xOf (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T) : P ≤ xOf V H := by
  have hX :=
    (h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).2.2.1
  rw [hX]
  exact cfg.hyp.setup.mc.toMinCex.PleH

theorem psi_smul_a_mem_VW (cfg : GCfg M V Q P H Φ ψ a T) (k : GaloisField 2 1) :
    ψG (k • a) ∈ V ⊓ wOf V H := by
  rcases twl_gf2 k with rfl | rfl
  · rw [zero_smul, psi_zero]
    exact Subgroup.one_mem _
  · rw [one_smul]
    exact (aG_mem_VW cfg).1

theorem mem_VW_of_toVec (cfg : GCfg M V Q P H Φ ψ a T) {w : G} (hw : w ∈ wOf V H)
    {k : GaloisField 2 1} (hk : toVec ψ w = k • a) : w ∈ V ⊓ wOf V H := by
  rw [← psi_toVec (ψ := ψ) hw, hk]
  exact psi_smul_a_mem_VW cfg k

theorem exists_toVec_eq_smul (cfg : GCfg M V Q P H Φ ψ a T) {w : G} (hw : w ∈ V ⊓ wOf V H) :
    ∃ k : GaloisField 2 1, toVec ψ w = k • a := by
  rcases toVec_mem_VW cfg hw with h | h
  · exact ⟨0, by rw [h, zero_smul]⟩
  · exact ⟨1, by rw [h, one_smul]⟩

theorem comm_psi_mem_PW (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : spForm a b = 1) {p : G} (hp : p ∈ P) :
    ⁅p, ψG b⁆ ∈ P ⊓ wOf V H := by
  obtain ⟨g, -, hpX, -, u, hu, c, -, hcomm⟩ := comm_psi_eq h11a cfg hb hp
  rw [hcomm]
  refine Subgroup.mem_inf.mpr ⟨(psi_mem_P_iff h11a cfg _).mpr ?_, psi_mem_W _⟩
  rw [spForm_add_right, spForm_smul_right', spForm_self, hu, mul_zero, add_zero]

theorem comm_mem_PW_of_mem_Q (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T) {c : G}
    (hcQ : c ∈ Q) (hcX : ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) {p : G} (hp : p ∈ P) :
    ⁅p, c⁆ ∈ P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hcP : c * p⁻¹ * c⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P (mem_M_of_mem_Q cfg hcQ)) p⁻¹).mp
      (P.inv_mem hp)
  refine Subgroup.mem_inf.mpr ⟨?_, hcX p (P_le_xOf h11a cfg hp)⟩
  have e : ⁅p, c⁆ = p * (c * p⁻¹ * c⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact P.mul_mem hp hcP

theorem toVec_comm_mul (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) {p p' z : G}
    (hp : p ∈ P) (hz' : ⁅p', z⁆ ∈ P ⊓ wOf V H) (hz : ⁅p, z⁆ ∈ wOf V H) :
    ∃ k : GaloisField 2 1, toVec ψ ⁅p * p', z⁆ = toVec ψ ⁅p, z⁆ + toVec ψ ⁅p', z⁆ + k • a := by
  obtain ⟨r, hr, e⟩ := comm_mul_eq h11b cfg hp hz' hz
  obtain ⟨k, hk⟩ := exists_toVec_eq_smul cfg hr
  refine ⟨k, ?_⟩
  have hz'W := (Subgroup.mem_inf.mp hz').2
  rw [e, toVec_mul ((wOf V H).mul_mem hz'W hz) (Subgroup.mem_inf.mp hr).2, toVec_mul hz'W hz, hk,
    add_comm (toVec ψ ⁅p', z⁆)]

theorem comm_mem_VW_of_comm_psi_mem (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (cfg : GCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : spForm a b = 1) {c : G} (hcQ : c ∈ Q) (hcW : ∀ w ∈ wOf V H, c * w = w * c)
    {p : G} (hp : p ∈ P) (h : ⁅p, ψG b⁆ ∈ V ⊓ wOf V H) : ⁅p, c⁆ ∈ V ⊓ wOf V H := by
  obtain ⟨y, hyV, hyp⟩ := exists_V_mul_of_comm_psi_mem h11a cfg hb hp h
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ wOf V H, p = y * w :=
    ⟨y⁻¹ * p, (Subgroup.mem_inf.mp hyp).2, by group⟩
  have hwc : w * c * w⁻¹ = c := by
    rw [← hcW w hw, mul_inv_cancel_right]
  have e : ⁅y * w, c⁆ = ⁅c, y⁆⁻¹ := by
    rw [commutatorElement_inv]
    calc ⁅y * w, c⁆ = y * (w * c * w⁻¹) * y⁻¹ * c⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅y, c⁆ := by rw [hwc, commutatorElement_def]
  rw [e]
  exact (V ⊓ wOf V H).inv_mem (comm_mem_VW_of_mem_M h11b cfg (mem_M_of_mem_Q cfg hcQ) hyV)

theorem exists_mem_P_toVec_comm (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : spForm a b = 1)
    {e : Fin n ⊕ Fin n → GaloisField 2 1} (he : spForm a e = 0) :
    ∃ p ∈ P, ∃ k : GaloisField 2 1, toVec ψ ⁅p, ψG b⁆ = e + k • a := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨-, hRbar, -, -⟩ :=
    h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  have hgR : Φ (spTau a e 0 he) ∈ Rbar V H P := by
    rw [hRbar]
    exact Subgroup.mem_map.mpr ⟨_, spTau_mem a e 0 he, rfl⟩
  obtain ⟨y, hyP, hy⟩ := mem_barOf_iff.mp (mem_Rbar.mp hgR)
  have hpX : (y : G) ∈ xOf V H := P_le_xOf h11a cfg hyP
  have hxy : xToXbar hVH ⟨y, hpX⟩ = Φ (spTau a e 0 he) := by
    apply Subtype.ext
    rw [coe_xToXbar, ← hy]
    rfl
  obtain ⟨g, -, hpX', hgΦ, u, -, c, hgu, hcomm⟩ := comm_psi_eq h11a cfg hb hyP
  have hg : g = spTau a e 0 he := by
    rw [← hgΦ, show xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨(y : G), hpX'⟩ =
      Φ (spTau a e 0 he) from hxy, MulEquiv.symm_apply_apply]
  refine ⟨y, hyP, spForm e b, ?_⟩
  rw [hcomm, toVec_psi]
  have h1 := hgu b
  simp only [hg, spTau_mulVec, hb, one_smul, zero_mul, zero_smul, add_zero, mul_one] at h1
  linear_combination (norm := module) h1.symm

theorem exists_trans_elt (cfg : GCfg M V Q P H Φ ψ a T) {y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hay : spForm a y = 0) (hy0 : y ≠ 0) :
    ∃ x ∈ M, x ∈ xOf V H ∧ ∀ v, x * ψG v * x⁻¹ = ψG (v + spForm y v • y) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hy1 : ψG y ≠ 1 := by
    intro h
    exact hy0 (psi_injective (h.trans psi_zero.symm))
  obtain ⟨h, hh⟩ := exists_conj_aG_eq cfg (psi_mem_W y) hy1
  obtain ⟨v₀, hv₀, hv₀W⟩ := exists_mem_V_not_mem_W cfg
  have hact := conj_act_eq_trans cfg h hv₀ hv₀W hh.symm
  have hVX : V ≤ xOf V H := le_xOf (V_mem_omegaOf V H)
  refine ⟨(h : G) * v₀ * (h : G)⁻¹, ?_, ?_, hact⟩
  · obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
    apply hc.mem_M_of_commute (Subgroup.mem_inf.mp haK).1 haG1
    have h2 := hact a
    rw [spForm_eq_zero_comm hay, zero_smul, add_zero] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  · exact (xOf V H).mul_mem ((xOf V H).mul_mem h.2 (hVX hv₀)) ((xOf V H).inv_mem h.2)

theorem toVec_comm_conj_psi {y b : Fin n ⊕ Fin n → GaloisField 2 1} {x : G}
    (hx : ∀ v, x * ψG v * x⁻¹ = ψG (v + spForm y v • y)) (hyb : spForm y b = 0)
    {p : G} (hpb : ⁅p, ψG b⁆ ∈ wOf V H) :
    toVec ψ ⁅x * p * x⁻¹, ψG b⁆ = toVec ψ ⁅p, ψG b⁆ + spForm y (toVec ψ ⁅p, ψG b⁆) • y := by
  have hxb : x * ψG b * x⁻¹ = ψG b := by
    rw [hx b, hyb, zero_smul, add_zero]
  have e : ⁅x * p * x⁻¹, ψG b⁆ = x * ⁅p, ψG b⁆ * x⁻¹ := by
    conv_lhs => rw [← hxb]
    simp only [commutatorElement_def]
    group
  have e' : x * ⁅p, ψG b⁆ * x⁻¹ =
      ψG (toVec ψ ⁅p, ψG b⁆ + spForm y (toVec ψ ⁅p, ψG b⁆) • y) := by
    rw [← hx, psi_toVec hpb]
  rw [e, e', toVec_psi]

theorem toVec_comm_conj_of_mem_PW (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {y : Fin n ⊕ Fin n → GaloisField 2 1} {x c w₁ : G} (hxM : x ∈ M)
    (hx : ∀ v, x * ψG v * x⁻¹ = ψG (v + spForm y v • y))
    (hw : x⁻¹ * c * x = w₁ * c) (hw₁ : w₁ ∈ P ⊓ wOf V H) {p : G} (hp : p ∈ P)
    (hpc : ⁅p, c⁆ ∈ wOf V H) :
    ∃ k : GaloisField 2 1, toVec ψ ⁅x * p * x⁻¹, c⁆ =
      toVec ψ ⁅p, c⁆ + spForm y (toVec ψ ⁅p, c⁆) • y + k • a := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨hcomm', -, -⟩ := h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  have hw₁P := (Subgroup.mem_inf.mp hw₁).1
  have hw₁W := (Subgroup.mem_inf.mp hw₁).2
  have hr : ⁅p, w₁⁆ ∈ V ⊓ wOf V H := by
    rw [← hcomm']
    exact Subgroup.commutator_mem_commutator hp hw₁P
  have hrW := (Subgroup.mem_inf.mp hr).2
  have hWab := (MinCex.wOf_isElemAbelian hc).1
  have hcommW : ∀ u ∈ wOf V H, ∀ v ∈ wOf V H, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hWab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hpN : p * w₁ * p⁻¹ ∈ wOf V H :=
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hc.PleH hp)) w₁).mp hw₁W
  have e1 : ⁅x * p * x⁻¹, c⁆ = x * (p * w₁ * p⁻¹ * ⁅p, c⁆ * w₁⁻¹) * x⁻¹ := by
    have e0 : ⁅x * p * x⁻¹, c⁆ = x * p * (x⁻¹ * c * x) * p⁻¹ * (x⁻¹ * c * x)⁻¹ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e0, hw]
    simp only [commutatorElement_def]
    group
  have e2 : p * w₁ * p⁻¹ * ⁅p, c⁆ * w₁⁻¹ = ⁅p, c⁆ * ⁅p, w₁⁆ := by
    rw [hcommW _ hpN _ hpc, commutatorElement_def p w₁]
    group
  have e3 : x * ⁅p, w₁⁆ * x⁻¹ = ⁅p, w₁⁆ := conj_eq_of_mem_VW h11b cfg hxM hr
  have e4 : x * ⁅p, c⁆ * x⁻¹ = ψG (toVec ψ ⁅p, c⁆ + spForm y (toVec ψ ⁅p, c⁆) • y) := by
    rw [← hx, psi_toVec hpc]
  obtain ⟨k, hk⟩ := exists_toVec_eq_smul cfg hr
  refine ⟨k, ?_⟩
  have e5 : ⁅x * p * x⁻¹, c⁆ = (x * ⁅p, c⁆ * x⁻¹) * (x * ⁅p, w₁⁆ * x⁻¹) := by
    rw [e1, e2]
    group
  rw [e5, e3, e4, toVec_mul (psi_mem_W _) hrW, toVec_psi, hk]

theorem toVec_comm_congr (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (cfg : GCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : spForm a b = 1) {c : G} (hcQ : c ∈ Q) (hcW : ∀ w ∈ wOf V H, c * w = w * c)
    (hcX : ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) {p p' : G} (hp : p ∈ P) (hp' : p' ∈ P)
    {k : GaloisField 2 1} (hk : toVec ψ ⁅p, ψG b⁆ = toVec ψ ⁅p', ψG b⁆ + k • a) :
    ∃ k' : GaloisField 2 1, toVec ψ ⁅p, c⁆ = toVec ψ ⁅p', c⁆ + k' • a := by
  obtain ⟨q, hqP, rfl⟩ : ∃ q ∈ P, p = p' * q := ⟨p'⁻¹ * p, P.mul_mem (P.inv_mem hp') hp, by group⟩
  obtain ⟨k1, hk1⟩ := toVec_comm_mul h11b cfg hp' (comm_psi_mem_PW h11a cfg hb hqP)
    (comm_psi_mem_PW h11a cfg hb hp').2
  have hqE : toVec ψ ⁅q, ψG b⁆ = (k - k1) • a := by
    rw [hk1] at hk
    linear_combination (norm := module) hk
  have hqA := comm_mem_VW_of_comm_psi_mem h11a h11b cfg hb hcQ hcW hqP
    (mem_VW_of_toVec cfg (comm_psi_mem_PW h11a cfg hb hqP).2 hqE)
  obtain ⟨k2, hk2⟩ := exists_toVec_eq_smul cfg hqA
  obtain ⟨k3, hk3⟩ := toVec_comm_mul h11b cfg hp' (comm_mem_PW_of_mem_Q h11a cfg hcQ hcX hqP)
    (comm_mem_PW_of_mem_Q h11a cfg hcQ hcX hp').2
  exact ⟨k2 + k3, by rw [hk3, hk2]; module⟩

theorem comm_mem_VW_of_centralizes (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : spForm a b = 1) {c : G} (hcQ : c ∈ Q)
    (hcW : ∀ w ∈ wOf V H, c * w = w * c) (hcX : ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H)
    (hQ : ∀ q ∈ Q, q ∈ P ∨ c⁻¹ * q ∈ P) {p : G} (hp : p ∈ P) : ⁅p, c⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hE : ∀ p ∈ P, ⁅p, ψG b⁆ ∈ P ⊓ wOf V H := fun p hp => comm_psi_mem_PW h11a cfg hb hp
  have hD : ∀ p ∈ P, ⁅p, c⁆ ∈ P ⊓ wOf V H := fun p hp =>
    comm_mem_PW_of_mem_Q h11a cfg hcQ hcX hp
  have hperp : ∀ w ∈ P ⊓ wOf V H, spForm a (toVec ψ w) = 0 := by
    intro w hw
    rw [← psi_mem_P_iff h11a cfg, psi_toVec (Subgroup.mem_inf.mp hw).2]
    exact (Subgroup.mem_inf.mp hw).1
  have hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
    intro m hm q hq
    rw [hc.hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
  have hsurj : ∀ z, ∃ s ∈ P, ∃ k : GaloisField 2 1, toVec ψ ⁅s, ψG b⁆ = prAB a b z + k • a :=
    fun z => exists_mem_P_toVec_comm h11a cfg hb (spForm_prAB_left hb z)
  choose s hsP ks hks using hsurj
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin n ⊕ Fin n → GaloisField 2 1) →+ (Fin n ⊕ Fin n → GaloisField 2 1),
      ∀ z, φ z = prAB a b (toVec ψ ⁅s z, c⁆) := by
    refine ⟨AddMonoidHom.mk' (fun z => prAB a b (toVec ψ ⁅s z, c⁆)) fun z z' => ?_, fun z => rfl⟩
    obtain ⟨k1, hk1⟩ := toVec_comm_mul h11b cfg (hsP z) (hE (s z') (hsP z')) (hE (s z) (hsP z)).2
    obtain ⟨k2, hk2⟩ := toVec_comm_congr h11a h11b cfg hb hcQ hcW hcX (hsP (z + z'))
      (P.mul_mem (hsP z) (hsP z')) (k := ks (z + z') - ks z - ks z' - k1) (by
        linear_combination (norm := module) hks (z + z') + map_add (prAB a b) z z' - hk1 -
          hks z - hks z')
    obtain ⟨k3, hk3⟩ := toVec_comm_mul h11b cfg (hsP z) (hD (s z') (hsP z')) (hD (s z) (hsP z)).2
    show prAB a b (toVec ψ ⁅s (z + z'), c⁆) =
      prAB a b (toVec ψ ⁅s z, c⁆) + prAB a b (toVec ψ ⁅s z', c⁆)
    simp only [hk2, hk3, map_add, prAB_smul_a hb, add_zero]
  have hequiv : ∀ y e, spForm a y = 0 → spForm b y = 0 → spForm a e = 0 → spForm b e = 0 →
      ∃ k : GaloisField 2 1, φ (e + spForm y e • y) = φ e + spForm y (φ e) • y + k • a := by
    intro y e hay hby hae hbe
    refine ⟨0, ?_⟩
    rw [zero_smul, add_zero]
    by_cases hy0 : y = 0
    · subst hy0
      simp only [smul_zero, add_zero]
    obtain ⟨x, hxM, hxX, hx⟩ := exists_trans_elt cfg hay hy0
    have hw₁W : ⁅x⁻¹, c⁆ ∈ wOf V H := hcX _ ((xOf V H).inv_mem hxX)
    have hw₁Q : ⁅x⁻¹, c⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (hQn _ (M.inv_mem hxM) c hcQ) (Q.inv_mem hcQ)
    have hw₁P : ⁅x⁻¹, c⁆ ∈ P := mem_P_of_mem_W_Q h11a h11b h11c cfg hcQ hcW hcX hQ hw₁W hw₁Q
    have hw : x⁻¹ * c * x = ⁅x⁻¹, c⁆ * c := by
      simp only [commutatorElement_def]
      group
    have hxp : x * s e * x⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hxM) (s e)).mp (hsP e)
    have hEx := toVec_comm_conj_psi (ψ := ψ) hx (spForm_eq_zero_comm hby) (hE (s e) (hsP e)).2
    obtain ⟨kD, hDx⟩ := toVec_comm_conj_of_mem_PW h11b cfg hxM hx hw
      (Subgroup.mem_inf.mpr ⟨hw₁P, hw₁W⟩) (hsP e) (hD (s e) (hsP e)).2
    have hte : prAB a b (e + spForm y e • y) = e + spForm y e • y := by
      rw [prAB_trans hay hby, prAB_of_perp hae hbe]
    have hpe : prAB a b e = e := prAB_of_perp hae hbe
    have hya : spForm y (ks e • a) = 0 := by
      rw [spForm_smul_right', spForm_eq_zero_comm hay, mul_zero]
    have hs1 := hks (e + spForm y e • y)
    rw [hte] at hs1
    have hs2 := hks e
    rw [hpe] at hs2
    have hEx' : toVec ψ ⁅x * s e * x⁻¹, ψG b⁆ = e + ks e • a + spForm y e • y := by
      rw [hEx, hs2, spForm_add_right, hya, add_zero]
    obtain ⟨k', hk'⟩ := toVec_comm_congr h11a h11b cfg hb hcQ hcW hcX (hsP (e + spForm y e • y))
      hxp (k := ks (e + spForm y e • y) - ks e) (by
        linear_combination (norm := module) hs1 - hEx')
    rw [hφ, hφ, hk', hDx, map_add, prAB_smul_a hb, add_zero, map_add, prAB_smul_a hb, add_zero,
      prAB_trans hay hby]
  obtain ⟨μ, hμ⟩ := eq_smul_of_trans_equivariant cfg.two_le hb φ hequiv
  have hDE : ∀ p ∈ P, ∃ k : GaloisField 2 1,
      toVec ψ ⁅p, c⁆ = μ • toVec ψ ⁅p, ψG b⁆ + k • a := by
    intro p hp
    have hEp : toVec ψ ⁅p, ψG b⁆ =
        prAB a b (toVec ψ ⁅p, ψG b⁆) + spForm b (toVec ψ ⁅p, ψG b⁆) • a :=
      eq_prAB_add (hperp _ (hE p hp))
    have hse := hks (prAB a b (toVec ψ ⁅p, ψG b⁆))
    rw [prAB_idem hb] at hse
    obtain ⟨k1, hk1⟩ := toVec_comm_congr h11a h11b cfg hb hcQ hcW hcX hp (hsP _)
      (k := spForm b (toVec ψ ⁅p, ψG b⁆) - ks (prAB a b (toVec ψ ⁅p, ψG b⁆))) (by
        linear_combination (norm := module) hEp - hse)
    obtain ⟨k2, hk2⟩ := hμ (prAB a b (toVec ψ ⁅p, ψG b⁆)) (spForm_prAB_left hb _)
      (spForm_prAB_right hb _)
    rw [hφ] at hk2
    have hDs := eq_prAB_add (b := b) (hperp _ (hD (s (prAB a b (toVec ψ ⁅p, ψG b⁆))) (hsP _)))
    exact ⟨k1 + k2 + spForm b (toVec ψ ⁅s (prAB a b (toVec ψ ⁅p, ψG b⁆)), c⁆) -
      μ * spForm b (toVec ψ ⁅p, ψG b⁆), by
        linear_combination (norm := module) hk1 + hDs + hk2 - μ • hEp⟩
  rcases twl_gf2 μ with hμ0 | hμ1
  · obtain ⟨k, hk⟩ := hDE p hp
    rw [hμ0, zero_smul, zero_add] at hk
    exact mem_VW_of_toVec cfg (hD p hp).2 hk
  · exfalso
    have hbW : ψG b ∈ wOf V H := psi_mem_W b
    have huM : c * ψG b ∈ M := M.mul_mem (mem_M_of_mem_Q cfg hcQ) (wOf_le_M cfg hbW)
    have huP : ∀ p ∈ P, ⁅c * ψG b, p⁆ ∈ V ⊓ wOf V H := by
      intro p hp
      have e1 : ⁅p, c * ψG b⁆ = ⁅p, c⁆ * ⁅p, ψG b⁆ := by
        have hc' := hcW _ (hE p hp).2
        calc ⁅p, c * ψG b⁆ = ⁅p, c⁆ * (c * ⁅p, ψG b⁆ * c⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅p, c⁆ * ⁅p, ψG b⁆ := by rw [hc', mul_inv_cancel_right]
      obtain ⟨k, hk⟩ := hDE p hp
      rw [hμ1, one_smul] at hk
      have hmem : ⁅p, c * ψG b⁆ ∈ V ⊓ wOf V H := by
        refine mem_VW_of_toVec cfg (k := k) ?_ ?_
        · rw [e1]
          exact (wOf V H).mul_mem (hD p hp).2 (hE p hp).2
        · rw [e1, toVec_mul (hD p hp).2 (hE p hp).2, hk, add_comm (toVec ψ ⁅p, ψG b⁆) (k • a),
            add_assoc, gf2_vec_add_self, add_zero]
      rw [← commutatorElement_inv]
      exact (V ⊓ wOf V H).inv_mem hmem
    have huQ := mem_Q_of_comm_mem_VW h11b cfg huM huP
    have hbQ : ψG b ∈ Q := by
      have e : ψG b = c⁻¹ * (c * ψG b) := by group
      rw [e]
      exact Q.mul_mem (Q.inv_mem hcQ) huQ
    have hbP := mem_P_of_mem_W_Q h11a h11b h11c cfg hcQ hcW hcX hQ hbW hbQ
    rw [psi_mem_P_iff h11a cfg, hb] at hbP
    exact one_ne_zero hbP

end Cfg

end CFSG.RankThree.GF2n.Tim79a.Gamma
