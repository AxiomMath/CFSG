module

public import CFSG.RankThree.PartTwo.Sec13.Item138ProofMain
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item138Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix (GeneralLinearGroup ProjGenLinGroup)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits slPi glPi PiField ModThree qSubPi)

section Index

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_mk_eq_mk_mul_pow (hK : PiField π p f K) {δ₀ : GL (Fin 3) K}
    (hδ₀ : δ₀ ∈ glPi π 3 (p ^ f) K)
    (hδ₀P : ProjGenLinGroup.mk δ₀ ∉ projImage (slPi π 3 (p ^ f) K))
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) :
    ∃ s ∈ slPi π 3 (p ^ f) K, ∃ k : ℕ,
      ProjGenLinGroup.mk g = ProjGenLinGroup.mk s * ProjGenLinGroup.mk δ₀ ^ k := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  set T := rootsOfUnity (qSubPi π (p ^ f)) K with hT
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := T)
  have hdet : ∀ {y : GL (Fin 3) K}, y ∈ glPi π 3 (p ^ f) K → GeneralLinearGroup.det y ∈ T :=
    fun hy => Sec4.det_mem_rootsOfUnity hK hy
  have hdsc : ∀ ℓ : Kˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ℓ) = ℓ ^ 3 :=
    fun ℓ => Units.ext (by rw [GeneralLinearGroup.val_det_apply, Sec4.det_scalar,
      Units.val_pow_eq_pow_val])
  have hpowζ : ∀ t : T, ∃ m : ℤ, ζ ^ m = t := fun t => Subgroup.mem_zpowers_iff.mp (hζ t)
  obtain ⟨m₀, hm₀⟩ := hpowζ ⟨_, hdet hδ₀⟩
  obtain ⟨m, hm⟩ := hpowζ ⟨_, hdet hg⟩
  have hcube : ∀ {y : GL (Fin 3) K}, y ∈ glPi π 3 (p ^ f) K → ∀ ℓ : T,
      ((ℓ : Kˣ) ^ 3 = GeneralLinearGroup.det y) →
        (GeneralLinearGroup.scalar (Fin 3) (ℓ : Kˣ))⁻¹ * y ∈ slPi π 3 (p ^ f) K := by
    intro y hy ℓ hℓ
    rw [Sec4.mem_slPi_iff hπ]
    refine ⟨mul_mem (inv_mem ((Sec4.scalar_mem_glPi_iff hK _).mpr ℓ.2)) hy, ?_⟩
    have h1 : GeneralLinearGroup.det ((GeneralLinearGroup.scalar (Fin 3) (ℓ : Kˣ))⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hdsc, hℓ, inv_mul_cancel]
    have h2 := congrArg Units.val h1
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  have hm₀3 : ¬ (3 : ℤ) ∣ m₀ := by
    rintro ⟨a, ha⟩
    apply hδ₀P
    refine ⟨_, hcube hδ₀ (ζ ^ a) ?_, ?_⟩
    · have e1 : (ζ ^ a) ^ 3 = ζ ^ m₀ := by
        rw [ha, ← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      have e2 := congrArg (fun t : T => (t : Kˣ)) (e1.trans hm₀)
      simpa using e2
    · rw [map_mul, map_inv, Sec13.mk_scalar, inv_one, one_mul]
  obtain ⟨k, j, hkj⟩ : ∃ k : ℕ, ∃ j : ℤ, m = k * m₀ + 3 * j := by
    have h1 : m₀ % 3 = 1 ∨ m₀ % 3 = 2 := by omega
    have h2 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · exact ⟨0, m / 3, by omega⟩
    · exact ⟨1, (m - m₀) / 3, by omega⟩
    · exact ⟨2, (m - 2 * m₀) / 3, by omega⟩
    · exact ⟨0, m / 3, by omega⟩
    · exact ⟨2, (m - 2 * m₀) / 3, by omega⟩
    · exact ⟨1, (m - m₀) / 3, by omega⟩
  have hgk : g * (δ₀ ^ k)⁻¹ ∈ glPi π 3 (p ^ f) K := mul_mem hg (inv_mem (pow_mem hδ₀ k))
  have hdetgk : ((ζ ^ j : T) : Kˣ) ^ 3 = GeneralLinearGroup.det (g * (δ₀ ^ k)⁻¹) := by
    have e1 := congrArg (fun t : T => (t : Kˣ)) hm
    have e0 := congrArg (fun t : T => (t : Kˣ)) hm₀
    simp only at e1 e0
    rw [map_mul, map_inv, map_pow, ← e1, ← e0]
    simp only [SubgroupClass.coe_zpow]
    rw [hkj, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast
    ring
  refine ⟨_, hcube hgk (ζ ^ j) hdetgk, k, ?_⟩
  rw [map_mul, map_inv, Sec13.mk_scalar, inv_one, one_mul, map_mul, map_inv, map_pow,
    inv_mul_cancel_right]

end Index

section Inner

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {c : G}

theorem eq_of_conj_eq {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) {a b : M}
    (h : ∀ z : M, a * z * a⁻¹ = b * z * b⁻¹) : a = b := by
  have hc : b⁻¹ * a ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := h z
    calc z * (b⁻¹ * a) = b⁻¹ * (b * z * b⁻¹) * b * b⁻¹ * a := by group
      _ = b⁻¹ * (a * z * a⁻¹) * a := by rw [← h1]; group
      _ = b⁻¹ * a * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem exists_eq_zpow_mul_of_inner (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hEC : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G))
    {y : G} (hy : y ∈ E) {w : L ⧸ aschbacherSolvableCore 3 L}
    (hyw : ∀ z, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z = w * z * w⁻¹) :
    ∃ n : L, (n : G) ∈ E ∧ (n : L ⧸ aschbacherSolvableCore 3 L) = w ∧
      ∃ k : ℤ, y = c ^ k * n := by
  set σ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hσ
  have hσapp : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)),
      σ ⟨x, hx⟩ = Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) := fun _ _ => rfl
  have hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hwfix : ∀ (x : G) (hx : x ∈ E),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) w = w := by
    intro x hx
    set τx := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) with hτx
    have hcomm : ∀ z, τx (w * z * w⁻¹) = w * τx z * w⁻¹ := by
      intro z
      have h1 : σ ⟨x, hEN hx⟩ * σ ⟨y, hEN hy⟩ = σ ⟨y, hEN hy⟩ * σ ⟨x, hEN hx⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hEc x hx y hy)
      have h2 := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ z) h1
      simp only [MulAut.mul_apply] at h2
      rw [hσapp, hσapp, hyw, hyw] at h2
      exact h2
    refine eq_of_conj_eq hZ fun z' => ?_
    obtain ⟨z, rfl⟩ := τx.surjective z'
    rw [← hcomm z, map_mul, map_mul, map_inv]
  have hy3 : y ^ 3 = 1 := hE3.2 y hy
  have hw3 : w ^ 3 = 1 := by
    have h1 : σ ⟨y, hEN hy⟩ ^ 3 = 1 := by
      rw [← map_pow, show (⟨y, hEN hy⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3), map_one]
    have h2 : ∀ z, w ^ 3 * z * (w ^ 3)⁻¹ = 1 * z * 1⁻¹ := by
      intro z
      have h3 := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ z) h1
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h3
      rw [hσapp, hyw, hyw, hyw] at h3
      calc w ^ 3 * z * (w ^ 3)⁻¹ = w * (w * (w * z * w⁻¹) * w⁻¹) * w⁻¹ := by
            rw [pow_three]; group
        _ = z := h3
        _ = 1 * z * 1⁻¹ := by group
    exact eq_of_conj_eq hZ h2
  obtain ⟨n, hnE, hnw⟩ := exists_mem_of_fixed hEN hE3 hEmax hw3 hwfix
  refine ⟨n, hnE, hnw, ?_⟩
  have hsec : y * (n : G)⁻¹ ∈ Late.sectionCentralizer E L
      ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨mul_mem hy (inv_mem hnE), fun l hl => ?_⟩
    set l' : L := n⁻¹ * ⟨l, hl⟩ * n with hl'
    have h1 := hyw (l' : L ⧸ aschbacherSolvableCore 3 L)
    rw [Sec4.thetaQuotMulAut_mk, ← hnw, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hl', show n * (n⁻¹ * ⟨l, hl⟩ * n) * n⁻¹ = ⟨l, hl⟩ by group,
      mk_eq_mk_iff, Sec4.normalizerMonoidHom_apply_coe] at h1
    have h2 := mul_inv_mem_theta_of_inv_mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hEN hy) _).mp (n⁻¹ * ⟨l, hl⟩ * n).2) h1
    have h3 := inv_mem h2
    rw [show ((⟨l, hl⟩ : L) : G) * (y * ((n⁻¹ * ⟨l, hl⟩ * n : L) : G) * y⁻¹)⁻¹ =
        (y * (n : G)⁻¹ * l * (y * (n : G)⁻¹)⁻¹ * l⁻¹)⁻¹ by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group, inv_inv] at h3
    exact h3
  rw [hEC] at hsec
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsec
  refine ⟨k, ?_⟩
  rw [hk]
  group

end Inner

section Construction

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}

local notation "NC" => Subgroup.normalizer (Subgroup.zpowers c : Set G)
set_option quotPrecheck false in
local notation "θC" => aschbacherSolvableCore 3 ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))
set_option quotPrecheck false in
local notation "qC" => QuotientGroup.mk' (aschbacherSolvableCore 3
  ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)))

set_option maxHeartbeats 400000 in
theorem isZ3PGLThreePi_of_not_le (hH : Hyp138 A c L E)
    (hout : ¬ E ≤ Subgroup.zpowers c ⊔ L) : Sec8.IsZ3PGLThreePi (lBarA c L E) := by
  obtain ⟨h, -, hcE, hE3, -, hEN, hEC, hST, hC⟩ := hH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := by
    rcases hST with hS | hT
    · exact hS.1
    · exact hT.1
  have hEF : E ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hEE
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hEF.2.1
  obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hτD, -⟩ := hC
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hL := h.mem_thetaComponentsAt
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hK hq e
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv e (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hEc : ∀ x ∈ E, x * c = c * x := fun x hx =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx))
  obtain ⟨x₀, hx₀E, hx₀⟩ := Set.not_subset.mp hout
  obtain ⟨δ₀, hδ₀D, hδ₀⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x₀, hEN hx₀E, hx₀E, rfl⟩)
  have hδ₀H : δ₀ ∈ glPi π 3 (p ^ f) K := hD.1 hδ₀D
  have hδ₀P : ProjGenLinGroup.mk δ₀ ∉ projImage (slPi π 3 (p ^ f) K) := by
    intro hmem
    set w : L ⧸ aschbacherSolvableCore 3 L := e.symm ⟨_, hmem⟩ with hw
    have hx₀w : ∀ z, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x₀, hEN hx₀E⟩) z =
        w * z * w⁻¹ := by
      intro z
      apply e.injective
      apply Subtype.ext
      rw [hδ₀ z, map_mul, map_mul, map_inv, hw, MulEquiv.apply_symm_apply]
      rfl
    obtain ⟨n, -, -, k, hk⟩ := exists_eq_zpow_mul_of_inner hEN hE3 hEmax hZ hEC hx₀E hx₀w
    exact hx₀ (hk ▸ mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
      (Subgroup.mem_sup_right n.2))
  obtain ⟨η, hη⟩ := exists_lBarEquiv hL
  have hLN : L ≤ NC := le_normalizer_zpowers_of_mem hL
  have hη' : ∀ (l : G) (hl : l ∈ L),
      ((η ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) : Sec12.lBar c L) : ↥NC ⧸ θC) =
        qC ⟨l, hLN hl⟩ := fun l hl => hη ⟨l, hl⟩
  have hxlX : ∀ {l : G} (hl : l ∈ L), qC ⟨l, hLN hl⟩ ∈ lBarA c L E := fun hl =>
    lBar_le_lBarA ⟨⟨_, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hxyX : ∀ {y : G} (hy : y ∈ E), qC ⟨y, hEH hy⟩ ∈ lBarA c L E := fun hy =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hy))
  have hconjE : ∀ {y : G} (hy : y ∈ E) (z : L ⧸ aschbacherSolvableCore 3 L),
      qC ⟨y, hEH hy⟩ * ((η z : Sec12.lBar c L) : ↥NC ⧸ θC) * (qC ⟨y, hEH hy⟩)⁻¹ =
        ((η (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z) : Sec12.lBar c L) :
          ↥NC ⧸ θC) := by
    intro y hy z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [Sec4.thetaQuotMulAut_mk, hη, hη, ← map_mul, ← map_inv, ← map_mul]
      rfl
  have hXN : lBarA c L E ≤ Subgroup.normalizer ((Sec12.lBar c L : Subgroup (↥NC ⧸ θC)) :
      Set (↥NC ⧸ θC)) := by
    intro x hx
    apply mem_normalizer_of_map_le
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, y, hy, rfl⟩ := exists_mk_mul_of_mem_lBarA hL hEN hEH hx
    change qC ⟨l, _⟩ * qC ⟨y, _⟩ * z * (qC ⟨l, _⟩ * qC ⟨y, _⟩)⁻¹ ∈ Sec12.lBar c L
    have hz' : z = ((η (η.symm ⟨z, hz⟩) : Sec12.lBar c L) : ↥NC ⧸ θC) := by
      rw [MulEquiv.apply_symm_apply]
    rw [show qC ⟨l, le_normalizer_zpowers_of_mem hL hl⟩ * qC ⟨y, hEH hy⟩ * z *
        (qC ⟨l, le_normalizer_zpowers_of_mem hL hl⟩ * qC ⟨y, hEH hy⟩)⁻¹ =
        qC ⟨l, hLN hl⟩ * (qC ⟨y, hEH hy⟩ * z * (qC ⟨y, hEH hy⟩)⁻¹) * (qC ⟨l, hLN hl⟩)⁻¹ by
      group, hz', hconjE hy]
    have hlb : qC ⟨l, hLN hl⟩ ∈ Sec12.lBar c L := ⟨⟨_, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    exact mul_mem (mul_mem hlb (η _).2) (inv_mem hlb)
  set ρ₀ : lBarA c L E →* MulAut (Sec12.lBar c L) :=
    (Sec12.lBar c L).normalizerMonoidHom.comp (Subgroup.inclusion hXN) with hρ₀
  set ε : Sec12.lBar c L ≃* projImage (slPi π 3 (p ^ f) K) := η.symm.trans e with hε
  set ρ : lBarA c L E →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr ε).toMonoidHom.comp ρ₀ with hρ
  have hPQ' : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hPQ : projImage (glPi π 3 (p ^ f) K) ≤ Subgroup.normalizer
      ((projImage (slPi π 3 (p ^ f) K) : Subgroup (ProjGenLinGroup (Fin 3) K)) :
        Set (ProjGenLinGroup (Fin 3) K)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨g * s * g⁻¹, Sec4.conj_mem_slPi hπ hg hs, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨s, hs, hsx⟩
      refine ⟨g⁻¹ * s * g, ?_, ?_⟩
      · have := Sec4.conj_mem_slPi hπ (inv_mem hg) hs
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hsx]
        group
  set κ : projImage (glPi π 3 (p ^ f) K) →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (projImage (slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp (Subgroup.inclusion hPQ) with hκdef
  have hκapp : ∀ (g : projImage (glPi π 3 (p ^ f) K)) (x : projImage (slPi π 3 (p ^ f) K)),
      ((κ g x : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        (g : ProjGenLinGroup (Fin 3) K) * x * (g : ProjGenLinGroup (Fin 3) K)⁻¹ :=
    fun _ _ => rfl
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨_, ⟨g, hg, rfl⟩⟩ h1
    have hcomm : ∀ s ∈ slPi π 3 (p ^ f) K,
        ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
          ProjGenLinGroup.mk s * ProjGenLinGroup.mk g := by
      intro s hs
      have h2 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
        ((σ ⟨_, Subgroup.mem_map_of_mem _ hs⟩ : projImage (slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K)) h1
      simp only [hκapp, MulAut.one_apply] at h2
      calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
          ProjGenLinGroup.mk g * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk g)⁻¹ *
            ProjGenLinGroup.mk g := by group
        _ = ProjGenLinGroup.mk s * ProjGenLinGroup.mk g := by rw [h2]
    have hsc := mem_statedScalars_of_commute_mk hK hq hq2 hcomm
    exact Subtype.ext (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hsc)
  have hρ₀app : ∀ (x : lBarA c L E) (z : Sec12.lBar c L),
      ((ρ₀ x z : Sec12.lBar c L) : ↥NC ⧸ θC) = (x : ↥NC ⧸ θC) * z * (x : ↥NC ⧸ θC)⁻¹ :=
    fun _ _ => rfl
  have hρapp : ∀ (x : lBarA c L E) (w : projImage (slPi π 3 (p ^ f) K)),
      ρ x w = e (η.symm (ρ₀ x (η (e.symm w)))) := fun _ _ => rfl
  have hρl : ∀ (l : G) (hl : l ∈ L), ρ ⟨_, hxlX hl⟩ =
      κ ⟨_, hPQ' (e ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)).2⟩ := by
    intro l hl
    ext w
    rw [hρapp, hκapp]
    have h1 : ρ₀ ⟨_, hxlX hl⟩ (η (e.symm w)) =
        η (((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * e.symm w *
          ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹) := by
      apply Subtype.ext
      rw [hρ₀app, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hη' l hl]
    rw [h1, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hρy : ∀ (y : G) (hy : y ∈ E) (δ : GL (Fin 3) K)
      (hδ : ∀ z, ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk δ * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk δ)⁻¹)
      (hδQ : ProjGenLinGroup.mk δ ∈ projImage (glPi π 3 (p ^ f) K)),
      ρ ⟨_, hxyX hy⟩ = κ ⟨_, hδQ⟩ := by
    intro y hy δ hδ hδQ
    ext w
    rw [hρapp, hκapp]
    have h1 : ρ₀ ⟨_, hxyX hy⟩ (η (e.symm w)) =
        η (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) (e.symm w)) := by
      apply Subtype.ext
      rw [hρ₀app]
      exact hconjE hy _
    rw [h1, MulEquiv.symm_apply_apply, hδ, MulEquiv.apply_symm_apply]
  have hdecX : ∀ x : lBarA c L E, ∃ (l : G) (hl : l ∈ L) (y : G) (hy : y ∈ E),
      x = ⟨_, hxlX hl⟩ * ⟨_, hxyX hy⟩ := by
    rintro ⟨x, hx⟩
    obtain ⟨l, hl, y, hy, rfl⟩ := exists_mk_mul_of_mem_lBarA hL hEN hEH hx
    exact ⟨l, hl, y, hy, rfl⟩
  have hδE : ∀ (y : G) (hy : y ∈ E), ∃ δ : GL (Fin 3) K,
      ProjGenLinGroup.mk δ ∈ projImage (glPi π 3 (p ^ f) K) ∧
      ∀ z, ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk δ * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk δ)⁻¹ := by
    intro y hy
    obtain ⟨δ, hδD, hδ⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨y, hEN hy, hy, rfl⟩)
    exact ⟨δ, Subgroup.mem_map_of_mem _ (hD.1 hδD), hδ⟩
  have hρκ : ∀ x : lBarA c L E, ρ x ∈ κ.range := by
    intro x
    obtain ⟨l, hl, y, hy, rfl⟩ := hdecX x
    obtain ⟨δ, hδQ, hδ⟩ := hδE y hy
    rw [map_mul, hρl l hl, hρy y hy δ hδ hδQ, ← map_mul]
    exact ⟨_, rfl⟩
  set Ψ : lBarA c L E →* projImage (glPi π 3 (p ^ f) K) :=
    (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ρ.codRestrict κ.range hρκ) with hΨdef
  have hΨκ : ∀ x, κ (Ψ x) = ρ x := by
    intro x
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply ⟨ρ x, hρκ x⟩
    exact congrArg Subtype.val h1
  have hΨl : ∀ (l : G) (hl : l ∈ L), Ψ ⟨_, hxlX hl⟩ =
      ⟨_, hPQ' (e ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)).2⟩ :=
    fun l hl => hκ (by rw [hΨκ, hρl])
  have hΨy : ∀ (y : G) (hy : y ∈ E) (δ : GL (Fin 3) K)
      (hδ : ∀ z, ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk δ * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk δ)⁻¹)
      (hδQ : ProjGenLinGroup.mk δ ∈ projImage (glPi π 3 (p ^ f) K)),
      Ψ ⟨_, hxyX hy⟩ = ⟨_, hδQ⟩ := fun y hy δ hδ hδQ => hκ (by rw [hΨκ, hρy y hy δ hδ hδQ])
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  set cb : lBarA c L E := ⟨_, hxyX hcE⟩ with hcb
  have hτc : ∀ z, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hEN hcE⟩) z = z := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, ← hLc l l.2, mul_inv_cancel_right]
  have h1Q : ProjGenLinGroup.mk (1 : GL (Fin 3) K) ∈ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.mem_map_of_mem _ (one_mem _)
  have hΨc : Ψ cb = 1 := by
    rw [hcb, hΨy c hcE 1 (fun z => by rw [hτc, map_one, inv_one, one_mul, mul_one]) h1Q]
    exact Subtype.ext (map_one _)
  have hker : ∀ x : lBarA c L E, Ψ x = 1 → x ∈ Subgroup.zpowers cb := by
    intro x hx1
    obtain ⟨l, hl, y, hy, rfl⟩ := hdecX x
    obtain ⟨δ, hδQ, hδ⟩ := hδE y hy
    rw [map_mul, hΨl l hl, hΨy y hy δ hδ hδQ] at hx1
    have h2 : ProjGenLinGroup.mk δ = ((e (((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L))⁻¹ :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
      have h3 := congrArg Subtype.val hx1
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at h3
      rw [map_inv, Subgroup.coe_inv]
      exact eq_inv_of_mul_eq_one_right h3
    have hyw : ∀ z, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hEN hy⟩) z =
        ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹ * z *
          (((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹)⁻¹ := by
      intro z
      apply e.injective
      apply Subtype.ext
      rw [hδ z, h2]
      simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨n, -, hnw, k, hk⟩ := exists_eq_zpow_mul_of_inner hEN hE3 hEmax hZ hEC hy hyw
    have hqln : qC ⟨l * n, hLN (mul_mem hl n.2)⟩ = 1 := by
      rw [← hη' (l * n) (mul_mem hl n.2)]
      have h3 : ((⟨l * n, mul_mem hl n.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 := by
        change (((⟨l, hl⟩ : L) * n : L) : L ⧸ aschbacherSolvableCore 3 L) = 1
        rw [QuotientGroup.mk_mul, hnw, mul_inv_cancel]
      rw [h3, map_one]
      rfl
    have hyeq : (⟨y, hEH hy⟩ : NC) = ⟨c, hEH hcE⟩ ^ k * ⟨n, hLN n.2⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow]; exact hk)
    have hlc : (⟨l, hLN hl⟩ : NC) * ⟨c, hEH hcE⟩ ^ k = ⟨c, hEH hcE⟩ ^ k * ⟨l, hLN hl⟩ :=
      Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
        exact (Commute.zpow_right (show Commute l c from hLc l hl) k).eq)
    have hln' : (⟨l, hLN hl⟩ : NC) * ⟨n, hLN n.2⟩ = ⟨l * n, hLN (mul_mem hl n.2)⟩ := rfl
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, hcb]
    rw [hyeq, map_mul, map_zpow, ← mul_assoc, ← map_zpow, ← map_mul, hlc, map_mul, mul_assoc,
      ← map_mul, hln', hqln, mul_one, map_zpow]
  set xb : lBarA c L E := ⟨_, hxyX hx₀E⟩ with hxb
  have hδ₀Q : ProjGenLinGroup.mk δ₀ ∈ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.mem_map_of_mem _ hδ₀H
  have hΨx₀ : Ψ xb = ⟨_, hδ₀Q⟩ := hΨy x₀ hx₀E δ₀ hδ₀ hδ₀Q
  set Lb' : Subgroup (lBarA c L E) := (Sec12.lBar c L).subgroupOf (lBarA c L E) with hLb'
  have hLb'N : Subgroup.zpowers xb ≤ Subgroup.normalizer (Lb' : Set (lBarA c L E)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hXN xb.2) a
  set M : Subgroup (lBarA c L E) := Lb' ⊔ Subgroup.zpowers xb with hM
  have hMdec : ∀ m ∈ M, ∃ (l : G) (hl : l ∈ L) (k : ℤ), m = ⟨_, hxlX hl⟩ * xb ^ k := by
    intro m hm
    have hm' : m ∈ ((Lb' ⊔ Subgroup.zpowers xb : Subgroup (lBarA c L E)) :
        Set (lBarA c L E)) := hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Lb' (Subgroup.zpowers xb) hLb'N] at hm'
    obtain ⟨a, ha, b, hb, rfl⟩ := hm'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨n, hn, hna⟩ := Subgroup.mem_subgroupOf.mp ha
    refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hn, k, ?_⟩
    congr 1
    exact Subtype.ext hna.symm
  have hδ₀3 : ProjGenLinGroup.mk δ₀ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← map_pow,
      ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact hD.2.1 δ₀ hδ₀D
  have hxb3 : xb ^ (3 : ℤ) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, Subgroup.coe_one, hxb, ← map_zpow]
    rw [show (⟨x₀, hEH hx₀E⟩ : NC) ^ (3 : ℤ) = 1 from Subtype.ext (by
      rw [Subgroup.coe_zpow, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hE3.2 x₀ hx₀E), map_one]
  have hMinj : ∀ m ∈ M, Ψ m = 1 → m = 1 := by
    intro m hm hm1
    obtain ⟨l, hl, k, rfl⟩ := hMdec m hm
    rw [map_mul, map_zpow, hΨl l hl, hΨx₀] at hm1
    have hm2 := congrArg Subtype.val hm1
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] at hm2
    have hk3 : (3 : ℤ) ∣ k := by
      by_contra hk
      have h2 : ProjGenLinGroup.mk δ₀ ^ k ∈ projImage (slPi π 3 (p ^ f) K) := by
        rw [eq_inv_of_mul_eq_one_right hm2]
        exact inv_mem (e _).2
      apply hδ₀P
      rw [Sec4.zpow_emod_three (by exact_mod_cast hδ₀3) k] at h2
      rcases (show k % 3 = 1 ∨ k % 3 = 2 by omega) with hk' | hk'
      · rw [hk', zpow_one] at h2
        exact h2
      · rw [hk'] at h2
        have h4 : ProjGenLinGroup.mk δ₀ = (ProjGenLinGroup.mk δ₀ ^ (2 : ℤ)) ^ (2 : ℤ) *
            (ProjGenLinGroup.mk δ₀ ^ (3 : ℤ))⁻¹ := by group
        rw [h4, hδ₀3, inv_one, mul_one]
        exact zpow_mem h2 2
    obtain ⟨j, rfl⟩ := hk3
    have hxbk : xb ^ (3 * j) = 1 := by rw [zpow_mul, hxb3, one_zpow]
    have hδk : ProjGenLinGroup.mk δ₀ ^ (3 * j) = 1 := by rw [zpow_mul, hδ₀3, one_zpow]
    rw [hδk, mul_one] at hm2
    rw [hxbk, mul_one]
    have hl1 : ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
      e.injective (Subtype.ext (by rw [hm2, map_one, Subgroup.coe_one]))
    apply Subtype.ext
    change qC ⟨l, hLN hl⟩ = ((1 : lBarA c L E) : ↥NC ⧸ θC)
    rw [Subgroup.coe_one, ← hη' l hl, hl1, map_one]
    rfl
  have hMsurj : ∀ g : projImage (glPi π 3 (p ^ f) K), ∃ m ∈ M, Ψ m = g := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    obtain ⟨s, hs, k, hsk⟩ := exists_mk_eq_mk_mul_pow hK hδ₀H hδ₀P hg
    obtain ⟨l, hl⟩ :=
      QuotientGroup.mk_surjective (e.symm ⟨_, Subgroup.mem_map_of_mem ProjGenLinGroup.mk hs⟩)
    refine ⟨⟨_, hxlX l.2⟩ * xb ^ k, mul_mem (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers xb) k)), ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨⟨_, hLN l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rw [map_mul, map_pow, hΨl _ l.2, hΨx₀]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [hsk]
      congr 1
      have hl' : ((⟨(l : G), l.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
          e.symm ⟨_, Subgroup.mem_map_of_mem ProjGenLinGroup.mk hs⟩ := hl
      rw [hl', MulEquiv.apply_symm_apply]
  have hcbc : ∀ x : lBarA c L E, cb * x = x * cb := by
    intro x
    obtain ⟨l, hl, y, hy, rfl⟩ := hdecX x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hcb]
    rw [← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc c * (l * y) = c * l * y := (mul_assoc _ _ _).symm
      _ = l * c * y := by rw [hLc l hl]
      _ = l * (c * y) := mul_assoc _ _ _
      _ = l * (y * c) := by rw [hEc y hy]
      _ = l * y * c := (mul_assoc _ _ _).symm
  set Z : Subgroup (lBarA c L E) := Subgroup.zpowers cb with hZdef
  have hZcomm : ∀ z ∈ Z, ∀ x : lBarA c L E, z * x = x * z := by
    rintro _ ⟨k, rfl⟩ x
    exact (Commute.zpow_left (hcbc x) k).eq
  have hZM : ∀ z ∈ Z, z ∈ M → z = 1 := by
    rintro _ ⟨k, rfl⟩ hzM
    apply hMinj _ hzM
    change Ψ (cb ^ k) = 1
    rw [map_zpow, hΨc, one_zpow]
  have hXZM : ∀ x : lBarA c L E, ∃ z ∈ Z, ∃ m ∈ M, x = z * m := by
    intro x
    obtain ⟨m, hm, hmx⟩ := hMsurj (Ψ x)
    exact ⟨x * m⁻¹, hker _ (by rw [map_mul, map_inv, hmx, mul_inv_cancel]), m, hm, by group⟩
  set φ : Z × M →* lBarA c L E :=
    MonoidHom.noncommCoprod Z.subtype M.subtype (fun z m => hZcomm z z.2 m) with hφdef
  have hφapp : ∀ zm : Z × M, φ zm = (zm.1 : lBarA c L E) * zm.2 := fun _ => rfl
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨z, m⟩ h1
      rw [hφapp] at h1
      have hmz : (m : lBarA c L E) = (z : lBarA c L E)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hm1 : (m : lBarA c L E) = 1 := hZM _ (hmz ▸ inv_mem z.2) m.2
      have hz1 : (z : lBarA c L E) = 1 := by rw [hm1, mul_one] at h1; exact h1
      exact Prod.ext (Subtype.ext hz1) (Subtype.ext hm1)
    · intro x
      obtain ⟨z, hz, m, hm, rfl⟩ := hXZM x
      exact ⟨(⟨z, hz⟩, ⟨m, hm⟩), rfl⟩
  have hcb3 : cb ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hcb, ← map_pow]
    rw [show (⟨c, hEH hcE⟩ : NC) ^ 3 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3),
      map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    apply mkC_ne_one h
    have h2 : ((cb : lBarA c L E) : ↥NC ⧸ θC) = 1 := by rw [h1, Subgroup.coe_one]
    exact Subtype.ext h2
  have hZ3 : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers, orderOf_eq_prime hcb3 hcb1]
  have eZ₀ := zmodCyclicMulEquiv (Subgroup.isCyclic_zpowers cb)
  rw [← hZdef, hZ3] at eZ₀
  set eM : M ≃* projImage (glPi π 3 (p ^ f) K) :=
    MulEquiv.ofBijective (Ψ.comp M.subtype) ⟨fun m₁ m₂ hm => by
      have h1 : Ψ ((m₁ : lBarA c L E) * (m₂ : lBarA c L E)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hm
      exact Subtype.ext (mul_inv_eq_one.mp (hMinj _ (mul_mem m₁.2 (inv_mem m₂.2)) h1)),
      fun g => by
        obtain ⟨m, hm, hmg⟩ := hMsurj g
        exact ⟨⟨m, hm⟩, hmg⟩⟩ with heM
  exact ⟨π, p, f, K, inferInstance, hK, hq,
    ⟨(MulEquiv.ofBijective φ hφ).symm.trans (MulEquiv.prodCongr eZ₀.symm eM)⟩⟩

end Construction

end CFSG.RankThree.PartTwo.Sec13.Item138Proof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item138OuterN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ¬ E ≤ Subgroup.zpowers c ⊔ L

theorem item138PGLN_of (hout : Item138OuterN) : Item138PGLN :=
  fun G _ _ A c L E hH => Item138Proof.isZ3PGLThreePi_of_not_le hH (hout G A c L E hH)

theorem Item138Proof.not_le_of_isZ3PGLThreePi {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L E : Subgroup G} (hH : Hyp138 A c L E)
    (hPGLE : Sec8.IsZ3PGLThreePi (lBarA c L E)) : ¬ E ≤ Subgroup.zpowers c ⊔ L := by
  intro hle
  obtain ⟨h, -, hcE, hE3, -, hEN, -, -, -⟩ := hH
  have hL := h.mem_thetaComponentsAt
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun l hl => hLc l hl))
  have hinn : ∀ x ∈ E, ∀ hN : x ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hN⟩) z = w * z * w⁻¹ := by
    intro x hx hN
    have hx' : x ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hx'
    obtain ⟨_, ⟨k, rfl⟩, l, hl, rfl⟩ := hx'
    refine ⟨((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H l' =>
      rw [Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hck : c ^ k * (l' : G) = l' * c ^ k := (Commute.zpow_left (hLc l' l'.2).symm k).eq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc c ^ k * l * (l' : G) * (c ^ k * l)⁻¹ = c ^ k * (l * l' * l⁻¹) * (c ^ k)⁻¹ := by group
        _ = l * l' * l⁻¹ := by
          rw [(Commute.zpow_left (hLc _ (mul_mem (mul_mem hl l'.2) (inv_mem hl))).symm k).eq,
            mul_inv_cancel_right]
  exact false_of_inner_of_isZ3PGLThreePi h hEN hEH hEc
    (fun x hx => exists_lBar_conj_eq_of_inner hL hEN hEH hinn hx) hPGLE

end CFSG.RankThree.PartTwo.Sec13
