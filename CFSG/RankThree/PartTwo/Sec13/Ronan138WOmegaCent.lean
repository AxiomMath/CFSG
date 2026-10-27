module

public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn
import CFSG.RankThree.PartTwo.Sec14.Ronan148WAutInner
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport
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
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138W

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem omegaCent_holds :
    ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (d : G) (K : Subgroup G),
      K ∈ thetaComponentsAt 3 d → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      E ≤ Subgroup.normalizer (K : Set G) →
      Late.sectionCentralizer E K ((aschbacherSolvableCore 3 K).map K.subtype) =
        (Subgroup.zpowers d : Set G) →
      Sec8.IsZ3PGLThreePi (lBarA d K E) → (∃ x₀ ∈ E, Sec4.InducesTypeOn K x₀ 3) →
      ∀ g ∈ Subgroup.normalizer (K : Set G), g ^ 3 = 1 →
        (∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Sec4.thetaQuotCentralizer K) →
          ∃ e ∈ E, e⁻¹ * g ∈ Sec4.thetaQuotCentralizer K := by
  intro G _ _ E d K hK hE hE27 hEN hCE _ hx₀ g hgN hg3 hgE
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, hx₀E, hx₀N, π, p, f, F, _, hF, hq, e, y, hyH, hy3, hyx⟩ := hx₀
  have hq2 : 2 < p ^ f :=
    Item138Proof.two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hK) hF hq e
  have := hF.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _)
      (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (projImage (Sec4.slPi π 3 (p ^ f) F))) :=
    Finite.of_injective (fun α : MulAut (projImage (Sec4.slPi π 3 (p ^ f) F)) =>
      (α : projImage (Sec4.slPi π 3 (p ^ f) F) → projImage (Sec4.slPi π 3 (p ^ f) F)))
      fun _ _ h => MulEquiv.ext (congrFun h)
  by_contra hno
  push Not at hno
  set N := Subgroup.normalizer (K : Set G) with hNdef
  set ρ : N →* MulAut (projImage (Sec4.slPi π 3 (p ^ f) F)) :=
    (MulAut.congr e).toMonoidHom.comp ((Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom)
    with hρ
  have hker : ∀ x : N, ρ x = 1 ↔ (x : G) ∈ Sec4.thetaQuotCentralizer K := by
    intro x
    have h1 : ρ x = 1 ↔ (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom x = 1 :=
      MulEquiv.map_eq_one_iff (MulAut.congr e)
    rw [h1, ← MonoidHom.mem_ker]
    exact (Subgroup.mem_map_iff_mem N.subtype_injective).symm
  set Es : Subgroup N := E.subgroupOf N with hEs
  set ψ : Es →* MulAut (projImage (Sec4.slPi π 3 (p ^ f) F)) := ρ.comp Es.subtype with hψ
  have hEbe : ψ.range = Es.map ρ := by rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hEb : CFSG.Open.IsElemAbelian 3 ψ.range := by
    rw [hEbe]
    exact (CFSG.Open.IsElemAbelian.subgroupOf hE N).map ρ
  have hEs27 : Nat.card Es = 27 := by
    rw [← hE27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hcardEs : Nat.card Es = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hCEi : ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) =
      (Subgroup.zpowers d : Set G) := by
    rw [← Sec13.sectionCentralizer_eq_inf hEN]
    exact hCE
  have hd3 : d ^ 3 = 1 := by
    have hd : d ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := by
      rw [hCEi]
      exact Subgroup.mem_zpowers d
    exact hE.2 d hd.1
  have hkerle : Nat.card ψ.ker ≤ 3 := by
    have hmem : ∀ x : ψ.ker, (((x : Es) : N) : G) ∈ Subgroup.zpowers d := by
      intro x
      have h1 : (((x : Es) : N) : G) ∈
          ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp (x : Es).2, (hker _).mp (MonoidHom.mem_ker.mp x.2)⟩
      rw [hCEi] at h1
      exact h1
    have hinj : Function.Injective
        (fun x : ψ.ker => (⟨_, hmem x⟩ : Subgroup.zpowers d)) := by
      intro x x' h
      have h' : (((x : Es) : N) : G) = (((x' : Es) : N) : G) :=
        congrArg (fun w : Subgroup.zpowers d => (w : G)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    calc Nat.card ψ.ker ≤ Nat.card (Subgroup.zpowers d) := Nat.card_le_card_of_injective _ hinj
      _ = orderOf d := Nat.card_zpowers d
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
  have hEb9 : 9 ≤ Nat.card ψ.range := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * 8 :=
      Nat.mul_le_mul hkerle (by omega)
    omega
  set gb := ρ ⟨g, hgN⟩ with hgbdef
  have hgb3 : gb ^ 3 = 1 := by
    have h1 : (⟨g, hgN⟩ : N) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hg3]; rfl)
    rw [hgbdef, ← map_pow, h1, map_one]
  have hgbE : gb ∉ ψ.range := by
    rintro ⟨⟨⟨e', he'N⟩, he'E⟩, hψe⟩
    apply hno e' (Subgroup.mem_subgroupOf.mp he'E)
    have h1 : ρ ((⟨e', he'N⟩ : N)⁻¹ * ⟨g, hgN⟩) = 1 := by
      have h2 : ρ ⟨e', he'N⟩ = gb := hψe
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    exact (hker _).mp h1
  have hgbc : ∀ x ∈ ψ.range, ∀ z ∈ Subgroup.zpowers gb, x * z = z * x := by
    rintro _ ⟨⟨⟨e', he'N⟩, he'E⟩, rfl⟩ z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute (ρ ⟨e', he'N⟩) gb := by
      have h1 := hgE e' (Subgroup.mem_subgroupOf.mp he'E)
      have h2 : ρ ((⟨g, hgN⟩ : N) * ⟨e', he'N⟩ * (⟨g, hgN⟩ : N)⁻¹ * (⟨e', he'N⟩ : N)⁻¹) = 1 :=
        (hker _).mpr h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hgbdef] at h2
      have h3 : gb * ρ ⟨e', he'N⟩ * gb⁻¹ = ρ ⟨e', he'N⟩ := mul_inv_eq_one.mp h2
      calc ρ ⟨e', he'N⟩ * gb = gb * ρ ⟨e', he'N⟩ * gb⁻¹ * gb := by rw [h3]
        _ = gb * ρ ⟨e', he'N⟩ := by group
    exact (hc.zpow_right k).eq
  have hinf : ψ.range ⊓ Subgroup.zpowers gb = ⊥ := Sec4.inf_zpowers_eq_bot hgb3 hgbE
  obtain ⟨hcard'', hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hgbc
  have hgb1 : gb ≠ 1 := fun h => hgbE (h ▸ Subgroup.one_mem _)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hgb3 hgb1] at hcard''
  have h9 : 9 < Nat.card (ψ.range ⊔ Subgroup.zpowers gb : Subgroup _) := by omega
  have hz3 : ∀ z ∈ Subgroup.zpowers gb, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgb3, one_zpow]
  have hEbc : ∀ a ∈ ψ.range, ∀ a' ∈ ψ.range, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hEb.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hzc : ∀ z ∈ Subgroup.zpowers gb, ∀ z' ∈ Subgroup.zpowers gb, z * z' = z' * z := by
    intro z hz z' hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    exact ((Commute.refl gb).zpow_zpow k k').eq
  have hcomm'' : ∀ x ∈ (ψ.range ⊔ Subgroup.zpowers gb : Subgroup _),
      ∀ x' ∈ (ψ.range ⊔ Subgroup.zpowers gb : Subgroup _), x * x' = x' * x := by
    intro x hx x' hx'
    rw [← SetLike.mem_coe, hset] at hx hx'
    obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨a', ha', z', hz', rfl⟩ := Set.mem_mul.mp hx'
    have h1 : Commute a (a' * z') :=
      Commute.mul_right (hEbc a ha a' ha') (hgbc a ha z' hz')
    have h2 : Commute z (a' * z') :=
      Commute.mul_right (hgbc a' ha' z hz).symm (hzc z hz z' hz')
    exact (Commute.mul_left h1 h2).eq
  have hE'' : CFSG.Open.IsElemAbelian 3 (ψ.range ⊔ Subgroup.zpowers gb) := by
    refine ⟨⟨⟨fun x x' => Subtype.ext (hcomm'' x x.2 x' x'.2)⟩⟩, fun x hx => ?_⟩
    rw [← SetLike.mem_coe, hset] at hx
    obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.mp hx
    rw [(show Commute a z from hgbc a ha z hz).mul_pow, hEb.2 a ha, hz3 z hz, one_mul]
  have hx₀y : ∀ m : projImage (Sec4.slPi π 3 (p ^ f) F),
      (ρ ⟨x₀, hx₀N⟩ m : Matrix.ProjGenLinGroup (Fin 3) F) = pmk y * m * (pmk y)⁻¹ := by
    intro m
    have h := hyx (e.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hx₀b : ρ ⟨x₀, hx₀N⟩ ∈ (ψ.range ⊔ Subgroup.zpowers gb : Subgroup _) :=
    Subgroup.mem_sup_left ⟨⟨⟨x₀, hx₀N⟩, Subgroup.mem_subgroupOf.mpr hx₀E⟩, rfl⟩
  exact Sec14.Ronan148W.not_mem_inner_of_type_three hF hq hq2 hyH hy3 hx₀y
    (Sec14.Ronan148W.mem_inner_of_pgl_of_elemAbelian hF hq hq2 hE'' h9 hx₀b hyH hx₀y)

end CFSG.RankThree.PartTwo.Sec13.Ronan138W
