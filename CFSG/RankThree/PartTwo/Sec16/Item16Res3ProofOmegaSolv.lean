module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofOmega
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofFix

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res3Omega

section Perfect

variable {H : Type*} [Group H] [Finite H]

theorem exists_simple_quotient_of_isPerfect [Nontrivial H] (hH : Group.IsPerfect H) :
    ∃ (M : Subgroup H) (_ : M.Normal), IsSimpleGroup (H ⧸ M) ∧
      ∃ a b : H ⧸ M, a * b ≠ b * a := by
  obtain ⟨M, hMn, -, hsimple⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.exists_normal_isSimpleGroup_quotient H
  refine ⟨M, hMn, hsimple, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : Group.IsPerfect (H ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have : IsMulCommutative (H ⧸ M) := ⟨⟨fun a b => hcomm a b⟩⟩
  have : Nontrivial (H ⧸ M) := hsimple.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (H ⧸ M) inferInstance

end Perfect

theorem two_dvd_card_of_suzukiModel {S : Type} [Group S] {p e : ℕ}
    (h : CFSG.Blueprint.SuzukiModel S p e) [Finite S] : 2 ∣ Nat.card S := by
  obtain ⟨t, ht, -⟩ := KFacts.KP7.exists_involution_fixed_of_suzukiModel h
    (MonoidHom.id (MulAut S)) (E := ⊥) (fun x hx => by
      rw [Subgroup.mem_bot] at hx
      rw [hx, one_pow])
  rw [← ht]
  exact orderOf_dvd_natCard t

section KP

theorem suzukiModel_of_quotient {Y : Type} [Group Y] [Finite Y] (hK : CFSG.IsKGroup Y)
    (P : Subgroup Y) (h3 : ¬ 3 ∣ Nat.card P) {S : Type} [Group S] [Finite S] (f : P →* S)
    (hf : Function.Surjective f) (M : Subgroup S) [M.Normal] [IsSimpleGroup (S ⧸ M)]
    (hnab : ∃ a b : S ⧸ M, a * b ≠ b * a) : ∃ e : ℕ, CFSG.Blueprint.SuzukiModel (S ⧸ M) 2 e := by
  have hcat : CFSG.Assembly.InCatalog (S ⧸ M) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK P (S ⧸ M)
      ((QuotientGroup.mk' M).comp f) ((QuotientGroup.mk'_surjective M).comp hf)
  refine KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd (S ⧸ M) hnab hcat fun h => h3 ?_
  have h1 : Nat.card (S ⧸ M) ∣ Nat.card S := Subgroup.card_quotient_dvd_card M
  have h2 : Nat.card S ∣ Nat.card P := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact h.trans (h1.trans h2)

theorem eq_bot_of_isPerfect_of_coprime {Y : Type} [Group Y] [Finite Y] (hK : CFSG.IsKGroup Y)
    (P : Subgroup Y) (hP : Group.IsPerfect P) (h3 : ¬ 3 ∣ Nat.card P)
    (h2 : ¬ 2 ∣ Nat.card P) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨M, _, hsimple, hnab⟩ := exists_simple_quotient_of_isPerfect hP
  obtain ⟨e, he⟩ := suzukiModel_of_quotient hK P h3 (MonoidHom.id P) Function.surjective_id M
    hnab
  apply h2
  exact (two_dvd_card_of_suzukiModel he).trans (Subgroup.card_quotient_dvd_card M)

end KP

end Res3Omega

open Res3Omega Proof169 Proof1613 Proof1614 Proof1613Res

section Solv

theorem step1616OmegaSolv_of (h1612 : Step1612) (hNoSz : KSL3PiNoSz) : Step1616OmegaSolv := by
  intro G _ _ A c L h hPGL b hbA hb1
  have hA := h.isElemAbelian
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  obtain ⟨hsimp, hCL⟩ : IsSimpleGroup ↥L ∧
      ∀ T ∈ invariantPiSubgroups (Subgroup.centralizer (L : Set G)) A (piOf 2), T = ⊥ := by
    rcases h1612 G A c L h with h1 | ⟨⟨ψ⟩⟩
    · exact h1
    · exfalso
      obtain ⟨-, -, ⟨ψ'⟩, -⟩ := facts_l34 h ψ
      exact false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ'
  have hθL : aschbacherSolvableCore 3 ↥L = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_isSimpleGroup hLc hsimp
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  set N := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊓ Cc with hN
  set P := (perfectResidual ↥N).map N.subtype with hP
  suffices hP1 : P = ⊥ by
    have h1 : perfectResidual ↥N = ⊥ := by
      rw [hP, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hP1
      exact hP1
    exact perfect_residual_characterization.2.2.2.2.2.mp h1
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hPC : P ≤ Cc := hPN.trans inf_le_right
  have hPperf : Group.IsPerfect P := by
    have := (perfect_residual_characterization (G := ↥N)).2.2.1
    let e := (perfectResidual ↥N).equivMapOfInjective N.subtype N.subtype_injective
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hP3 : ¬ 3 ∣ Nat.card P := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    exact fun h3 => h1 (h3.trans (Subgroup.card_dvd_of_le (hPN.trans inf_le_left)))
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
  have hAc : A ≤ Cc := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf 3 _ (hAb ha), Subgroup.le_normalizer (hAc ha)⟩
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized A N hAN
      (perfectResidual ↥N)
  have hKc : CFSG.IsKGroup ↥Cc := isKGroup_centralizer h.toTheoremFourHyp hc1
  have hPNL : P ≤ Subgroup.normalizer (L : Set G) :=
    hPC.trans (centralizer_le_normalizer_L h.toSec14Std)
  set T := ↥L ⧸ aschbacherSolvableCore 3 ↥L with hT
  have hTL : IsLThreePi T := (facts_of_isZ3PGLThreePi h.toSec13Data hPGL).1
  have : Finite (MulAut T) := KFacts.KP7.finite_mulAut T
  set ρ : ↥P →* MulAut T :=
    ((Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hPNL)
    with hρ
  have hρ1 : ρ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ρ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hperf : Group.IsPerfect ρ.range :=
      Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
    obtain ⟨M, _, hsimple, hnab⟩ := exists_simple_quotient_of_isPerfect hperf
    set P' := P.subgroupOf Cc with hP'
    let eP : ↥P' ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPC
    have hP'3 : ¬ 3 ∣ Nat.card P' := by rwa [Nat.card_congr eP.toEquiv]
    obtain ⟨e, he⟩ := suzukiModel_of_quotient hKc P' hP'3
      (ρ.rangeRestrict.comp eP.toMonoidHom)
      (ρ.rangeRestrict_surjective.comp eP.surjective) M hnab
    exact hNoSz T hTL ρ.range M 2 e he
  have hPCL : P ≤ Subgroup.centralizer (L : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ρ ⟨x, hx⟩ = 1 := by
      have : ρ ⟨x, hx⟩ ∈ ρ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hρ1, Subgroup.mem_bot] at this
      exact this
    have h2 := congrArg (fun σ : MulAut T => σ ((⟨l, hl⟩ : ↥L) : T)) h1
    simp only [hρ, MonoidHom.coe_comp, Function.comp_apply, MulAut.one_apply] at h2
    rw [Sec4.thetaQuotMulAut_mk] at h2
    have h3 := eq_of_mk_eq hθL h2
    have h4 := congrArg Subtype.val h3
    have h5 : x * l * x⁻¹ = l := h4
    calc l * x = (x * l * x⁻¹) * x := by rw [h5]
      _ = x * l := by group
  have hP2 : ¬ 2 ∣ Nat.card P := by
    intro h2
    have hA3 : IsPGroup 3 A := isPGroup_three_of_isElemAbelian hA
    obtain ⟨Q, hQ, hQ1⟩ :=
      CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
        Nat.prime_three Nat.prime_two A P hA3 hAP
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3) h2
    apply hQ1
    refine hCL _ ⟨(Subgroup.map_subtype_le _).trans hPCL, ?_, hQ⟩
    exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr ((Q.isPGroup').map P.subtype)
  have hP'1 := eq_bot_of_isPerfect_of_coprime hKc (P.subgroupOf Cc)
    (by
      let eP : ↥(P.subgroupOf Cc) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPC
      exact Group.IsPerfect.ofSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv])
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv])
  rw [← Subgroup.map_subgroupOf_eq_of_le hPC, hP'1, Subgroup.map_bot]

end Solv

end CFSG.RankThree.PartTwo.Sec16
