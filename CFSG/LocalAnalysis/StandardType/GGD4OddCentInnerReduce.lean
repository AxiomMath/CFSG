module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentA2NotInnDiag
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3009
public import Certificates.Certificate12041
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldSchur
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankTransfer
import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofKG
import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGClass
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaGroup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnCount
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.GH74.BNPair.Coordinatization
import CFSG.GH74.GLS.SP.Local.SPLFaith
import CFSG.GH74.GLS.SP.Local.SPLRestrict
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrame
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylT
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Transport

variable {X Y : Type*} [Group X] [Group Y]

private theorem congr_apply_apply (e : X ≃* Y) (a : MulAut X) (x : X) :
    MulAut.congr e a (e x) = e (a x) := by
  simp [MulAut.congr_apply]

theorem ggKLocal_map (e : X ≃* Y) {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (h : GGKLocal A σ J) :
    GGKLocal (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e σ) (J.map e.toMonoidHom) := by
  obtain ⟨⟨hEA, hσA, hσ1, hcomp, hinv⟩, hker⟩ := h
  refine ⟨⟨D4Rank.isElemAbelian_map _ hEA, Subgroup.mem_map_of_mem _ hσA, ?_, ?_, ?_⟩, ?_⟩
  · intro h1
    exact hσ1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  · rw [gdf_fixed_congr]
    exact isComponentOf_map_mulEquiv e hcomp
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨j, hj, rfl⟩
    refine ⟨a j, hinv a ha j hj, ?_⟩
    change e (a j) = MulAut.congr e a (e j)
    rw [congr_apply_apply]
  · rintro _ ⟨a, ha, rfl⟩ htriv
    have ha' : ∀ j ∈ J, a j = j := by
      intro j hj
      have h1 := htriv (e j) ⟨j, hj, rfl⟩
      change MulAut.congr e a (e j) = e j at h1
      rw [congr_apply_apply] at h1
      exact e.injective h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hker a ha ha')
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    change MulAut.congr e σ ^ k = MulAut.congr e a
    rw [← map_zpow, hk]

theorem ggAutsFixedInCenter_of_map (e : X ≃* Y) {A : Subgroup (MulAut X)} {J : Subgroup X}
    (h : GGAutsFixedInCenter (A.map (MulAut.congr e).toMonoidHom) (J.map e.toMonoidHom)) :
    GGAutsFixedInCenter A J := by
  intro j hj
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
  have hfix : ∀ a' ∈ A.map (MulAut.congr e).toMonoidHom,
      a' ((eJ j : ↥(J.map e.toMonoidHom)) : Y) = (eJ j : Y) := by
    rintro _ ⟨a, ha, rfl⟩
    change MulAut.congr e a (e (j : X)) = e (j : X)
    rw [congr_apply_apply, hj a ha]
  have hc := h (eJ j) hfix
  have hc' := (MulEquivClass.apply_mem_center_iff eJ.symm).2 hc
  rwa [MulEquiv.symm_apply_apply] at hc'

theorem ggAutsInduceOn_map_of (e : X ≃* Y) {A : Subgroup (MulAut X)} {J : Subgroup X}
    {R : Type} [Group R] (θ' : ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) ≃* R)
    (I : Set (MulAut R))
    (h : GGAutsInduceOn A J
      ((centerQuotCongr (J.equivMapOfInjective e.toMonoidHom e.injective)).trans θ') I) :
    GGAutsInduceOn (A.map (MulAut.congr e).toMonoidHom) (J.map e.toMonoidHom) θ' I := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨φ, hφ, hind⟩ := h a ha
  refine ⟨φ, hφ, ?_⟩
  refine (largeEvenInduces_congr_equiv (J.equivMapOfInjective e.toMonoidHom e.injective) θ'
    (fun j j' : ↥J => a (j : X) = (j' : X))
    (fun y y' : ↥(J.map e.toMonoidHom) => MulAut.congr e a (y : Y) = (y' : Y)) ?_ φ).1 hind
  intro j j'
  change a (j : X) = (j' : X) ↔ MulAut.congr e a (e (j : X)) = e (j' : X)
  rw [congr_apply_apply]
  exact ⟨fun h' => by rw [h'], fun h' => e.injective h'⟩

end Transport

private theorem ggD4OddCentInner_core
    (h1 : GGD4InnerOneInput)
    (h4 : GGD4InnerFourInput) (h2m : GGD4InnerTwoMarkInput) (h2d : GGD4InnerTwoDichInput)
    {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤) {A : Subgroup (MulAut K)}
    {σ : MulAut K} {J : Subgroup K} (hloc : GGKLocal A σ J)
    (hA : Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4)
    {F₁ : Type} [Field F₁] [Finite F₁] {n : ℕ} (hF₁ : Nat.card F₁ = 2 ^ n)
    (θ : K ⧸ Subgroup.center K ≃* D4Recipe F₁)
    (hdat : GGOddCentDatum A ⟨.D, 4, n⟩ (LargeEvenInnSet (D4Recipe F₁)) (D4FieldSet F₁) θ)
    (hσ : ggInducedAut θ σ ∈ LargeEvenInnSet (D4Recipe F₁)) :
    LargeEvenMarking J fun lab' _ _ I' _ θ' =>
      (GGLabelA2 lab' ∧ lab'.tag = .twA ∧ Subgroup.center J ≠ ⊥ ∧
        (GGAutsFixedInCenter A J ∨ ¬ GGAutsInduceOn A J θ' I')) ∨
      (lab'.tag = .A ∧ lab'.rank = 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F₁ := Fintype.ofFinite F₁
  haveI : CharP F₁ 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hF₁])
  have hloc0 := hloc
  obtain ⟨⟨hEA, hσA, hσ1, hcomp, -⟩, -⟩ := hloc
  have hodd : Odd n := hdat.2.2.1
  set Θ : D4Recipe F₁ ≃* Om8 F₁ := RecipeFieldOmega.plusEquiv (K := F₁) (m := 4) one_le_four
    with hΘ
  obtain ⟨r, hr⟩ := hσ
  set s : Om8 F₁ := Θ r with hs_def
  have hs_conj : MulAut.congr Θ (ggInducedAut θ σ) = MulAut.conj s := by
    rw [← hr, mulAut_congr_conj]
  have hσ3 : σ ^ 3 = 1 := hEA.2 σ hσA
  have hs3 : s ^ 3 = 1 := by
    apply NbrGraphD4.conj_injective
    rw [map_pow, ← hs_conj, ← map_pow, ← map_pow, hσ3, map_one, map_one, map_one]
  have hinj : Function.Injective fun a : MulAut K => MulAut.congr Θ (ggInducedAut θ a) :=
    (MulAut.congr Θ).injective.comp (ggInducedAut_injective_of_perfect hK θ)
  have hs1 : s ≠ 1 := by
    intro h
    apply hσ1
    apply hinj
    change MulAut.congr Θ (ggInducedAut θ σ) = MulAut.congr Θ (ggInducedAut θ 1)
    rw [hs_conj, h, map_one, map_one, map_one]
  obtain ⟨a₀, ha₀A, ha₀⟩ := hdat.2.2.2.2.2
  set α : MulAut (Om8 F₁) := MulAut.congr Θ (ggInducedAut θ a₀) with hα_def
  have hα3 : α ^ 3 = 1 := by
    rw [hα_def, ← map_pow, ← map_pow, hEA.2 a₀ ha₀A, map_one, map_one]
  have hαout : α ∉ Inn (Om8 F₁) ⊔ (AutOm.fieldAutP 4).range := fun h =>
    ha₀ (NbrGraphD4.exists_inner_mul_field_of_mem h)
  have hcomm : a₀ * σ = σ * a₀ :=
    congrArg Subtype.val (hEA.1.is_comm.comm ⟨a₀, ha₀A⟩ ⟨σ, hσA⟩)
  have hαs : α s = s := by
    apply NbrGraphD4.conj_injective
    have h' : α * MulAut.conj s = MulAut.conj s * α := by
      rw [← hs_conj, hα_def, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm]
    rw [D4Rank.mulAut_mul_conj α s] at h'
    exact mul_right_cancel h'
  have hd : D4Rank.omFixDim s = 2 ∨ D4Rank.omFixDim s = 4 :=
    L613KG.omFixDim_two_or_four hα3
      (fun g hg => hαout (NbrGraphD4.mem_inner_sup_of_conjAct hα3 hg)) hs3 hs1 hαs
  by_cases hn3 : 3 ≤ n
  ·
    have hZ : Subgroup.center K = ⊥ := ggD4_center_eq_bot hK (by omega) hF₁ θ
    set e : K ≃* Om8 F₁ := (mulEquivOfCenterBot θ hZ).trans Θ with he
    have hcongr : ∀ a : MulAut K, MulAut.congr e a = MulAut.congr Θ (ggInducedAut θ a) := by
      intro a
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [congr_apply_apply, he, MulEquiv.trans_apply, MulEquiv.trans_apply, congr_apply_apply,
        ggInducedAut_mulEquivOfCenterBot]
    have hloc' := ggKLocal_map e hloc0
    rw [hcongr σ, hs_conj] at hloc'
    set A' := A.map (MulAut.congr e).toMonoidHom with hA'
    set J' := J.map e.toMonoidHom with hJ'
    have hcardA' : Nat.card A' = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    have hcomp' : IsComponentOf J' (ggAutFixedSubgroup (MulAut.conj s)) := hloc'.1.2.2.2.1
    set eJ : ↥J ≃* ↥J' := J.equivMapOfInjective e.toMonoidHom e.injective with heJ
    rcases hd with hd2 | hd4
    ·
      have hZJ : Subgroup.center ↥J' ≠ ⊥ → Subgroup.center ↥J ≠ ⊥ := by
        intro h hbot
        apply h
        rw [← Subgroup.map_center_eq eJ, hbot, Subgroup.map_bot]
      have hmarkJ : LargeEvenMarking ↥J fun lab _ _ _ _ _ =>
          GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center ↥J ≠ ⊥ :=
        largeEvenMarking_congr eJ (fun lab R _ I F θ' h => ⟨h.1, h.2.1, hZJ h.2.2⟩)
          (h2m F₁ n hF₁ hodd s hs3 hd2 J' hcomp')
      have hdich : GGMarkingAll (K := ↥J) fun lab _ _ I _ θ' =>
          (GGLabelA2 lab ∧ lab.tag = .twA) →
            GGAutsFixedInCenter A J ∨ ¬ GGAutsInduceOn A J θ' I := by
        rcases hA with h27 | h81
        · have hdat27 : ∀ a ∈ A', a ∈ Inn (Om8 F₁) ⊔ (AutOm.fieldAutP 4).range →
              a ∈ Inn (Om8 F₁) := by
            rintro _ ⟨a, ha, rfl⟩ hmem
            change MulAut.congr e a ∈ _ at hmem ⊢
            rw [hcongr a] at hmem ⊢
            exact (RecipeFieldOmega.mem_innSet_iff_congr Θ _).1
              (hdat.2.2.2.2.1 h27 a ha (NbrGraphD4.exists_inner_mul_field_of_mem hmem))
          have hout' : ∃ a ∈ A', a ∉ Inn (Om8 F₁) ⊔ (AutOm.fieldAutP 4).range :=
            ⟨MulAut.congr e a₀, Subgroup.mem_map_of_mem _ ha₀A, by rw [hcongr a₀]; exact hαout⟩
          have hd' := h2d F₁ n hF₁ hodd A' s J' hloc' (hcardA'.trans h27) hd2 hdat27 hout'
          refine ggMarkingAll_congr eJ.symm (fun lab R _ I F θ' h hl => ?_) hd'
          rcases h hl with hfix | hnot
          · exact Or.inl (ggAutsFixedInCenter_of_map e hfix)
          · refine Or.inr fun hind => hnot ?_
            refine ggAutsInduceOn_map_of e _ I ?_
            rwa [centerQuotCongr_symm, centerQuotCongr_trans_symm_trans]
        · exact ggMarkingAll_mono (fun lab R _ I F θ' h hl => Or.inr (h hl))
            (ggD4OddCentA2NotInnDiagInput_holds K hK A σ J hloc0 h81)
      exact largeEvenMarking_mono (fun lab R _ I F θ' h =>
        Or.inl ⟨h.1.1, h.1.2.1, h.1.2.2, h.2 ⟨h.1.1, h.1.2.1⟩⟩) (ggMarkingAll_apply hdich hmarkJ)
    ·
      exact largeEvenMarking_congr eJ (fun lab R _ I F θ' h => Or.inr h)
        (h4 F₁ n hF₁ hodd s hs3 hd4 J' hcomp')
  ·
    have hn1 : n = 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    have hF₂ : Nat.card F₁ = 2 := by rw [hF₁, hn1, pow_one]
    set s₁ : MulAut (D4Recipe F₁) := ggInducedAut θ σ with hs₁
    let φ : K ⧸ Subgroup.center K ≃* orthDerived (coordinateQuadPlus 4 F₁) :=
      θ.trans ((RecipeFieldOmega.plusEquiv (K := F₁) (m := 4) (by norm_num)).trans
        (CFSG.SeitzReduction.OmegaPilot.derivedEquiv (coordinateQuadPlus 4 F₁)))
    have hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus 4 2 1 :=
      CFSG.SeitzReduction.OmegaPilot.lieModel_of_mulEquiv_orthDerived_plus
        (m := 4) (f := 1) le_rfl le_rfl (by simpa using hF₂) φ
    haveI : Group.IsPerfect K := ⟨hK⟩
    have hcZ4 : Nat.card (Subgroup.center K) ∣ 4 :=
      CFSG.ComponentClassification.RankTwoClassical.card_center_dvd_four_of_omegaEight hL
    let π : K →* D4Recipe F₁ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hπsurj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπker : ∀ g : K, π g = 1 → g ∈ Subgroup.center K := by
      intro g hg
      have h1 : (QuotientGroup.mk' (Subgroup.center K)) g = 1 :=
        θ.injective (by simpa [π] using hg)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcen_ker : ∀ z : K, z ∈ Subgroup.center K → π z = 1 := by
      intro z hz
      change θ (z : K ⧸ Subgroup.center K) = 1
      rw [(QuotientGroup.eq_one_iff z).2 hz, map_one]
    have hcomm1 : ∀ k : K, s₁ (π k) = π (σ k) := by
      intro k
      show ggInducedAut θ σ (θ (k : K ⧸ Subgroup.center K)) =
        θ ((σ k : K) : K ⧸ Subgroup.center K)
      rw [ggInducedAut_apply]
    have hmap : (ggAutFixedSubgroup σ).map π = ggAutFixedSubgroup s₁ := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        have hg' : σ g = g := hg
        show s₁ (π g) = π g
        rw [hcomm1, hg']
      · intro r hr
        have hr' : s₁ r = r := hr
        obtain ⟨g, hg⟩ := hπsurj r
        haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        have hx : g⁻¹ * σ g ∈ Subgroup.center K := by
          apply hπker
          rw [map_mul, map_inv, ← hcomm1 g, hg, hr']
          group
        obtain ⟨z, hz, hzfix⟩ := CFSG.GH74.GLS.SP.exists_fixed_mul_mem_of_coprime σ
          (r := 3) (e := 1)
          (by simpa using hσ3) (Subgroup.center K)
          (fun v hv => by
            rw [Subgroup.mem_center_iff] at hv ⊢
            intro y
            obtain ⟨w, rfl⟩ := σ.surjective y
            rw [← map_mul, ← map_mul, hv w])
          (by
            intro h3
            exact absurd (dvd_trans h3 hcZ4) (by norm_num))
          hx
        refine Subgroup.mem_map.2 ⟨g * z, ?_, ?_⟩
        · exact hzfix
        · rw [map_mul, hcen_ker z hz, mul_one]; exact hg
    have hnotker : ¬ J ≤ π.ker := by
      intro hle
      have hcenterJ : Subgroup.center ↥J = ⊤ := by
        rw [eq_top_iff]
        intro j _
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext
          (Subgroup.mem_center_iff.mp (hπker (j : K) (hle j.2)) (k : K))
      haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hcomp.2.2.2.toNontrivial
      obtain ⟨q, hq⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
      have hq1 : q = 1 := by
        induction q using QuotientGroup.induction_on with
        | H x =>
          rw [QuotientGroup.eq_one_iff, hcenterJ]
          exact Subgroup.mem_top x
      exact hq hq1
    have hJmap : IsComponentOf (J.map π) (ggAutFixedSubgroup s₁) := by
      have hcompO : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup σ) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open J
          (ggAutFixedSubgroup σ)).1 hcomp
      have hmapO := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map π hπker hcompO
      rw [hmap] at hmapO
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
        (J.map π) (ggAutFixedSubgroup s₁)).2 hmapO
    have hfixΘ : ggAutFixedSubgroup (MulAut.conj s) =
        (ggAutFixedSubgroup s₁).map Θ.toMonoidHom := by
      rw [← hs_conj, gdf_fixed_congr]
    have hJΓ := isComponentOf_map_mulEquiv Θ hJmap
    rw [← hfixΘ] at hJΓ
    exact (h1 F₁ hF₂ s hs3 hd _ hJΓ).elim

theorem ggD4OddCentInnerInput_of_om8
    (h1 : GGD4InnerOneInput) (h4 : GGD4InnerFourInput) (h2m : GGD4InnerTwoMarkInput)
    (h2d : GGD4InnerTwoDichInput) : GGD4OddCentInnerInput := by
  intro K _ _ hK A σ J hloc hA P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  obtain ⟨tag, rank, n⟩ := lab
  by_cases hD : tag = .D ∧ rank = 4
  ·
    obtain ⟨rfl, rfl⟩ := hD
    refine ⟨hperf, ⟨.D, 4, n⟩, hlab, ?_⟩
    unfold LargeEvenRawDatumLegacy at hraw ⊢
    rw [if_neg (by norm_num : ¬ (4 : ℕ) = 3)] at hraw
    rw [if_neg (by norm_num : ¬ (4 : ℕ) = 3)]
    obtain ⟨F₁, i1, i2, hF₁, hs, hna, θ, hPθ⟩ := hraw
    exact ⟨F₁, i1, i2, hF₁, hs, hna, θ, hPθ, fun hdat hσ =>
      ggD4OddCentInner_core h1 h4 h2m h2d hK hloc hA hF₁ θ hdat hσ⟩
  ·
    refine ⟨hperf, ⟨tag, rank, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hdat _ => absurd ⟨hdat.1, hdat.2.1⟩ hD⟩

end CFSG.StandardType

end
