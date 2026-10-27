module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphShape
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentA2NotInnDiag
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldSchur
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnCount
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGLDer
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.GH74.BNPair.Coordinatization
import CFSG.GH74.GLS.SP.Local.SPLFaith
import CFSG.GH74.GLS.SP.Local.SPLRestrict
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrame
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylT
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

private theorem ggD4OddCentGraph_marking_of_map {X Y : Type} [Group X] [Group Y]
    {J : Subgroup X} {π : X →* Y} (hJperf : commutator ↥J = ⊤)
    (eJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map π) ⧸ Subgroup.center ↥(J.map π))
    {S : LargeEvenLabel → Prop}
    (h : LargeEvenMarking ↥(J.map π) fun lab _ _ _ _ _ => S lab) :
    LargeEvenMarking ↥J fun lab _ _ _ _ _ => S lab := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hJperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, eJ.trans θ, hθ⟩

private theorem ggD4OddCentGraph_core
    {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) {A : Subgroup (MulAut K)} {σ : MulAut K} {J : Subgroup K}
    (hloc : GGKLocal A σ J) {F₁ : Type} [Field F₁] [Finite F₁] {n : ℕ}
    (hF₁ : Nat.card F₁ = 2 ^ n) (hodd : Odd n)
    (θ : K ⧸ Subgroup.center K ≃* D4Recipe F₁)
    (hnot : ¬ GGInnField (LargeEvenInnSet (D4Recipe F₁)) (D4FieldSet F₁)
      (ggInducedAut θ σ)) :
    LargeEvenMarking J fun lab' _ _ _ _ _ =>
      GGLabelG2 lab' ∨ lab'.tag = .triD4 ∨
        (GGLabelA2 lab' ∧ lab'.tag = .twA ∧ Subgroup.center J = ⊥) := by
  obtain ⟨hAutLocal, hfaith⟩ := hloc
  obtain ⟨hEA, hσA, -, hcomp, hJsA⟩ := hAutLocal
  have hpow : σ ^ 3 = 1 := hEA.2 σ hσA
  let s : MulAut (D4Recipe F₁) := ggInducedAut θ σ
  have hs3 : s ^ 3 = 1 := by
    show (ggInducedAut θ σ) ^ 3 = 1
    rw [← map_pow, hpow, map_one]
  have hshape : GGD4OddCentOuterShape n ↥(ggAutFixedSubgroup s) :=
    ggD4OddCent_outerShape hF₁ hodd hs3 hnot
  by_cases hn3 : 3 ≤ n
  ·
    have hZ : Subgroup.center K = ⊥ := ggD4_center_eq_bot hK (by omega) hF₁ θ
    let e : K ≃* D4Recipe F₁ := mulEquivOfCenterBot θ hZ
    have hFix : (ggAutFixedSubgroup σ).map e.toMonoidHom = ggAutFixedSubgroup s :=
      (ggAutFixedSubgroup_ggInducedAut θ hZ σ).symm
    let e' : ↥(ggAutFixedSubgroup σ) ≃* ↥(ggAutFixedSubgroup s) :=
      (Subgroup.equivMapOfInjective (ggAutFixedSubgroup σ) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hFix)
    have hshape' : GGD4OddCentOuterShape n ↥(ggAutFixedSubgroup σ) :=
      GGD4OddCentOuterShape.of_mulEquiv e' hshape
    exact ggD4OddCent_outerShape_marking hodd hshape' hcomp
  ·
    have hn1 : n = 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    rw [hn1] at hF₁ hshape
    haveI : Fintype F₁ := Fintype.ofFinite F₁
    have hF₂ : Nat.card F₁ = 2 := by simpa using hF₁
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F₁ 2 :=
      charP_of_card_eq_prime_pow (p := 2) (f := 1)
        (by rw [← Nat.card_eq_fintype_card]; exact hF₂)
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
    have hcomm : ∀ k : K, s (π k) = π (σ k) := by
      intro k
      show ggInducedAut θ σ (θ (k : K ⧸ Subgroup.center K)) =
        θ ((σ k : K) : K ⧸ Subgroup.center K)
      rw [ggInducedAut_apply]
    have hmap : (ggAutFixedSubgroup σ).map π = ggAutFixedSubgroup s := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        have hg' : σ g = g := hg
        show s (π g) = π g
        rw [hcomm, hg']
      · intro r hr
        have hr' : s r = r := hr
        obtain ⟨g, hg⟩ := hπsurj r
        haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        have hx : g⁻¹ * σ g ∈ Subgroup.center K := by
          apply hπker
          rw [map_mul, map_inv, ← hcomm g, hg, hr']
          group
        obtain ⟨z, hz, hzfix⟩ := CFSG.GH74.GLS.SP.exists_fixed_mul_mem_of_coprime σ
          (r := 3) (e := 1)
          (by simpa using hpow) (Subgroup.center K)
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
    have hJmap : IsComponentOf (J.map π) (ggAutFixedSubgroup s) := by
      have hcompO : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup σ) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open J
          (ggAutFixedSubgroup σ)).1 hcomp
      have hmapO := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map π hπker hcompO
      rw [hmap] at hmapO
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
        (J.map π) (ggAutFixedSubgroup s)).2 hmapO
    let res : ↥J →* ↥(J.map π) :=
      { toFun := fun j => ⟨π (j : K), Subgroup.mem_map_of_mem π j.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
    have hres : Function.Surjective res := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hxJ, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hxJ⟩, Subtype.ext hxy⟩
    have hresker : res.ker ≤ Subgroup.center ↥J := by
      intro j hj
      rw [MonoidHom.mem_ker] at hj
      have hj1 : π (j : K) = 1 := congrArg Subtype.val hj
      have hjZ : (j : K) ∈ Subgroup.center K := hπker (j : K) hj1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hjZ (y : K))
    have hQnat : CFSG.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1
        hcomp.2.2
    obtain ⟨eJ⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
      hQnat res hres hresker
    rcases hshape with
      ⟨k, i1, i2, hk, ⟨E⟩⟩ | ⟨F, i1, i2, hFc, ⟨E⟩⟩ | ⟨d, K₃, i1, i2, hd, hnd, -⟩
    · obtain ⟨-, hmark⟩ := ggTriD4_g2_clause (X := D4Recipe F₁) (C := ggAutFixedSubgroup s)
        (n := 1) le_rfl hk E hJmap
      refine largeEvenMarking_mono (fun lab R _ I F θ h => Or.inl h)
        (ggD4OddCentGraph_marking_of_map hcomp.2.2.1 eJ hmark)
    · haveI : Group.IsSolvable ↥(ggAutFixedSubgroup s) := by
        haveI := ggTriD4_pgu_two_solvable (n := 1) rfl hFc
        exact Group.isSolvable_of_isSolvable_injective (f := E.toMonoidHom) E.injective
      exact (gffa2_false_of_solvable this hJmap).elim
    · exfalso; omega

theorem ggD4OddCentGraphCore_holds
    : GGD4OddCentGraphCore := by
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
    exact ⟨F₁, i1, i2, hF₁, hs, hna, θ, hPθ, fun hdat hnot =>
      ggD4OddCentGraph_core hK hloc hF₁ hdat.2.2.1 θ hnot⟩
  ·
    refine ⟨hperf, ⟨tag, rank, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hdat _ => absurd ⟨hdat.1, hdat.2.1⟩ hD⟩

theorem ggD4OddCentGraphInput_holds
    : GGD4OddCentGraphInput :=
  ggD4OddCentGraphInput_of_graphCore ggD4OddCentGraphCore_holds

end CFSG.StandardType
