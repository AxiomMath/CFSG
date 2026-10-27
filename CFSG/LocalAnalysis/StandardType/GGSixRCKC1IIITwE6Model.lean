module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6ComponentPrime
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoord
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Line
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUActAux
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Seitz CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.RCKK1IIISU
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk onCenterQuotient_eq_one_imp)
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)

section Row


theorem three_dvd_card_centerQuot_of_row_III {X : Type} [Group X] {J : Subgroup X}
    (hrow : GGSixRCKJRow .III J) : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmodel
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.SymplecticPilot.card_of_lieModel_PSp_two_pow hm']
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordBC (by omega)
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hm']
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordTwistedA (by omega)

end Row

private theorem map_fixSubgroup_normalizerMonoidHom {X : Type} [Group X] {K : Subgroup X}
    (d : ↥(Subgroup.normalizer (K : Set X))) :
    (fixSubgroup (K.normalizerMonoidHom d)).map K.subtype =
      K ⊓ Subgroup.centralizer {(d : X)} := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
    have h1 : (d : X) * k * (d : X)⁻¹ = k := by
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val (mem_fixSubgroup.1 hk)
    exact mul_inv_eq_iff_eq_mul.1 h1
  · rintro ⟨hxK, hxC⟩
    refine ⟨⟨x, hxK⟩, mem_fixSubgroup.2 (Subtype.ext ?_), rfl⟩
    have hdx : (d : X) * x = x * d :=
      Subgroup.mem_centralizer_iff.1 hxC d (Set.mem_singleton _)
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, hdx]

private theorem commutator_subgroupOf_eq_self {X : Type} [Group X] {K J : Subgroup X}
    (hJK : J ≤ K) (hJ : commutator ↥J = ⊤) :
    ⁅J.subgroupOf K, J.subgroupOf K⁆ = J.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJK,
    ← Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Model


theorem exists_twistedE6_model_of_row_III
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B₁ : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hB1K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    (hJcomp : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hJK : J ≤ K) :
    ∃ ε : ↥K →* ↥(twistedE6RootGroup SUF SUσ), Function.Surjective ε ∧
      ε.ker = Subgroup.center ↥K ∧
      ∃ h : ↥(twistedE6InndiagGL SUF SUσ), h ^ 3 = 1 ∧ h ≠ 1 ∧
        CFSG.Open.IsComponentOf ((J.subgroupOf K).map ε)
          (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj SUF SUσ h))) ∧
        GGSixRCKJRow .III ((J.subgroupOf K).map ε) := by
  classical
  have hp3 : p = 3 :=
    prime_eq_three_of_twistedE6_label hp hp2 hBab hdB hB1K hrank hKq hlab hoddK hJcomp hrow
  subst hp3
  have hσθ : SUσ.toRingHom = frobQ 2 1 := RingHom.ext fun c => by
    change SUσ c = frobQ 2 1 c
    rw [rckSUc_sigma_apply, frobQ_apply, pow_one]
  obtain ⟨eC⟩ := nonempty_centerQuot_equiv_twistedE6_of_label hKq hlab hoddK
  have hsub : graphFixedRootGroup TwistTag.E6 SUF (frobQ 2 1) = twistedE6RootGroup SUF SUσ := by
    change graphFixedRootGroup TwistTag.E6 SUF (frobQ 2 1) =
      graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom
    rw [hσθ]
  let eSU : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(twistedE6RootGroup SUF SUσ) :=
    eC.trans (MulEquiv.subgroupCongr hsub)
  let dN : ↥(Subgroup.normalizer (K : Set X)) := ⟨d, hB1K hdB⟩
  let ζ : MulAut ↥K := K.normalizerMonoidHom dN
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center ↥K := QuotientGroup.ker_mk' _
  let β : MulAut (↥K ⧸ Subgroup.center ↥K) := centerQuotientHom ↥K ζ
  have hβ : ∀ k, π (ζ k) = β (π k) := fun k => (onCenterQuotient_apply_mk ζ k).symm
  have hζ3 : ζ ^ 3 = 1 := by
    have h : dN ^ 3 = 1 := Subtype.ext (by simpa [dN] using hBab.2 d hdB)
    rw [show ζ ^ 3 = K.normalizerMonoidHom (dN ^ 3) from (map_pow _ _ _).symm, h, map_one]
  have hβ3 : β ^ 3 = 1 := by
    rw [show β ^ 3 = centerQuotientHom ↥K (ζ ^ 3) from (map_pow _ _ _).symm, hζ3, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ1
    have : Group.IsPerfect ↥K := ⟨hKq.1⟩
    have hζ1 : ζ = 1 := onCenterQuotient_eq_one_imp ζ hβ1
    refine not_mem_centralizer_of_twistedE6_label_row_III hKq hlab hJcomp hrow
      (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
    have hfix : ζ ⟨g, hg⟩ = ⟨g, hg⟩ := by rw [hζ1, MulAut.one_apply]
    have hconj : d * g * d⁻¹ = g := by
      simpa [ζ, dN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hfix
    exact (mul_inv_eq_iff_eq_mul.1 hconj).symm
  have hJcK : CFSG.Assembly.IsComponentOf (J.subgroupOf K) (fixSubgroup ζ) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff K.subtype_injective).1
      (by rw [Subgroup.map_subgroupOf_eq_of_le hJK, map_fixSubgroup_normalizerMonoidHom dN]
          exact hJcomp)
  have h3J : 3 ∣ Nat.card ↥(J.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJK).toEquiv]
    exact (three_dvd_card_centerQuot_of_row_III hrow).trans
      (Subgroup.center ↥J).index_dvd_card
  have hJ3 : CFSG.Open.GLAPComponent 3 (fixSubgroup ζ) (J.subgroupOf K) :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf
      (isComponentOf_iff_open.1 hJcK) h3J
  have hJ3' := glaPComponent_map_fixSubgroup π hπker.le ζ β hβ hπs Nat.prime_three hJ3
  obtain ⟨h, hh3, hh1, _D, _i, -, -, -, hcomp, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S265.TE6.exists_twE6LineModel_of_glaPComponent_of_equiv
      rckSUc_card rckSUc_sigma_apply eSU hβ3 hβ1 hJ3'
  let ε : ↥K →* ↥(twistedE6RootGroup SUF SUσ) := eSU.toMonoidHom.comp π
  have hkerε : ε.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, ← hπker, MonoidHom.mem_ker]
    change eSU (π k) = 1 ↔ π k = 1
    exact eSU.map_eq_one_iff
  have hmapε : (J.subgroupOf K).map ε = ((J.subgroupOf K).map π).map eSU.toMonoidHom :=
    (Subgroup.map_map _ _ _).symm
  refine ⟨ε, eSU.surjective.comp hπs, hkerε, h, hh3, hh1, hmapε ▸ hcomp, ?_⟩
  exact (SCFourCover.largeEvenMarking_map_iff hkerε.le
    (commutator_subgroupOf_eq_self hJK hJcomp.2.2.1) (fun lab => ggSixRCKLabelRow lab = .III)).1
    (largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hrow)

end Model

end CFSG.StandardType.RCKC1
