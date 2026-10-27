module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Transfer
import CFSG.LocalAnalysis.StandardType.GGPumpUpQuotComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1pp

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType

section InnDiag

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem pptp5_innDiag_linear_not_u52_of
    (hSL : CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial)
    (hP1 : CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.LinPCompIsComp)
    (hP2 : CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.LinLabelDict)
    {S : Type} [Group S] [Finite S] {β : MulAut S} {J : Subgroup S} {labK : GLALabel}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hin : InnDiagKind S labK β)
    (hβ : β ^ 3 = 1) (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJU : HasLabel J (fun l => l = ⟨.twA, 4, 1⟩)) : False := by
  obtain ⟨K, hK, hKf, d, hd, hcard, A, u, e, hβu, hgraph⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiag_linear_data hcen hFam hin
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, n, hqp, hqcard⟩ := FiniteField.card' K
    rw [Nat.card_eq_fintype_card, hqcard] at hcard
    have hdvd : q ∣ 2 ^ (CFSG.LocalAnalysis.GLTheoremA.canonLabel labK).n := by
      rw [← hcard]
      exact dvd_pow_self q (PNat.ne_zero n)
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  have hMEq : MulAut.congr e β = u := by
    ext r
    have h1 := hβu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hβ, map_one]
  have hJ' : GLAPComponent 3 (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← fixSubgroup_map_congr e β]
    exact
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three e.injective).mpr hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom)
      (fun l : GLALabel => l = (⟨.twA, 4, 1⟩ : GLALabel)) :=
    hasLabel_transport e hJU
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.pComponent_psl_fixed hSL hP1 h2 hd A
      Nat.prime_three (by norm_num) u hgraph hpow (J.map e.toMonoidHom) hJ'
  have hEcard : Nat.card E =
      2 ^ ((CFSG.LocalAnalysis.GLTheoremA.canonLabel labK).n * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hcard, ← pow_mul]
  have hcanon := hP2 ↥(J.map e.toMonoidHom) (⟨.twA, 4, 1⟩ : GLALabel) a _ E ha hEcard hlabJ' ⟨φ⟩
  have htag : (CFSG.LocalAnalysis.GLTheoremA.canonLabel (⟨.twA, 4, 1⟩ : GLALabel)).tag =
      (⟨.A, a - 1, (CFSG.LocalAnalysis.GLTheoremA.canonLabel labK).n * Module.finrank K E⟩ :
        GLALabel).tag :=
    congrArg (fun l : GLALabel => l.tag) hcanon
  simp only [CFSG.LocalAnalysis.GLTheoremA.canonLabel] at htag
  exact absurd htag (by decide)

theorem innDiag_linear_not_u52
    {S : Type} [Group S] [Finite S]
    {β : MulAut S} {J : Subgroup S} {labK : GLALabel}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hin : InnDiagKind S labK β)
    (hβ : β ^ 3 = 1) (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJU : HasLabel J (fun l => l = ⟨.twA, 4, 1⟩)) : False :=
  pptp5_innDiag_linear_not_u52_of
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.LinPCompIsComp_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds
    hcen hFam hin hβ hJ hJU

private theorem pptp5_innDiagKind_linear_of_inner
    {K : Type} [Group K] [Finite K] {m : ℕ}
    (hquasi : CFSG.Open.IsQuasisimple K)
    (hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL m 2 1)
    (hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥)
    (hm : 3 ≤ m)
    {β : MulAut (K ⧸ Subgroup.center K)}
    (hinner : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (K ⧸ Subgroup.center K)) :
    InnDiagKind (K ⧸ Subgroup.center K) (⟨.A, m - 1, 1⟩ : GLALabel) β := by
  haveI : Group.IsPerfect K := ⟨hquasi.1⟩
  have hSperf : commutator (K ⧸ Subgroup.center K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.isQuasisimple_of_openQuasisimple hquasi
  have hΛ : GLAInLambda2 (⟨.A, m - 1, 1⟩ : GLALabel) := by
    simp only [GLAInLambda2, CFSG.Assembly.LargeEvenInLambda2]
    refine ⟨le_rfl, by omega, ?_⟩
    omega
  have hinner' : β ∈ (MulAut.conj : (K ⧸ Subgroup.center K) →*
      MulAut (K ⧸ Subgroup.center K)).range := by
    simpa only [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hinner
  obtain ⟨s, hs⟩ := hinner'
  refine ⟨hSperf, ⟨.A, m - 1, 1⟩, hΛ, ?_⟩
  simp only [CFSG.Assembly.LargeEvenRawDatum]
  rw [show m - 1 + 1 = m by omega]
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.StandardType.recipeLinear_of_statedClassicalModel (d := m) (f := 1) hSC
  refine ⟨F, hF, hFin, hcard, ?_⟩
  refine ⟨(MulEquiv.isSimpleGroup_congr e).1 hKq.2.1, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hKq.2.2
    exact ⟨e a, e b, fun heq => hab (e.injective (by rw [map_mul, map_mul, heq]))⟩
  · refine ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).trans e, trivial, ?_⟩
    refine ⟨MulAut.congr
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).trans e)
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut (K ⧸ Subgroup.center K) β), ?_, ?_⟩
    · rw [← CFSG.StandardType.RecipeFieldLinear.coe_recI]
      have hcq : CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut (K ⧸ Subgroup.center K)
          (MulAut.conj s) = MulAut.conj (QuotientGroup.mk s) := by
        ext x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
        rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut_mk, MulAut.conj_apply,
          MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hs, hcq, mulAut_congr_conj]
      exact CFSG.StandardType.RecipeFieldLinear.conj_mem_recI _
    · intro l l' hl
      subst hl
      have hq : (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm l =
          QuotientGroup.mk l := by
        rw [MulEquiv.symm_apply_eq, CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
        MulEquiv.symm_apply_apply, hq,
        CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut_mk,
        CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]

theorem pumpUp_not_psl_two
    {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) (m : ℕ) (hm : 3 ≤ m)
    (hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL m 2 1) : False := by
  obtain ⟨hβ, hJ, hJU⟩ := pumpUp_quotient_component h
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot h.quasi
  have hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL m 2 1 :=
    hS.statedClassicalModel_of_ne_zero (by omega)
  have hinner : CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K) :=
    CFSG.LocalAnalysis.GLTheoremA.I1431C2.lin_inner_of_model hSC hm hβ
  have hin : InnDiagKind (K ⧸ Subgroup.center K) (⟨.A, m - 1, 1⟩ : GLALabel)
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ) :=
    pptp5_innDiagKind_linear_of_inner h.quasi hSC hcen hm hinner
  exact innDiag_linear_not_u52 hcen (Or.inl rfl) hin hβ hJ hJU

end InnDiag

end CFSG.GGQ2Prime

end
