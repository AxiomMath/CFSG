module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieModelClosed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Odd
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie (IsSmallThreeTag)
open CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
  (quotientMap quotientMap_mk fixed_quotient_iff)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_fixHom {L : Subgroup G} {b : G} (hb : b ∈ normalizer (L : Set G))
    (hbp : (orderOf b).Prime) (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) :
    ∃ φ : ↥(L ⊓ centralizer ({b} : Set G)) →*
        ↥(signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)),
      Function.Surjective φ ∧ Nat.card φ.ker ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
  classical
  haveI : Fact (orderOf b).Prime := ⟨hbp⟩
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨b, hb⟩ with hαdef
  have hN : ∀ n ∈ CFSG.solvableRadical ↥L, α n ∈ CFSG.solvableRadical ↥L := fun n hn => by
    rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv α]
    exact Subgroup.mem_map_of_mem _ hn
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ orderOf b = 1 := by
    rw [← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hα : α ^ orderOf b = 1 := by rw [hαdef, ← map_pow, hbpow, map_one]
  have hθq : ∀ z : BarInf L,
      quotientMap α (CFSG.solvableRadical ↥L) hN z = inducedBarInfAutHom L ⟨b, hb⟩ z := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x => rfl
  have hmem : ∀ x : ↥(L ⊓ centralizer ({b} : Set G)),
      ((QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp (Subgroup.inclusion inf_le_left)) x ∈
        signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) := by
    intro x
    change inducedBarInfAutHom L ⟨b, hb⟩ (QuotientGroup.mk (Subgroup.inclusion inf_le_left x)) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left x)
    rw [← hθq, quotientMap_mk]
    congr 1
    apply Subtype.ext
    rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxc := (mem_inf.1 x.2).2
    rw [mem_centralizer_singleton_iff] at hxc
    change b * (x : G) * b⁻¹ = x
    rw [← hxc, mul_inv_cancel_right]
  let φ := ((QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp
    (Subgroup.inclusion inf_le_left)).codRestrict _ hmem
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨z, hz⟩
    have hz' : quotientMap α (CFSG.solvableRadical ↥L) hN z = z := by
      rw [hθq]
      exact hz
    obtain ⟨y, rfl, hy⟩ := (fixed_quotient_iff α hα (CFSG.solvableRadical ↥L) hN hbN z).1 hz'
    have hyc : (y : G) ∈ centralizer ({b} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hy
      rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      change b * (y : G) * b⁻¹ = y at h1
      calc (y : G) * b = b * y * b⁻¹ * b := by rw [h1]
        _ = b * y := by group
    exact ⟨⟨y, mem_inf.2 ⟨y.2, hyc⟩⟩, rfl⟩
  · have hle : φ.ker.map (Subgroup.inclusion (inf_le_left :
        L ⊓ centralizer ({b} : Set G) ≤ L)) ≤ CFSG.solvableRadical ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx))
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective
      (inf_le_left : L ⊓ centralizer ({b} : Set G) ≤ L))]
    exact Subgroup.card_dvd_of_le hle

theorem uc22s2112r34_false_of_fixed {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hLM : L ≤ D.M) {p : ℕ} (hpσ : p ∈ D.sig)
    (hMs : IsStronglyPEmbedded p D.M) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime)
    (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)))
    {Y : Subgroup (BarInf L)} (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    {S : Type} [Group S] [IsSimpleGroup S] (hSns : ¬ Group.IsSolvable S) (g : ↥Y →* S)
    (hg : Function.Surjective g) (hpS : p ∣ Nat.card S) (h5 : p = 5 → ¬ IsAlt S 5) : False := by
  classical
  obtain ⟨hp, -⟩ := D.sig_prime p hpσ
  obtain ⟨φ, hφ, hker⟩ := uc22s2112r34_exists_fixHom hb hbp hbN
  obtain ⟨hHne, hHM, -, hCH⟩ := uc22s2112r2_normalizer hH c hLM hbB hbp
  have hcop : p.Coprime (Nat.card φ.ker) :=
    Nat.Coprime.coprime_dvd_right hker ((hp.coprime_iff_not_dvd).2 hpN)
  have hrC : 2 ≤ Open.pRank p (L ⊓ centralizer ({b} : Set G)) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel p hp φ hφ hcop,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrank
  have hrank' : 2 ≤ Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    obtain ⟨E, hEC, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrC
    exact UC6S846.le_pRank' hp (hEC.trans hCH) hEel hEc
  let Y' : Subgroup ↥(signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) :=
    Y.subgroupOf _
  let A : Subgroup ↥(L ⊓ centralizer ({b} : Set G)) := Y'.comap φ
  let eA := A.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let g' : ↥(A.map (Subgroup.subtype _)) →* S :=
    ((g.comp (Subgroup.subgroupOfEquivOfLe hY).toMonoidHom).comp (φ.subgroupComap Y')).comp
      eA.symm.toMonoidHom
  have hg' : Function.Surjective g' :=
    ((hg.comp (Subgroup.subgroupOfEquivOfLe hY).surjective).comp
      (φ.subgroupComap_surjective Y' hφ)).comp eA.symm.surjective
  haveI : Group.IsPerfect S := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hbot | htop
    · exact absurd ⟨⟨1, by rw [derivedSeries_one]; exact hbot⟩⟩ hSns
    · exact ⟨htop⟩
  obtain ⟨D0, hD0A, hD0perf, f0, hf0⟩ := uc22s2112r2_exists_perfect g' hg'
  exact uc22s2112r2_false_of_kf7 hKF7 hpσ hMs hHne hHM hrank'
    ((hD0A.trans (Subgroup.map_subtype_le A)).trans hCH) hD0perf hSns f0 hf0 hpS h5

section Cover


theorem uc22s2112r34_not_dvd_center_char {M L : Subgroup G} (hL : L ∈ calC M)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ≠ .twistedG2)
    (hX : LieModel (BarInf L) t n p f)
    (hcl : (5 ≤ p ^ f ∧ ¬ (t = .PSL ∧ n = 2)) ∨ (p = 3 ∧ f = 1 ∧ ¬ IsSmallThreeTag t n)) :
    ¬ p ∣ Nat.card ↥(center (Bar2 L)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hadm := hX.admissible
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    cases t
    case twistedB2 => exact absurd hadm.2.2.2.1 hp2
    case twistedF4 => exact absurd hadm.2.2.2.1 hp2
    case Tits => exact absurd hadm.2.2.2.1 hp2
    case twistedG2 => exact absurd rfl ht
    all_goals trivial
  exact PartTwo.Inputs1719.OddLie.not_dvd_card_center_of_lieModel hp hp2 hfund hadm hL.2.2
    (CFSG.Blueprint.LieModel.of_mulEquiv e hX) hcl

end Cover

theorem uc22s2112r34_not_dvd_center (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {M L : Subgroup G} (hL : L ∈ calC M)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) t n p f) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrg : ¬ r ∣ (genericOrders t n p f).1) : ¬ r ∣ Nat.card ↥(center (Bar2 L)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  exact fun h => hrg (CFSG.LocalAnalysis.RankFourTheoremC.p_dvd_genericOrders_of_lieModel hGA hr
    hr5 hL.2.2 e.symm
    (CFSG.ComponentClassification.HarrisLit.T1.P58b3.models_lieModel_of_lieModel hTB hp hp2 hX) h)

theorem uc22s2112r34_le_pRank_of_dvd (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {n p f : ℕ} (hX : LieModel (BarInf L) t n p f)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrg : r ∣ (genericOrders t n p f).1) :
    (t = .PSL ∨ t = .PSU) ∧ r ∣ n ∧ (4 ≤ n → n - 2 ≤ Open.pRank r L) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hPU : (t = .PSL ∨ t = .PSU) ∧ r ∣ n := by
    rcases CFSG.LocalAnalysis.RankFourTheoremC.eq_psl_or_psu_of_dvd_genericOrders hr hr5 t n p f
      hrg with ⟨h, hrn, -⟩ | ⟨h, hrn, -⟩
    · exact ⟨Or.inl h, hrn⟩
    · exact ⟨Or.inr h, hrn⟩
  refine ⟨hPU.1, hPU.2, fun hn => ?_⟩
  obtain ⟨eB⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hq := hL.2.2
  obtain ⟨eK⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := r) hq
  have hperf : Group.IsPerfect (Bar2 L ⧸ GL83.I243.Cover.primeCentre r (Bar2 L)) :=
    ⟨(GL83.I243.Cover.isQuasisimple_quotient hq).1⟩
  have hcl : t ∈ CFSG.Blueprint.classicalTags := by
    rcases hPU.1 with rfl | rfl <;> decide
  obtain ⟨he1, he1', he2, he2'⟩ := CFSG.RankThree.PartOne.exceptionalOrders_bounds t n p f
  have hle : ∀ a : ℕ, 1 ≤ a → a ≤ 4 → ¬ r ∣ a := fun a ha ha4 hra =>
    absurd (Nat.le_of_dvd (by omega) hra) (by omega)
  have hb : ¬ r ∣ (genericOrders t n p f).2 := by
    rcases hPU.1 with rfl | rfl
    · exact hle 1 le_rfl (by norm_num)
    · exact hle 1 le_rfl (by norm_num)
  have hK := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.rank_ge_of_model hGA hperf hr hr2
    (GL83.I243.Cover.isPGroup_center_quotient hq) (eK.trans eB.symm)
    (CFSG.Models.LieModel.of_blueprint hcl hX) hPU.1 hn hrg hb (hle _ he1 he1') (hle _ he2 he2')
  have hcop : r.Coprime
      (Nat.card (QuotientGroup.mk' (GL83.I243.Cover.primeCentre r (Bar2 L))).ker) := by
    rw [QuotientGroup.ker_mk']
    exact GL83.I243.Cover.coprime_card_primeCentre
  have hK' : n - 2 ≤ CFSG.pRank r (Bar2 L) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel r hr _
        (QuotientGroup.mk'_surjective _) hcop]
    exact hK
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  exact uc22s2112r2_le_pRank (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) hker hr hr2 hK'

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
