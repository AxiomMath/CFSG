module

public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineOrbit
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors card_pow_four_le
  genericOrders_fst_pos genericOrders_snd_le exceptionalOrders_le torsBound_le_of_five_le
  eq_psu_four_three_of_nine_le)

open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplier_le_center hopfMultiplierToKer
  hopfMultiplierToKer_surjective hopfMultiplierEquivGriess centralQuotientMap
  centralQuotientMap_surjective centralQuotientMap_ker)


theorem card_torsion_center_le_of_perfect {K S : Type} [Group K] [Finite K] [Group S]
    (hK : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* S) [Finite (hopfMultiplier S)]
    (r : ℕ) :
    Nat.card {z : Subgroup.center K // z ^ r = 1} ≤
      Nat.card {m : hopfMultiplier S // m ^ r = 1} := by
  have : Group.IsPerfect K := ⟨hK⟩
  have hker := centralQuotientMap_ker e
  have hle := CFSG.AGLEmbedding.CompCenterNine.card_pow_eq_one_le_of_surjective
    (fun a b : hopfMultiplier S =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center b.2) a))
    (hopfMultiplierToKer (centralQuotientMap e) (centralQuotientMap_surjective e) hker.le)
    (hopfMultiplierToKer_surjective _ _ _) r
  refine le_trans (le_of_eq (Nat.card_congr ((MulEquiv.subgroupCongr hker.symm).toEquiv.subtypeEquiv
    fun z => ?_))) hle
  change z ^ r = 1 ↔ MulEquiv.subgroupCongr hker.symm z ^ r = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem finite_and_torsion_le_native {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n p f)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f))
    {r : ℕ} (hr : r.Prime) :
    Finite (hopfMultiplier X) ∧
      Nat.card {m : hopfMultiplier X // m ^ r = 1} ≤ torsBound r t n p f := by
  obtain ⟨eg⟩ := hT
  have ha := genericOrders_fst_pos hm.admissible
  obtain ⟨hb, -⟩ := genericOrders_snd_le t n p f
  obtain ⟨⟨hc, -⟩, ⟨hd, -⟩⟩ := exceptionalOrders_le t n p f
  have : NeZero (genericOrders t n p f).1 := ⟨ha.ne'⟩
  have : NeZero (genericOrders t n p f).2 := ⟨hb.ne'⟩
  have : NeZero (exceptionalOrders t n p f).1 := ⟨hc.ne'⟩
  have : NeZero (exceptionalOrders t n p f).2 := ⟨hd.ne'⟩
  let e : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  refine le_trans (le_of_eq (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)))
    (card_pow_four_le hr ha hb hc hd)
  change m ^ r = 1 ↔ e m ^ r = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem center_torsion_le_native {K X : Type} [Group K] [Finite K] [Group X]
    (hK : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n p f)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f))
    {r : ℕ} (hr : r.Prime) :
    Nat.card {z : Subgroup.center K // z ^ r = 1} ≤ torsBound r t n p f := by
  obtain ⟨hfin, hM⟩ := finite_and_torsion_le_native hm hT hr
  have := hfin
  exact (card_torsion_center_le_of_perfect hK e r).trans hM

theorem torsBound_three_le_of_ne_psu {t : StatedLieTag} {n p f : ℕ}
    (h : ¬ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1)) : torsBound 3 t n p f ≤ 3 := by
  by_contra hlt
  refine h (eq_psu_four_three_of_nine_le ?_)
  revert hlt
  unfold torsBound tors
  split_ifs <;> omega

theorem not_mark_psu_four_three (lab : LargeEvenLabel) :
    ¬ (markTag lab = .PSU ∧ markRank lab = 4 ∧ markChar lab = 3 ∧ markDeg lab = 1) := by
  obtain ⟨t, l, n⟩ := lab
  rintro ⟨h1, h2, h3, -⟩
  cases t <;> simp_all [markTag, markRank, markChar]

theorem torsBound_mark_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel) :
    torsBound p (markTag lab) (markRank lab) (markChar lab) (markDeg lab) ≤ p := by
  by_cases hp5 : 5 ≤ p
  · exact torsBound_le_of_five_le hp5 _ _ _ _
  obtain rfl : p = 3 := by
    have h3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  exact torsBound_three_le_of_ne_psu (not_mark_psu_four_three lab)

section Certs


theorem ggLabelCenterPCyclicInput_holds : GGLabelCenterPCyclicInput := by
  intro p hp hp2 lab hlab K _ _ hK hl E hEZ hEab
  by_cases hn : Nontrivial (K ⧸ Subgroup.center K)
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hK hn
    obtain ⟨R, _, I, F, ⟨e⟩, hm⟩ := largeEvenRawDatum_exists
      (largeEvenRawDatum_markedModel hlab
        (Q := fun R' _ _ _ => Nonempty (K ⧸ Subgroup.center K ≃* R'))
        (by
          rintro R _ I F ⟨e⟩
          exact nonabelian_of_mulEquiv e ⟨a, b, hab⟩)
        hl)
    have hM : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv e.symm hm
    obtain ⟨-, hT⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hle := center_torsion_le_native hK (MulEquiv.refl _) hM hT hp
    have hcard : Nat.card E ≤ Nat.card {z : Subgroup.center K // z ^ p = 1} := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨⟨x.1, hEZ x.2⟩, Subtype.ext (hEab.2 x.1 x.2)⟩) ?_
      intro x y hxy
      exact Subtype.ext (congrArg (fun w : {z : Subgroup.center K // z ^ p = 1} => (w.1 : K)) hxy)
    exact hcard.trans (hle.trans (torsBound_mark_le hp hp2 lab))
  · have hZ : Subgroup.center K = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      have : Subsingleton (K ⧸ Subgroup.center K) := not_nontrivial_iff_subsingleton.mp hn
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    have : Group.IsPerfect K := ⟨hK⟩
    have : IsMulCommutative K := Subgroup.center_eq_top_iff.mp hZ
    have : Subsingleton K := inferInstance
    exact (Finite.card_le_one_iff_subsingleton.mpr inferInstance).trans hp.one_lt.le

end Certs

end CFSG.StandardType

end
