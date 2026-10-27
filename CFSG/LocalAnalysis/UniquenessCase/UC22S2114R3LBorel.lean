module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusEightOutOrderHolds
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)
open CFSG.AGLEmbedding.ParabHub (BorelQuotient)
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3l_dvd_of_borelQuotient {K Y : Type} [Group K] [Finite K] [Group Y]
    [Finite Y] {D : CFSG.LieType.Universal.UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ} (h : BorelQuotient D n H π M)
    (S : Sylow 2 Y) {y : Y} (hy : y ∈ normalizer ((S : Subgroup Y) : Set Y)) (hy1 : y ≠ 1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1) : r ∣ M := by
  obtain ⟨π', hπ', hker, hS⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { h with
      surj := hπ'
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  rw [hS, hQ.normalizer_map_posUnipotent] at hy
  have : Fact r.Prime := ⟨hr⟩
  refine CFSG.AGLEmbedding.ParabPrime.dvd_of_dvd_card_map_borel hQ.ct hQ.extras hQ.pGroup π'
    (fun t ht => hQ.pow_eq_one_of_mem_iSup ht) hr hr2 ?_
  rw [← orderOf_eq_prime hyr hy1]
  exact Subgroup.orderOf_dvd_natCard _ hy

theorem uc22s2114r3l_dvd_of_mem_normalizer {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hY : LieModel Y .PSL 4 2 f ∨ LieModel Y .PSp 3 2 f ∨ IsOmega8m Y f) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) {y : Y} (hy : y ∈ normalizer (U : Set Y)) (hy1 : y ≠ 1) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1) : r ∣ 2 ^ (2 * f) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  have hyS : y ∈ normalizer (((hU.2.1.toSylow hidx : Sylow 2 Y) : Subgroup Y) : Set Y) := hy
  have hsq : (2 ^ f) ^ 2 - 1 = 2 ^ (2 * f) - 1 := by rw [← pow_mul, mul_comm]
  have hsub : 2 ^ f - 1 ∣ 2 ^ (2 * f) - 1 :=
    hsq ▸ CFSG.AGLEmbedding.ParabHub.sub_one_dvd_sq_sub_one (2 ^ f)
  rcases hY with hY | hY | hY
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hY (by decide)
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
    refine (uc22s2114r3l_dvd_of_borelQuotient (CFSG.AGLEmbedding.ParabHub.borelQuotient_sl
      (m := 3) ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).trans
        e.symm)) _ hyS hy1 hr hr2 hyr).trans ?_
    rwa [hF]
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hY (by decide)
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
    refine (uc22s2114r3l_dvd_of_borelQuotient (CFSG.AGLEmbedding.ParabHub.borelQuotient_sp e)
      _ hyS hy1 hr hr2 hyr).trans ?_
    rwa [hF]
  · have hY' : LieModel Y .POmegaMinus 4 2 f := hY
    obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := LieModel.statedClassicalModel hY' (by decide)
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
    have := CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus (n := 4) hirr)
    refine (uc22s2114r3l_dvd_of_borelQuotient
      (CFSG.AGLEmbedding.ParabHub.borelQuotient_spinMinus hirr le_rfl e)
      _ hyS hy1 hr hr2 hyr).trans ?_
    rw [hF, hsq]

theorem uc22s2114r3l_inner {X : Type} [Group X] [Finite X] {f r : ℕ}
    (hX : LieModel X .PSL 4 2 f ∨ LieModel X .PSp 3 2 f ∨ IsOmega8m X f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrf : ¬ r ∣ f) {α : MulAut X} (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  have hm : Nat.card (Outer X) ∣ 2 * f * 4 := by
    rcases hX with hX | hX | hX
    · exact (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (Or.inl rfl) (by norm_num) Nat.prime_two (LieModel.admissible hX).2.1
        (LieModel.statedClassicalModel hX (by decide))).1.trans
        (Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 4 _))
    · exact (PartTwo.Inputs1719.k_SpSixOutOrder_holds hX).trans (dvd_mul_right _ _)
    · exact (PartTwo.Inputs1719.k_OmegaMinusEightOutOrder_holds X f hX).trans
        (dvd_mul_right _ _)
  have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  refine uc22p2214_out_mem_of_card_dvd hm hr (fun hd => ?_) hα
  rcases (Nat.Prime.dvd_mul hr).1 hd with h2f | h4
  · rcases (Nat.Prime.dvd_mul hr).1 h2f with h | h
    · exact h2 h
    · exact hrf h
  · exact h2 (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 from h4))

theorem uc22s2114r3l_dvd_of_borel {M L T : Subgroup G} (hL : L ∈ calC M)
    (hTL : IsSylowOf 2 (T ⊓ L) L) {f : ℕ}
    (hX : LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f)
    {b : G} (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (T : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrf : ¬ r ∣ f) (hbr : b ^ r = 1)
    (hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1) : r ∣ 2 ^ (2 * f) - 1 := by
  obtain ⟨U, hU, y, hy, hy1, hyr⟩ := uc22s2114_exists_of_borel hL hTL hbL hbT hbr hb1
    fun _ hα => uc22s2114r3l_inner hX hr hr2 hrf hα
  exact uc22s2114r3l_dvd_of_mem_normalizer hX hU hy hy1 hr hr2 hyr

end CFSG.LocalAnalysis.UniquenessCase.UC22
