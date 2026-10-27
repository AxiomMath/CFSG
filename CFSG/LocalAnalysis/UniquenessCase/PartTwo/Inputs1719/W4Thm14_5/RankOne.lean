module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Blueprint (LieModel)

private def RankOneOrder (m N : ℕ) : Prop :=
  1 ≤ N ∧ (∃ r, Odd r ∧ m = 2 ^ N * r) ∧
    (2 * N ≠ 6 → ∃ p, IsPrimitivePrimeDivisor p (2 * N) ∧ p ∣ m)

private def LowOrder (m N : ℕ) : Prop :=
  N ≠ 3 ∧ (∃ r, Odd r ∧ m = 2 ^ N * r) ∧
    (∀ p j, IsPrimitivePrimeDivisor p j → 0 < j → p ∣ m → j ≤ N) ∧ 3 ∣ m

private theorem false_of_rankOneOrder_of_lowOrder {m N N' : ℕ} (h : RankOneOrder m N)
    (h' : LowOrder m N') : False := by
  obtain ⟨hN, ⟨r, hr, hm⟩, hp⟩ := h
  obtain ⟨h3, ⟨r', hr', hm'⟩, hb, -⟩ := h'
  have hNN : N = N' := eq_of_two_pow_mul_odd hr hr' (hm.symm.trans hm')
  subst hNN
  obtain ⟨p, hp, hpm⟩ := hp (by omega)
  have := hb p (2 * N) hp (by omega) hpm
  omega

private theorem rankOneOrder_of_isL2 {X : Type} [Group X] {e : ℕ} (h : IsL2 X e) :
    RankOneOrder (Nat.card X) e := by
  have he : 1 ≤ e := h.admissible.2.1
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
  refine ⟨he, ⟨_, odd_pow_sub_one (by omega) two_pos, hcard⟩, fun h6 => ?_⟩
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (by omega : 2 ≤ 2 * e) h6
  refine ⟨p, hp, ?_⟩
  rw [hcard, ← pow_mul, mul_comm e 2]
  exact dvd_mul_of_dvd_right hp.dvd _

private theorem rankOneOrder_of_ordTwistedA {m e c : ℕ} (he : 1 ≤ e) (hc : Odd c)
    (hm : m = ordTwistedA 2 (2 ^ e) * c) : RankOneOrder m (e * 3) := by
  have hP := profile_ordTwistedA (n := 2) (g := e) le_rfl he
  rw [show e * (2 * (2 + 1) / 2) = e * 3 by norm_num] at hP
  obtain ⟨r, hr, hord⟩ := hP.two
  refine ⟨by omega, ⟨r * c, hr.mul hc, by rw [hm, hord, mul_assoc]⟩, fun h6 => ?_⟩
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (by omega : 2 ≤ 2 * (e * 3)) h6
  have htop := zU_top (n := 2) (g := e) (t := 1) (Or.inl rfl) le_rfl (by omega)
  rw [show 2 * (e * (2 * 1 + 1)) = 2 * (e * 3) by norm_num] at htop
  refine ⟨p, hp, ?_⟩
  rw [hm]
  exact dvd_mul_of_dvd_left ((hP.prim p _ hp (by omega)).mpr htop) _

private theorem rankOneOrder_of_isU3 {X : Type} [Group X] {e : ℕ} (h : IsU3 X e) :
    RankOneOrder (Nat.card X) (e * 3) := by
  have hcard : Nat.card X = ordTwistedA 2 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  exact rankOneOrder_of_ordTwistedA h.admissible.2.1 odd_one (by rw [hcard, mul_one])

private theorem rankOneOrder_of_isSU3 {X : Type} [Group X] {e : ℕ} (h : IsSU3 X e)
    (hZ : Odd (Nat.card (center X))) : RankOneOrder (Nat.card X) (e * 3) := by
  have hcard : Nat.card (X ⧸ center X) = ordTwistedA 2 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.2.card_eq_lieOrd (by norm_num)
  exact rankOneOrder_of_ordTwistedA h.2.admissible.2.1 hZ
    (by rw [← hcard]; exact (center X).card_eq_card_quotient_mul_card_subgroup)

private theorem lowOrder_of_mul {f c F : ℕ} (hF : Odd F) (hN : f * c ≠ 3) (h3 : 3 ∣ F)
    (hb : ∀ p j, IsPrimitivePrimeDivisor p j → 0 < j → p ∣ F → j ≤ f * c) :
    LowOrder ((2 ^ f) ^ c * F) (f * c) := by
  refine ⟨hN, ⟨F, hF, by rw [← pow_mul]⟩, fun p j hp hj hpm => hb p j hp hj ?_,
    dvd_mul_of_dvd_right h3 _⟩
  rcases hp.prime.dvd_mul.mp hpm with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow (hp.prime.dvd_of_dvd_pow h2))) (hp.ne_two hj)
  · exact h2

private theorem lowOrder_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hN : N ≠ 3)
    (hb : ∀ j, Z j → j ≤ N) (h3 : 3 ∣ m) : LowOrder m N :=
  ⟨hN, h.two, fun p j hp hj hpm => hb j ((h.prim p j hp hj).mp hpm), h3⟩

private theorem le_of_dvd_pow_sub_one {p j f a : ℕ} (hp : IsPrimitivePrimeDivisor p j)
    (hj : 0 < j) (hf : 0 < f) (ha : 0 < a) (h : p ∣ (2 ^ f) ^ a - 1) : j ≤ f * a :=
  Nat.le_of_dvd (Nat.mul_pos hf ha) ((PrimDiv.dvd_pow_sub_one_iff hp hj f a).mp h)

private theorem le_of_dvd_pow_add_one {p j f a : ℕ} (hp : IsPrimitivePrimeDivisor p j)
    (hj : 0 < j) (hf : 0 < f) (ha : 0 < a) (h : p ∣ (2 ^ f) ^ a + 1) : j ≤ 2 * (f * a) :=
  Nat.le_of_dvd (by positivity) ((PrimDiv.dvd_pow_add_one_iff hp hj f a).mp h).1

private theorem lowOrder_of_isOmegaPlus_four {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : IsOmegaPlus X 4 k) : LowOrder (Nat.card X) (k * 2) := by
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  rw [Om8Excl.card_isOmegaPlus_four hk h, mul_pow, h4]
  refine lowOrder_of_mul (odd_pow_sub_one (by omega) two_pos).pow (by omega)
    (dvd_pow (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_two_pow_sq_sub_one k)
      two_ne_zero) fun p j hp hj hpF => ?_
  exact le_of_dvd_pow_sub_one hp hj (by omega) two_pos (hp.prime.dvd_of_dvd_pow hpF)

private theorem lowOrder_of_isSp4 {X : Type} [Group X] {k : ℕ} (h : IsSp4 X k) :
    LowOrder (Nat.card X) (k * (2 * 2)) := by
  have hk : 1 ≤ k := h.admissible.2.1
  have hcard : Nat.card X = ordBC 2 (2 ^ k) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  rw [hcard]
  exact lowOrder_of_profile (profile_ordBC hk) (by omega) (fun j hj => zBC_le (by omega) hj)
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordBC (by norm_num))

private theorem lowOrder_of_isSLn_three {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : IsSLn X 3 k) : LowOrder (Nat.card X) (k * 3) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hKcard]
  refine lowOrder_of_mul ((odd_pow_sub_one (by omega) two_pos).mul
      (odd_pow_sub_one (by omega) three_pos)) (by omega)
    (dvd_mul_of_dvd_left
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_two_pow_sq_sub_one k) _)
    fun p j hp hj hpF => ?_
  rcases hp.prime.dvd_mul.mp hpF with h2 | h3
  · exact (le_of_dvd_pow_sub_one hp hj (by omega) two_pos h2).trans (by omega)
  · exact le_of_dvd_pow_sub_one hp hj (by omega) three_pos h3

private theorem lowOrder_two_three_four {f F₃ : ℕ} (hf : 1 ≤ f) (hF₃ : Odd F₃)
    (hb : ∀ p j, IsPrimitivePrimeDivisor p j → 0 < j → p ∣ F₃ → j ≤ f * 6) :
    LowOrder ((2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * F₃ * ((2 ^ f) ^ 4 - 1))) (f * 6) := by
  refine lowOrder_of_mul (((odd_pow_sub_one (by omega) two_pos).mul hF₃).mul
      (odd_pow_sub_one (by omega) four_pos)) (by omega)
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_two_pow_sq_sub_one f) _) _)
    fun p j hp hj hpF => ?_
  rcases hp.prime.dvd_mul.mp hpF with h23 | h4
  · rcases hp.prime.dvd_mul.mp h23 with h2 | h3
    · exact (le_of_dvd_pow_sub_one hp hj (by omega) two_pos h2).trans (by omega)
    · exact hb p j hp hj h3
  · exact (le_of_dvd_pow_sub_one hp hj (by omega) four_pos h4).trans (by omega)

private theorem lowOrder_two_three_four_sub {f : ℕ} (hf : 1 ≤ f) :
    LowOrder ((2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1)))
      (f * 6) :=
  lowOrder_two_three_four hf (odd_pow_sub_one (by omega) three_pos) fun _ _ hp hj h3 =>
    (le_of_dvd_pow_sub_one hp hj (by omega) three_pos h3).trans (by omega)

private theorem lowOrder_two_three_four_add {f : ℕ} (hf : 1 ≤ f) :
    LowOrder ((2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)))
      (f * 6) :=
  lowOrder_two_three_four hf (odd_pow_add_one (by omega) three_pos) fun _ _ hp hj h3 =>
    (le_of_dvd_pow_add_one hp hj (by omega) three_pos h3).trans (by omega)

private theorem lowOrder_of_isSUn_four {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (h : IsSUn X 4 a) : LowOrder (Nat.card X) (a * 6) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hKcard),
    show ∀ x y z w : ℕ, x * y * z * w = x * (y * z * w) from fun _ _ _ _ => by ring]
  exact lowOrder_two_three_four_add ha

private theorem lowOrder_of_isOmegaMinus_six {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsOmegaMinus X 6 k) : LowOrder (Nat.card X) (k * 6) := by
  obtain ⟨-, K, _, _, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadMinus 3 K b c v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by norm_num⟩ : Fin (3 - 1))
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) hv,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr,
    CFSG.SeitzReduction.F4Pilot.ordSU_four, hKcard]
  exact lowOrder_two_three_four_add hk

private theorem lowOrder_of_isSLn_four {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsSLn X 4 k) : LowOrder (Nat.card X) (k * 6) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four, hKcard,
    show ∀ x y z w : ℕ, x * y * z * w = x * (y * z * w) from fun _ _ _ _ => by ring]
  exact lowOrder_two_three_four_sub hk

private theorem lowOrder_of_isOmegaPlus_six {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : IsOmegaPlus X 6 k) : LowOrder (Nat.card X) (k * 6) := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadPlus 3 K v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K) hv,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three h4,
    CFSG.SeitzReduction.F4Pilot.ordSL_four, hKcard]
  exact lowOrder_two_three_four_sub (by omega)

private theorem lowOrder_of_isSpn_six {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsSpn X 6 k) : LowOrder (Nat.card X) (k * 9) := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 3, hKcard,
    show (3 : ℕ) ^ 2 = 9 from rfl]
  refine lowOrder_of_mul (odd_prod fun i hi => odd_pow_sub_one (by omega) (by simp at hi; omega))
    (by omega) ((CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_two_pow_sq_sub_one
      k).trans (Finset.dvd_prod_of_mem (fun i => (2 ^ k) ^ (2 * i) - 1)
        (by simp : 1 ∈ Finset.Icc 1 3))) fun p j hp hj hpF => ?_
  obtain ⟨i, hi, hpi⟩ := ((Nat.Prime.prime hp.prime).dvd_finsetProd_iff _).mp hpF
  simp only [Finset.mem_Icc] at hi
  exact (le_of_dvd_pow_sub_one hp hj (by omega) (by omega) hpi).trans
    (Nat.mul_le_mul_left _ (by omega))

private theorem lowOrder_of_isOmega8m {X : Type} [Group X] {k : ℕ} (h : IsOmega8m X k) :
    LowOrder (Nat.card X) (k * (4 * (4 - 1))) := by
  have hk : 1 ≤ k := h.admissible.2.1
  have hcard : Nat.card X = ordTwistedD 4 (2 ^ k) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  rw [hcard]
  exact lowOrder_of_profile (profile_ordTwistedD (by norm_num) hk) (by omega)
    (fun j hj => (z2D_le (by omega) (by norm_num) hj).trans (by omega))
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordTwistedD (by norm_num))

private theorem odd_card_center_of_isSimpleGroup {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hq : CFSG.Open.IsQuasisimple X) : Odd (Nat.card (center X)) := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · rw [h, Subgroup.card_bot]
    exact odd_one
  · have : IsSimpleGroup (X ⧸ center X) := hq.2
    have : Subsingleton (X ⧸ center X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact (false_of_nontrivial_of_subsingleton (X ⧸ center X)).elim

private theorem odd_card_statedScalars_subgroupOf {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (G : Subgroup (GL ι K)) :
    Odd (Nat.card ↥((StatedScalars ι K).subgroupOf G)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, pow_zero] at h1
      omega
    · exact h
  have h1 : Nat.card ↥((StatedScalars ι K).subgroupOf G) ∣ Nat.card ↥(StatedScalars ι K) := by
    rw [← Subgroup.card_map_of_injective G.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(StatedScalars ι K) ∣ Nat.card Kˣ :=
    Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar ι)
  rw [Nat.card_units, hK] at h2
  exact Odd.of_dvd_nat (odd_two_pow_sub_one hn) (h1.trans h2)

private theorem odd_card_center_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Odd (Nat.card (center Y))) : Odd (Nat.card (center X)) := by
  rwa [Nat.card_congr (Subgroup.centerCongr e).toEquiv]

private theorem odd_card_center_of_isSLn {X : Type} [Group X] {d k : ℕ} (h : IsSLn X d k) :
    Odd (Nat.card (center X)) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  refine odd_card_center_of_mulEquiv e ?_
  rw [CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq d]
  exact odd_card_statedScalars_subgroupOf hKcard _

private theorem odd_card_center_of_isSUn_four {X : Type} [Group X] {a : ℕ} (h : IsSUn X 4 a) :
    Odd (Nat.card (center X)) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((4 : ℕ), 2 ^ a) ≠ (3, 2) := fun hpair =>
    absurd (congrArg Prod.fst hpair) (by norm_num)
  refine odd_card_center_of_mulEquiv e ?_
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := a) (F := K)
    (n := 4) hKcard (by norm_num) hne).2]
  exact odd_card_statedScalars_subgroupOf (n := a * 2) (by rw [hKcard, ← pow_mul]) _

private theorem odd_card_center_of_isSpn {X : Type} [Group X] {m k : ℕ} (h : IsSpn X m k) :
    Odd (Nat.card (center X)) := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := h
  refine odd_card_center_of_mulEquiv e ?_
  rw [CFSG.LieType.Universal.Symplectic.center_eq (m / 2) K]
  exact odd_card_statedScalars_subgroupOf hKcard _

open CFSG.ComponentClassification.RankTwoClassical.ORigid in
private theorem isSimpleGroup_of_isOmegaMinus_six {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaMinus X 6 k) : IsSimpleGroup X := by
  obtain ⟨-, K, _, _, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadMinus 3 K b c v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by norm_num⟩ : Fin (3 - 1))
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedOmega (StatedQuadMinus 3 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr (e.trans eΩ)).mpr
    (isSimpleGroup_statedOmega_quadMinus_of_two_le (by norm_num) hirr)

private theorem isSimpleGroup_of_isOmegaPlus_six {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaPlus X 6 k) : IsSimpleGroup X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  exact (MulEquiv.isSimpleGroup_congr e).mpr
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := K)
      (n := 3) le_rfl)

private theorem false_of_rankOne {X : Type} [Group X] {e N : ℕ}
    (hshape : IsL2 X e ∨ IsSz X e ∨ IsU3 X e ∨ IsSU3 X e) (hlow : LowOrder (Nat.card X) N)
    (hZ : CFSG.Open.IsQuasisimple X → Odd (Nat.card (center X))) : False := by
  rcases hshape with h | h | h | h
  · exact false_of_rankOneOrder_of_lowOrder (rankOneOrder_of_isL2 h) hlow
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h hlow.2.2.2
  · exact false_of_rankOneOrder_of_lowOrder (rankOneOrder_of_isU3 h) hlow
  · exact false_of_rankOneOrder_of_lowOrder (rankOneOrder_of_isSU3 h (hZ h.1)) hlow

theorem natural_of_rankOne {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {e k : ℕ}
    (hshape : IsL2 ↥H e ∨ IsSz ↥H e ∨ IsU3 ↥H e ∨ IsSU3 ↥H e) (hk : 2 ≤ k)
    (hnat : IsNaturalClassicalModule H k) :
    (IsL2 ↥H k ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 k) ∨
      (IsOmegaMinus ↥H 4 k ∧ NatOmegaMinus H ⊤ ⊥ 4 k) := by
  rcases hnat with h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨a, rfl, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (false_of_rankOne hshape (lowOrder_of_isOmegaPlus_four hk h) fun hq =>
      absurd hq (C163.not_isQuasisimple_of_isOmegaPlus_four hk h)).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isSp4 h) fun hq =>
      odd_card_center_of_isSimpleGroup
        (LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) h) hq).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isSLn_three hk h) fun _ =>
      odd_card_center_of_isSLn h).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isSUn_four (by omega) h) fun _ =>
      odd_card_center_of_isSUn_four h).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isOmegaMinus_six (by omega) h) fun hq =>
      odd_card_center_of_isSimpleGroup (isSimpleGroup_of_isOmegaMinus_six h) hq).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isSLn_four (by omega) h) fun _ =>
      odd_card_center_of_isSLn h).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isOmegaPlus_six hk h) fun hq =>
      odd_card_center_of_isSimpleGroup (isSimpleGroup_of_isOmegaPlus_six h) hq).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isSpn_six (by omega) h) fun _ =>
      odd_card_center_of_isSpn h).elim
  · exact (false_of_rankOne hshape (lowOrder_of_isOmega8m h) fun hq =>
      odd_card_center_of_isSimpleGroup
        (LieModel.isSimpleGroup_of_mem_classicalTags (t := .POmegaMinus) (by decide) h) hq).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
