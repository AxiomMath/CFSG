module

public import CFSG.RankThree.PartTwo.KFacts.K71Item83PSU3
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartTwo.Census.Suzuki
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)
open Matrix

theorem card_unitaryPSU_three_eq {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    Nat.card (unitaryPSU h 3) = ordTwistedA 2 (2 ^ f) := by
  rw [Nat.card_congr (unitaryPSUEquiv h (by norm_num)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two h.one_le
      h.card_eq_sq (by norm_num), ordTwistedA]

theorem ne_ordTwistedA_two {N r m : ℕ} (hr : Odd r) (hN : Even N) (hm : Odd m) :
    2 ^ N * r ≠ ordTwistedA 2 (2 ^ m) := by
  intro h
  obtain ⟨s, hs, hseq⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := m) le_rfl hm.pos).two
  rw [hseq] at h
  have h1 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs h
  norm_num at h1
  rw [h1] at hN
  exact (Nat.not_even_iff_odd.mpr (hm.mul (by decide))) hN

theorem eq_of_ordTwistedA_two_eq {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordTwistedA 2 (2 ^ f) = ordTwistedA 2 (2 ^ g)) : f = g := by
  obtain ⟨r, hr, hreq⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := f) le_rfl hf).two
  obtain ⟨s, hs, hseq⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := g) le_rfl hg).two
  rw [hreq, hseq] at h
  have h1 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs h
  norm_num at h1
  exact h1

theorem card_psl_eq_ordA {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin n) K) = ordA (n - 1) (2 ^ f) := by
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj n K).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hn, hK, ordA,
    show n - 1 + 1 = n by omega]
  congr 2
  rw [mul_comm]

theorem exists_card_eq_two_pow {K : Type} [Field K] [Finite K] (hK : ringChar K = 2) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have : CharP K 2 := ringChar.of_eq hK
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem card_statedProj_statedSp_eq_ordBC {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (r : ℕ) :
    Nat.card (StatedProj (StatedSp r K)) = ordBC r (2 ^ f) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK, ordBC,
    show Nat.gcd 2 (2 ^ f - 1) = 1 from
      Nat.Coprime.symm ((CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hf).coprime_two_right),
    Nat.div_one, sq]

theorem center_eq_bot_of_mulEquiv_fwd {X M : Type*} [Group X] [Group M] (e : X ≃* M)
    (hX : Subgroup.center X = ⊥) : Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  by_contra hz1
  exact false_of_center_eq_bot_of_mulEquiv e.symm hX hz hz1

theorem odd_sub_add_one {x y : ℕ} (hyx : y ≤ x) (hx : Even x) (hy : Even y) : Odd (x - y + 1) :=
  ((Nat.even_sub hyx).mpr (iff_of_true hx hy)).add_one

theorem exists_two_part_ree {q f : ℕ} (hq : q = 2 ^ f) (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) = 2 ^ (f * 12) * r := by
  have he : Even q := hq ▸ Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq1 : 1 ≤ q := hq ▸ Nat.one_le_two_pow
  have he2 : Even (q ^ 2) := Nat.even_pow.mpr ⟨he, by norm_num⟩
  have he4 : Even (q ^ 4) := Nat.even_pow.mpr ⟨he, by norm_num⟩
  refine ⟨(q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1),
    ?_, ?_⟩
  · have h1 : Odd (q - 1) := hq ▸ CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hf
    have h2 : Odd (q + 1) := he.add_one
    have h3 : Odd (q ^ 2 + 1) := he2.add_one
    have h4 : Odd (q ^ 2 - q + 1) := odd_sub_add_one (Nat.le_self_pow (by norm_num) q) he2 he
    have h5 : Odd (q ^ 4 - q ^ 2 + 1) :=
      odd_sub_add_one (Nat.pow_le_pow_right hq1 (by norm_num)) he4 he2
    exact ((((h1.pow).mul h2.pow).mul h3.pow).mul h4).mul h5
  · rw [pow_mul, ← hq]
    ring

open CFSG.LieType.Chevalley in
@[expose] def OddCharStdModel (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 2 ∧
    (Nonempty (X ≃* PSL2 K) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (X ≃* LinearFlag.projectiveSL n K)) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (X ≃* SpecialLinearGroup (Fin n) K)) ∨
      (∃ r : ℕ, 2 ≤ r ∧ Nonempty (X ≃* StatedProj (StatedSp r K))) ∨
      Nonempty (X ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K) ∨
      ∃ (p f : ℕ) (h : UnitaryFieldData p f K),
        Nonempty (X ≃* unitaryPSU h 3) ∨ Nonempty (X ≃* unitarySU p f K 3))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducesKindPSU3_or_oddCharStdModel {m : ℕ} (hm : Odd m)
    (hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordTwistedA 2 (2 ^ m))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {x : G} {k : AutKind}
    (hx : InducesStdKind L x k) :
    (∃ (K : Type) (_ : Field K) (hK : UnitaryFieldData 2 m K) (_ : 2 < 2 ^ m),
      InducesKindPSU3 hK L x k) ∨ OddCharStdModel (L ⧸ aschbacherSolvableCore 3 L) := by
  have hm1 : 1 ≤ m := hm.pos
  have hM : ∀ {M : Type} [Group M], (L ⧸ aschbacherSolvableCore 3 L ≃* M) →
      Nat.card M = ordTwistedA 2 (2 ^ m) := fun e => (Nat.card_congr e.toEquiv).symm.trans hcard
  cases hx with
  | psl2 K h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [card_psl_eq_ordA (by norm_num) hKf] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) hf le_rfl hm1 h1).elim
    · exact Or.inr ⟨K, inferInstance, inferInstance, hK2, Or.inl ⟨e⟩⟩
  | psl n K hn h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).toEquiv,
        card_psl_eq_ordA (by omega) hKf] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by omega) hf le_rfl hm1 h1).elim
    · exact Or.inr ⟨K, inferInstance, inferInstance, hK2, Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)⟩
  | sl n K hn h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have hZ' : Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ :=
        center_eq_bot_of_mulEquiv_fwd e hZ
      have hc1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) = 1 := by
        rw [hZ', Subgroup.card_bot]
      have h1 := hM e
      have h2 : Nat.card (SpecialLinearGroup (Fin n) K) =
          Nat.card (ProjectiveSpecialLinearGroup (Fin n) K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (SpecialLinearGroup (Fin n) K)), hc1, mul_one]
      rw [h2, card_psl_eq_ordA (by omega) hKf] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by omega) hf le_rfl hm1 h1).elim
    · exact Or.inr ⟨K, inferInstance, inferInstance, hK2, Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩))⟩
  | @psu3 p f K _ hK hq h =>
    by_cases hp : p = 2
    · subst hp
      obtain ⟨e, -⟩ := id h
      have h1 := hM e
      rw [card_unitaryPSU_three_eq hK] at h1
      obtain rfl := eq_of_ordTwistedA_two_eq hK.one_le hm1 h1
      exact Or.inl ⟨K, inferInstance, hK, hq, h⟩
    · obtain ⟨e, -⟩ := h
      have := hK.finite
      have : CharP K p := hK.charP
      exact Or.inr ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inl ⟨e⟩⟩))))⟩
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hp : p = 2
    · subst hp
      have hZ' : Subgroup.center (unitarySU 2 f K 3) = ⊥ := center_eq_bot_of_mulEquiv_fwd e hZ
      by_cases h3 : 3 ∣ 2 ^ f + 1
      · obtain ⟨z, hz, hz1, -⟩ := exists_mem_center_statedSU_ne_one hK h3
        rw [hZ', Subgroup.mem_bot] at hz
        exact (hz1 hz).elim
      · have hsc : Nat.card (unitaryScalars hK 3) = 1 := by
          rw [card_unitaryScalars hK (by norm_num)]
          exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
        have h1 := hM e
        have h2 : Nat.card (unitarySU 2 f K 3) = ordTwistedA 2 (2 ^ f) := by
          rw [← card_unitaryPSU_three_eq hK,
            (unitaryScalars hK 3).card_eq_card_quotient_mul_card_subgroup, hsc, mul_one]
        rw [h2] at h1
        obtain rfl := eq_of_ordTwistedA_two_eq hK.one_le hm1 h1
        exact (h3 (by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hm)).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact Or.inr ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inr ⟨e⟩⟩))))⟩
  | psp r K hr h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · have hr3 : 3 ≤ r := by
        rcases hr with hr | ⟨-, hc⟩
        · exact hr
        · exact (hc hK2).elim
      obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have : CharP K 2 := ringChar.of_eq hK2
      have h1 := hM e
      rw [card_statedProj_statedSp_eq_ordBC hf hKf] at h1
      exact (CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA hr3 hf le_rfl hm1 h1).elim
    · have hr2 : 2 ≤ r := by rcases hr with hr | ⟨rfl, -⟩ <;> omega
      exact Or.inr ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr2, ⟨e⟩⟩)))⟩
  | psp4even F h =>
    obtain ⟨e, -⟩ := h
    obtain ⟨f, hf, hFf⟩ := exists_card_eq_two_pow (ringChar.eq F 2)
    have h1 := hM e
    rw [card_statedProj_statedSp_eq_ordBC hf hFf] at h1
    obtain ⟨r, hr, hreq⟩ := (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hf).two
    rw [hreq] at h1
    exact (ne_ordTwistedA_two hr ⟨f * 2, by ring⟩ hm h1).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hKf,
        CFSG.Timmesfeld.Orders.ordG2_eq] at h1
      exact (ne_ordTwistedA_two ((CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (by norm_num)).mul
        (CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (by norm_num))) ⟨f * 3, by ring⟩ hm h1).elim
    · exact Or.inr ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))⟩
  | sz a K ha hK h =>
    obtain ⟨e, -⟩ := h
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have h1 := hM e
    rw [Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_suzukiMatrixGroup (by omega)] at h1
    have hq : ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) =
        2 ^ ((2 * a + 1) * 2) * (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) := by
      rw [pow_mul]
      ring
    rw [hq] at h1
    exact (ne_ordTwistedA_two ((CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega)
      (by norm_num)).mul (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)))
      ⟨2 * a + 1, by ring⟩ hm h1).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, -, -⟩ := h
    have h1 := hM e
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom
      hσ] at h1
    obtain ⟨r, hr, hreq⟩ := (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two
    rw [hreq] at h1
    exact (ne_ordTwistedA_two hr ⟨f * 6, by ring⟩ hm h1).elim
  | largeRee a ha K hK h =>
    obtain ⟨e, -⟩ := h
    have h1 := hM e
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1] at h1
    obtain ⟨r, hr, hreq⟩ := exists_two_part_ree (q := 2 ^ (2 * a + 1)) rfl (by omega)
    rw [hreq] at h1
    exact (ne_ordTwistedA_two hr ⟨(2 * a + 1) * 6, by ring⟩ hm h1).elim

theorem not_inducesKindPSU3_graphField {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    {x : G} : ¬ InducesKindPSU3 hK L x .graphField := by
  rintro ⟨e, hN, γ, hγ, -⟩
  exact hγ

open CFSG.Assembly.RankThreeEven (projSU) in
theorem exists_data83_of_projSU {A : Subgroup G} {c : G} {a : G}
    (h : Sec8.Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n)))
    (hodd : ¬ OddCharStdModel (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ (A₀ : Subgroup G) (d : G), Sec8.Data83 G c L a A₀ d n := by
  obtain ⟨eL⟩ := hL
  have hn1 : 1 ≤ n := hn.pos
  have h₀ : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  have hq : 2 < 2 ^ (3 * n) := by
    have : 2 ^ 3 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h₀ 3 :=
    eL.trans ((Census.statedSUEquivProjSU 3 2 (3 * n)).symm.trans
      (unitaryPSUEquiv h₀ (by norm_num)).symm) with he
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordTwistedA 2 (2 ^ (3 * n)) :=
    (Nat.card_congr e.toEquiv).trans (card_unitaryPSU_three_eq h₀)
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd e.symm (center_unitaryPSU_three_eq_bot h₀ hq)
  have hm : Odd (3 * n) := Odd.mul (by decide) hn
  rcases h.inducesStdKind with ha | ha
  · rcases inducesKindPSU3_or_oddCharStdModel hm hcard hZ ha with ⟨K, _, hK, hq', hk⟩ | hO
    · exact exists_data83_of_psu3 h hn hK hq' hk
    · exact (hodd hO).elim
  · rcases inducesKindPSU3_or_oddCharStdModel hm hcard hZ ha with ⟨K, _, hK, -, hk⟩ | hO
    · exact (not_inducesKindPSU3_graphField hK hk).elim
    · exact (hodd hO).elim

end CFSG.RankThree.PartTwo.KFacts
