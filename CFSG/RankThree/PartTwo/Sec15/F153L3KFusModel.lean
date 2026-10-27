module

public import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofCore
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Census.Suzuki
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofTransport
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

section FusExclP


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclP

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSU projSL)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4
open Matrix

section Certs


section KindPSL

open Matrix CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)

open CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

private theorem exists_inducesKindPSL_of_inducesStdKind {G : Type} [Group G] [Finite G]
    (L : Subgroup G) (x : G) (n : ℕ) (k : KFacts.AutKind) (hn : Even n) (hn3 : 3 ≤ n)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)))
    (hx : KFacts.InducesStdKind L x k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      KFacts.InducesKindPSL 3 K L x k := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨eL⟩ := hL
  have hcardX : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordA 2 (2 ^ n) :=
    (Nat.card_congr eL.toEquiv).trans (card_projSL_three_galois (by omega))
  have hM : ∀ {M : Type} [Group M], (L ⧸ aschbacherSolvableCore 3 L ≃* M) →
      Nat.card M = ordA 2 (2 ^ n) := fun e => (Nat.card_congr e.toEquiv).symm.trans hcardX
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd (eL.trans (Sec4.projSLEquivProjectiveSL 3 _)).symm
      (Sec21.Item223CensusResProof.center_projectiveSL_three _)
  have hodd := not_oddCharStdModel_of_mulEquiv_projSL hn2 eL
  have h3 : 3 ∣ 2 ^ n - 1 := three_dvd_two_pow_sub_one hn
  cases hx with
  | psl2 K h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [card_psl_eq_ordA (by norm_num) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by norm_num) hf hn2 h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inl ⟨e⟩⟩).elim
  | psl m K hm h =>
    obtain ⟨e, -⟩ := id h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL m K).toEquiv,
        card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, -, hn⟩
      · obtain rfl : m = 3 := by omega
        exact ⟨K, inferInstance, inferInstance, hKf, h⟩
      · omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)⟩).elim
  | sl m K hm h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have hZ' : Subgroup.center (SpecialLinearGroup (Fin m) K) = ⊥ :=
        center_eq_bot_of_mulEquiv_fwd e hZ
      have hc1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin m) K)) = 1 := by
        rw [hZ', Subgroup.card_bot]
      have h1 := hM e
      have h2 : Nat.card (SpecialLinearGroup (Fin m) K) =
          Nat.card (ProjectiveSpecialLinearGroup (Fin m) K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (SpecialLinearGroup (Fin m) K)), hc1, mul_one]
      rw [h2, card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, -, hn⟩
      · obtain rfl : m = 3 := by omega
        exact (Sec21.Item223CensusResProof.center_SL_three_ne_bot (by rw [hKf]; exact h3)
          hZ').elim
      · omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩))⟩).elim
  | @psu3 p f K _ hK hq h =>
    obtain ⟨e, -⟩ := id h
    by_cases hp : p = 2
    · subst hp
      have h1 := hM e
      rw [card_unitaryPSU_three_eq hK] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
        hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inl ⟨e⟩⟩))))⟩).elim
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hp : p = 2
    · subst hp
      have hZ' : Subgroup.center (unitarySU 2 f K 3) = ⊥ := center_eq_bot_of_mulEquiv_fwd e hZ
      by_cases h3' : 3 ∣ 2 ^ f + 1
      · obtain ⟨z, hz, hz1, -⟩ := exists_mem_center_statedSU_ne_one hK h3'
        rw [hZ', Subgroup.mem_bot] at hz
        exact (hz1 hz).elim
      · have hsc : Nat.card (unitaryScalars hK 3) = 1 := by
          rw [card_unitaryScalars hK (by norm_num)]
          exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
        have h1 := hM e
        have h2 : Nat.card (unitarySU 2 f K 3) = ordTwistedA 2 (2 ^ f) := by
          rw [← card_unitaryPSU_three_eq hK,
            (unitaryScalars hK 3).card_eq_card_quotient_mul_card_subgroup, hsc, mul_one]
        rw [h2] at h1
        exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
          hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inr ⟨e⟩⟩))))⟩).elim
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
      exact (ordBC_ne_ordA_two hr3 hf (by omega) h1).elim
    · have hr2 : 2 ≤ r := by rcases hr with hr | ⟨rfl, -⟩ <;> omega
      exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr2, ⟨e⟩⟩)))⟩).elim
  | psp4even F h =>
    obtain ⟨e, -⟩ := h
    obtain ⟨f, hf, hFf⟩ := exists_card_eq_two_pow (ringChar.eq F 2)
    have h1 := hM e
    rw [card_statedProj_statedSp_eq_ordBC hf hFf] at h1
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) (by omega) hf h1.symm).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hKf] at h1
      exact (ordG2_ne_ordA_two hf (by omega) h1).elim
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))⟩).elim
  | sz a K ha hK h =>
    obtain ⟨e, -⟩ := h
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have h1 := hM e
    rw [Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_suzukiMatrixGroup (by omega), suzuki_eq_ordSuzuki] at h1
    exact (ordSuzuki_ne_ordA_two (by omega) (by omega) h1).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, -, -⟩ := h
    have h1 := hM e
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom
      hσ] at h1
    exact (ordTrialityD4_ne_ordA_two hf (by omega) h1).elim
  | largeRee a ha K hK h =>
    obtain ⟨e, -⟩ := h
    have h1 := hM e
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1, ree_native_eq_ordTwistedF4 Nat.one_le_two_pow] at h1
    exact (ordTwistedF4_ne_ordA_two (by omega) (by omega) h1).elim

private theorem inducesKindPSL_galoisField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {k : KFacts.AutKind} (hn : Even n) (hn3 : 3 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n))
    (hx : KFacts.InducesStdKind L x k) : KFacts.InducesKindPSL 3 (GaloisField 2 n) L x k := by
  obtain ⟨K, _, _, hK, hkK⟩ := exists_inducesKindPSL_of_inducesStdKind L x n k hn hn3 ⟨φ⟩ hx
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 n (by omega)]
  exact inducesKindPSL_of_ringEquiv (FiniteField.ringEquivOfCardEq hcard) 3 hkK

end KindPSL

private theorem not_inner_aux {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q}
    {K : Type} [Field K] [Finite K] {q : ℕ}
    (hθ : aschbacherSolvableCore 3 Kg = ⊥)
    (e : ↥Kg ≃* projImage (slPi true 3 q K))
    (hx : x ∈ Subgroup.normalizer (Kg : Set Q))
    (hkP : KFacts.InducesKindPSL 3 K Kg x .field) :
    ¬ ∃ y ∈ glPi true 3 q K, ∀ m : projImage (slPi true 3 q K),
        (slAct e ⟨x, hx⟩ m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  rintro ⟨y, -, hy⟩
  set ψ := pslEquivProjective q K with hψ
  set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
  set α := MulAut.congr ψ (slAct e ⟨x, hx⟩) with hα
  have hind : KFacts.inducedAutHom Kg e' ⟨x, hx⟩ = α :=
    inducedAutHom_thetaBot hθ e ψ ⟨x, hx⟩
  have hcoe : ∀ s : SpecialLinearGroup (Fin 3) K,
      slAct e ⟨x, hx⟩ (slToPsl q K s) = ψ.symm (α (proj 3 K s)) := by
    intro s
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← pslEquivProjective_slToPsl (q := q),
      MulEquiv.symm_apply_apply]
  have hα_pt : ∀ s : SpecialLinearGroup (Fin 3) K,
      α (proj 3 K s) = ψ (slAct e ⟨x, hx⟩ (slToPsl q K s)) := by
    intro s
    rw [hcoe s, MulEquiv.apply_symm_apply]
  have hslAct : ∀ s : SpecialLinearGroup (Fin 3) K,
      slAct e ⟨x, hx⟩ (slToPsl q K s) =
        slToPsl q K
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K y s) := by
    intro s
    apply Subtype.ext
    rw [hy (slToPsl q K s), coe_slToPsl, coe_slToPsl,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
  have hαy : α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y := by
    ext m
    obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 K m
    rw [hα_pt s, hslAct s, pslEquivProjective_slToPsl,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  have hD : α ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 K := by
    rw [hαy]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_linearAutGroup y
  obtain ⟨_, hk⟩ := (KFacts.inducesKindPSL_iff Kg le_rfl e' x .field).mp hkP
  have hτ : KFacts.inducedAutHom Kg e' ⟨x, hx⟩ ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 K := by
    rw [hind]
    exact hD
  have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
  exact hsep.not_mem_inndiag_of_hasKind hk (by decide) (by decide) hτ

theorem not_inner_of_field_plus {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q} {j : ℕ}
    (hjE : Even j) (hj3 : 3 ≤ j) (hθ : aschbacherSolvableCore 3 Kg = ⊥)
    (e : ↥Kg ≃* projImage (slPi true 3 (2 ^ j) (GaloisField 2 j)))
    (hx : x ∈ Subgroup.normalizer (Kg : Set Q)) (hx3 : x ^ 3 = 1)
    (hkind : KFacts.InducesStdKind Kg x .field) :
    ¬ ∃ y ∈ glPi true 3 (2 ^ j) (GaloisField 2 j),
        ∀ m : projImage (slPi true 3 (2 ^ j) (GaloisField 2 j)),
          (slAct e ⟨x, hx⟩ m : ProjGenLinGroup (Fin 3) (GaloisField 2 j)) =
            ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  have hφ : Kg ⧸ aschbacherSolvableCore 3 Kg ≃* projSL 3 (GaloisField 2 j) :=
    (thetaBotEquiv hθ).trans ((e.trans (pslEquivProjective (2 ^ j) (GaloisField 2 j))).trans
      (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 j)).symm)
  exact not_inner_aux hθ e hx (inducesKindPSL_galoisField hjE hj3 hφ hkind)

end Certs

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclP

end FusExclP

section FusExclU


open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclU

section Helpers

variable {K : Type} [Field K] {p f : ℕ}

theorem slAct_suToPsu_of_inner {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q}
    (e : ↥Kg ≃* projImage (slPi false 3 (p ^ f) K)) (hx : x ∈ Subgroup.normalizer (Kg : Set Q))
    (h : UnitaryFieldData p f K) (A : unitaryIsom3 h)
    (hyinner : ∀ m : projImage (slPi false 3 (p ^ f) K),
      (slAct e ⟨x, hx⟩ m : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A : GL (Fin 3) K) * m * (ProjGenLinGroup.mk (A : GL (Fin 3) K))⁻¹)
    (s : unitarySU p f K 3) :
    slAct e ⟨x, hx⟩ (suToPsu p f K s) = suToPsu p f K (suConj h A s) := by
  apply Subtype.ext
  rw [hyinner, coe_suToPsu, coe_suToPsu, coe_suConj]
  simp only [map_mul, map_inv, Subgroup.coe_inv]

theorem congr_psuEquivUnitary_apply (h : UnitaryFieldData p f K)
    (φ : MulAut (projImage (slPi false 3 (p ^ f) K)))
    (m : projImage (slPi false 3 (p ^ f) K)) :
    MulAut.congr (psuEquivUnitary h) φ (psuEquivUnitary h m) = psuEquivUnitary h (φ m) := by
  simp [MulAut.congr_apply]

theorem psuConj_eq_congr_of_inner {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q}
    (e : ↥Kg ≃* projImage (slPi false 3 (p ^ f) K)) (hx : x ∈ Subgroup.normalizer (Kg : Set Q))
    (h : UnitaryFieldData p f K) (A : unitaryIsom3 h)
    (hyinner : ∀ m : projImage (slPi false 3 (p ^ f) K),
      (slAct e ⟨x, hx⟩ m : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A : GL (Fin 3) K) * m * (ProjGenLinGroup.mk (A : GL (Fin 3) K))⁻¹) :
    psuConj h A = MulAut.congr (psuEquivUnitary h) (slAct e ⟨x, hx⟩) := by
  ext m
  obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 m
  rw [psuConj_unitaryProj, ← psuEquivUnitary_suToPsu h s, congr_psuEquivUnitary_apply,
    slAct_suToPsu_of_inner e hx h A hyinner s, psuEquivUnitary_suToPsu]

end Helpers

section Certs


theorem not_inner_of_field_minus {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q} {j : ℕ}
    (hjO : Odd j) (hj3 : 3 ≤ j) (hθ : aschbacherSolvableCore 3 Kg = ⊥)
    (e : ↥Kg ≃* projImage (slPi false 3 (2 ^ j) (GaloisField 2 (2 * j))))
    (hx : x ∈ Subgroup.normalizer (Kg : Set Q)) (hx3 : x ^ 3 = 1)
    (hkind : KFacts.InducesStdKind Kg x .field) :
    ¬ ∃ y ∈ glPi false 3 (2 ^ j) (GaloisField 2 (2 * j)),
        ∀ m : projImage (slPi false 3 (2 ^ j) (GaloisField 2 (2 * j))),
          (slAct e ⟨x, hx⟩ m : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * j))) =
            ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  rintro ⟨y, hy, hyinner⟩
  have hj1 : 1 ≤ j := by omega
  have hU := Sec4.unitaryFieldData_galoisField 2 j hj1
  have hq2 : 2 < 2 ^ j :=
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
  have := hU.finite
  have hyU : y ∈ unitaryIsom3 hU := (mem_glPi_false hU).mp hy
  obtain ⟨E, hE⟩ : ∃ E : Kg ⧸ aschbacherSolvableCore 3 Kg ≃* unitaryPSU hU 3,
      E = (thetaBotEquiv hθ).trans (e.trans (psuEquivUnitary hU)) := ⟨_, rfl⟩
  have hind : KFacts.inducedAutHom Kg E ⟨x, hx⟩ =
      MulAut.congr (psuEquivUnitary hU) (slAct e ⟨x, hx⟩) := by
    rw [hE]
    exact inducedAutHom_thetaBot hθ e (psuEquivUnitary hU) ⟨x, hx⟩
  have hD : KFacts.inducedAutHom Kg E ⟨x, hx⟩ ∈ (KFacts.psuConj hU).range := by
    rw [hind]
    exact MonoidHom.mem_range.mpr
      ⟨⟨y, hyU⟩, psuConj_eq_congr_of_inner e hx hU ⟨y, hyU⟩ hyinner⟩
  have hZ : Subgroup.center (Kg ⧸ aschbacherSolvableCore 3 Kg) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd E.symm (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
  have e₁ : Kg ⧸ aschbacherSolvableCore 3 Kg ≃* projSU 3 2 j :=
    E.trans (Sec4.projSUEquivUnitaryPSU 2 j hU).symm
  have hcard := (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two hj1)
  have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ j) e₁
  have key : ∀ k' : KFacts.AutKind, k' ≠ .inner → k' ≠ .diagonal →
      ¬ KFacts.InducesStdKind Kg x k' := by
    intro k' h1 h2 hstd
    rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := j) hjO hcard hZ hstd with
      ⟨K', _, hK', hq', e_L, hx', hkind'⟩ | hO
    · have h1' : KFacts.inducedAutHom Kg e_L ⟨x, hx'⟩ =
          MulAut.congr (E.symm.trans e_L) (KFacts.inducedAutHom Kg E ⟨x, hx⟩) := by
        ext z
        simp [KFacts.inducedAutHom_apply, MulAut.congr_apply]
      have hD' : KFacts.inducedAutHom Kg e_L ⟨x, hx'⟩ ∈ (KFacts.psuConj hK').range := by
        rw [h1']
        exact Sec21.Item223CensusResProof.congr_mem_psuConj_range_of_eq hK' hU hq'
          (E.symm.trans e_L) hD
      exact (KFacts.stdPinnedPSU3_separated hK').not_mem_inndiag_of_hasKind hkind' h1 h2 hD'
    · exact hodd hO
  exact key .field (by decide) (by decide) hkind

end Certs

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclU

end FusExclU

section FusModel


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusModel

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projImage projSU projSL)


theorem solvableCore_eq_bot {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec4.IsoLThreePi X 2 (3 * n)) : aschbacherSolvableCore 3 X = ⊥ := by
  have hs : IsSimpleGroup X := Proof1424Steps.isSimpleGroup_of_isoLThreePi_two (by omega) hX
  have h9 : 9 ∣ Nat.card X :=
    Proof155w2.nine_dvd_card_of_isLThreePi ⟨2, 3 * n, ⟨Nat.prime_two⟩, by omega, hX⟩
  rcases (aschbacherSolvableCore_normal 3 X).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have h3 := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
    rw [h, Subgroup.card_top] at h3
    exact h3 (dvd_trans (by norm_num) h9)

theorem even_of_two_pow_mod_three_eq_one {j : ℕ} (h : 2 ^ j % 3 = 1) : Even j := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨m, rfl⟩ := hodd
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have h5 : 2 ^ (2 * m + 1) = 4 ^ m * 2 := by
    rw [pow_succ, pow_mul]; norm_num
  have : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [h5, Nat.mul_mod, h4]
  rw [this] at h; exact absurd h (by norm_num)

theorem odd_of_two_pow_mod_three_eq_two {j : ℕ} (h : 2 ^ j % 3 = 2) : Odd j := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨m, rfl⟩ := hev
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have : 2 ^ (m + m) % 3 = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
    exact h4
  rw [this] at h; exact absurd h (by norm_num)

theorem hmodel_of_field {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q}
    (hx : x ∈ Subgroup.normalizer (Kg : Set Q)) {π : Bool} {q : ℕ} {K : Type} [Field K]
    (e : ↥Kg ≃* projImage (slPi π 3 q K)) {g : GL (Fin 3) K} {σ : K ≃+* K}
    (hfld : ∀ (s : GL (Fin 3) K) (hs : s ∈ slPi π 3 q K),
      (slAct e ⟨x, hx⟩ (projOf _ ⟨s, hs⟩) : Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) :
    ∀ (k k' : ↥Kg) (s : GL (Fin 3) K) (hs : s ∈ slPi π 3 q K),
      e k = projOf _ ⟨s, hs⟩ → x * (k : Q) * x⁻¹ = (k' : Q) →
      ((e k' : projImage (slPi π 3 q K)) : Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹) := by
  intro k k' s hs hks hk'
  have h1 : slAct e ⟨x, hx⟩ (e k) = e k' := by
    rw [slAct_apply, MulEquiv.symm_apply_apply]
    congr 1
    exact Subtype.ext ((coe_normalizerMonoidHom ⟨x, hx⟩ k).trans hk')
  rw [← h1, hks]
  exact hfld s hs


section Certs


theorem exists_fieldAct_model {Q : Type} [Group Q] [Finite Q] {Kg : Subgroup Q} {x : Q} {n : ℕ}
    (hn : 1 ≤ n) (hiso : Sec4.IsoLThreePi ↥Kg 2 (3 * n))
    (hx : x ∈ Subgroup.normalizer (Kg : Set Q)) (hx3 : x ^ 3 = 1)
    (hkind : KFacts.InducesStdKind Kg x .field) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π 2 (3 * n) K ∧ ModThree π (2 ^ (3 * n)) ∧
      ∃ e : ↥Kg ≃* projImage (slPi π 3 (2 ^ (3 * n)) K), ∃ f₀ : ℕ, 3 * n = 3 * f₀ ∧
        ∃ σ : K ≃+* K, ((∀ c, σ c = c ^ piCard π (2 ^ f₀)) ∨
            ∀ c, σ c = c ^ (piCard π (2 ^ f₀) ^ 2)) ∧
          ∃ g ∈ glPi π 3 (2 ^ (3 * n)) K,
            ∀ (k k' : ↥Kg) (s : GL (Fin 3) K) (hs : s ∈ slPi π 3 (2 ^ (3 * n)) K),
              e k = projOf _ ⟨s, hs⟩ → x * (k : Q) * x⁻¹ = (k' : Q) →
              ((e k' : projImage (slPi π 3 (2 ^ (3 * n)) K)) :
                Matrix.ProjGenLinGroup (Fin 3) K) =
                Matrix.ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvableCore_eq_bot hn hiso
  have h3n : 3 ≤ 3 * n := by omega
  have hxN : (⟨x, hx⟩ : Subgroup.normalizer (Kg : Set Q)) ^ 3 = 1 := Subtype.ext hx3
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  rcases hiso with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  ·
    have hev : Even (3 * n) := even_of_two_pow_mod_three_eq_one hq3
    have hK := Sec13.piField_galoisField 2 (3 * n) (by omega)
    refine ⟨true, GaloisField 2 (3 * n), inferInstance, hK, hq3, ?_⟩
    set e : ↥Kg ≃* projImage (slPi true 3 (2 ^ (3 * n)) (GaloisField 2 (3 * n))) :=
      φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage _ _)) with he
    rcases pslAct_pgl_or_field hK hq2 hθ e ⟨x, hx⟩ hxN with hin | ⟨-, f₀, hf, σ, hσ, g, hg, hfld⟩
    · exact absurd hin (CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclP.not_inner_of_field_plus hev h3n hθ e hx hx3 hkind)
    · exact ⟨e, f₀, hf, σ, hσ, g, hg, hmodel_of_field hx e hfld⟩
  ·
    have hodd : Odd (3 * n) := odd_of_two_pow_mod_three_eq_two hq3
    have hK := Sec13.piField_galoisField_two 2 (3 * n) (by omega)
    refine ⟨false, GaloisField 2 (2 * (3 * n)), inferInstance, hK, hq3, ?_⟩
    set e : ↥Kg ≃* projImage (slPi false 3 (2 ^ (3 * n)) (GaloisField 2 (2 * (3 * n)))) :=
      φ.trans (MulEquiv.subgroupCongr (projSU_eq_projImage _ _)) with he
    rcases pslAct_pgl_or_field hK hq2 hθ e ⟨x, hx⟩ hxN with hin | ⟨-, f₀, hf, σ, hσ, g, hg, hfld⟩
    · exact absurd hin (CFSG.RankThree.PartTwo.Sec15.F153L3K.FusExclU.not_inner_of_field_minus hodd h3n hθ e hx hx3 hkind)
    · exact ⟨e, f₀, hf, σ, hσ, g, hg, hmodel_of_field hx e hfld⟩

end Certs

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusModel

end FusModel

