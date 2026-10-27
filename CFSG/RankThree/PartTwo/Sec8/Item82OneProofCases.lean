module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofL2
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82OneProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  exact KP7.two_pow_odd_mod_three k

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem three_dvd_two_pow_add_one_of_odd {m : ℕ} (hm : Odd m) : 3 ∣ 2 ^ m + 1 := by
  have := two_pow_mod_three_of_odd hm
  omega

theorem exists_eq_pow_of_pow_three_eq {p x m : ℕ} (hp : p.Prime) (h : x ^ 3 = p ^ m) :
    ∃ j, x = p ^ j ∧ m = 3 * j := by
  have hdvd : x ∣ p ^ m := ⟨x ^ 2, by rw [← h]; ring⟩
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨j, rfl, ?_⟩
  rw [← pow_mul] at h
  exact (Nat.pow_right_injective hp.two_le h).symm.trans (mul_comm j 3)

theorem nonempty_statedSU_mulEquiv_projSU {m : ℕ} (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2) :
    Nonempty (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K ≃* projSU 3 2 m) := by
  set K₀ := GaloisField 2 (2 * m)
  have hU := unitaryFieldData_galoisField 2 m hm
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hcard : Fintype.card K = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hU.card, ← pow_mul,
      mul_comm]
  set κ : K ≃+* K₀ := FiniteField.ringEquivOfCardEq hcard
  set φ := CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin 3) κ
  have hmap := CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSU 3 (2 ^ m) κ
  let e₂ : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K ≃* unitarySU 2 m K₀ 3 :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  let e₃ : unitarySU 2 m K₀ 3 ≃* unitaryPSU hU 3 :=
    MulEquiv.ofBijective (unitaryProj hU 3)
      ⟨unitaryProj_three_injective hU hq, unitaryProj_surjective hU 3⟩
  exact ⟨e₂.trans (e₃.trans (projSUEquivUnitaryPSU 2 m hU).symm)⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  (h : Hyp81 G A c L a) (h27 : Nat.card A = 27) (hAN : A ≤ Subgroup.normalizer (L : Set G))
  (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))

include h h27 hAN hcyc

theorem isList82One_of_psl2 {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p e)) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  have hp : p.Prime := Fact.out
  have hK := card_galoisField p e he
  have : Finite (GaloisField p e ≃+* GaloisField p e) := finite_ringAut hp hK
  set E := e₁.trans (projSLEquivPSL (GaloisField p e))
  have hf := inducesKind_field_of_pow_three L ha3 hout E
  have h3e : 3 ∣ e := by
    have := three_dvd_card_of_inducesKind_field
      (ψ := CFSG.GorensteinWalter.psl2FieldAut (GaloisField p e)) rfl hf ha3
    rwa [card_ringAut_eq hp he hK] at this
  obtain ⟨e', rfl⟩ := h3e
  have he' : 1 ≤ e' := by omega
  rcases lt_trichotomy p 3 with hp3 | rfl | hp3
  · obtain rfl : p = 2 := by have := hp.two_le; omega
    exact Or.inr (Or.inr ⟨e', he', Or.inl ⟨e₁⟩⟩)
  · rcases Nat.lt_or_ge e' 2 with he2 | he2
    · obtain rfl : e' = 1 := by omega
      exact Or.inl ⟨e₁⟩
    · exfalso
      obtain ⟨σ, -, hcard, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_of_field ha3 E hf
      rw [hK] at hcard
      obtain ⟨j, hj, hje⟩ := exists_eq_pow_of_pow_three_eq Nat.prime_three hcard
      obtain rfl : j = e' := by omega
      have hE9 := (e9Closed_psl2_of_card_eq_three_pow hj he2).of_mulEquiv ι
      have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
        (CFSG.GorensteinWalter.psl2_center_eq_bot _)
      exact false_of_e9Closed h h27 hAN hcyc hZ hE9
  · exact Or.inr (Or.inl ⟨p, e', inferInstance, hp3, he', ⟨e₁⟩⟩)

theorem isList82One_of_projSL3 (hL3 : KF82LThreeWrong) {n : ℕ} (hn : 1 ≤ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  rcases Nat.even_or_odd n with hne | hno
  · exfalso
    have hq := two_pow_mod_three_of_even hne
    have hE9 := hL3 G L a n hne hn ⟨e₁⟩ ha3 h.inducesStdKind
    have hZ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd e₁.symm (Sec13.isPerfect_center_projSL 2 n hn hq).2
    exact false_of_e9Closed h h27 hAN hcyc hZ hE9
  · have hq := two_pow_mod_three_of_odd hno
    have hK := card_galoisField 2 n hn
    have : Finite (GaloisField 2 n ≃+* GaloisField 2 n) := finite_ringAut Nat.prime_two hK
    set E := e₁.trans (projSLEquivProjectiveSL 3 (GaloisField 2 n))
    rcases inducesKindPSL_diagonal_or_field L (le_refl 3) ha3 hout E with hd | hf
    · exact (false_of_inducesKind_diagonal
        (psl_inndiag_cube (Or.inr (not_three_dvd_card_units hK hq))) hd ha3).elim
    · have h3 := three_dvd_card_of_inducesKind_field (ψ := LinearFlag.fieldAut 3 (GaloisField 2 n))
        rfl hf ha3
      rw [card_ringAut_eq Nat.prime_two hn hK] at h3
      obtain ⟨n', rfl⟩ := h3
      exact Or.inr (Or.inr ⟨n', by omega, Or.inr (Or.inl (Or.inr ⟨hq, ⟨e₁⟩⟩))⟩)

omit h27 hAN hcyc in
theorem false_of_isSolvable (hs : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L)) : False :=
  false_of_isQuasisimple_of_isSolvable
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt) hs

theorem isList82One_of_projSU (hPGU : KF82E9PGUThree) {m : ℕ} (hm : 1 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 m) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  have hU := unitaryFieldData_galoisField 2 m hm
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    have := Sec13.isSolvable_projSU_two
    exact (false_of_isSolvable h (Group.isSolvable_of_surjective
      (f := e₁.symm.toMonoidHom) e₁.symm.surjective)).elim
  have hq2 : 2 < 2 ^ m :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
  rcases Nat.even_or_odd m with hme | hmo
  ·
    have hq := two_pow_mod_three_of_even hme
    have : Finite (GaloisField 2 (2 * m) ≃+* GaloisField 2 (2 * m)) :=
      finite_ringAut Nat.prime_two hU.card
    set E := e₁.trans (projSUEquivUnitaryPSU 2 m hU)
    rcases inducesKindPSU3_diagonal_or_field (h := hU) L hq2 ha3 hout E with hd | hf
    · exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd ha3).elim
    · have h3 := three_dvd_card_of_inducesKind_field (ψ := psuField hU) rfl hf ha3
      rw [card_ringAut_eq Nat.prime_two (by omega) hU.card] at h3
      obtain ⟨m', rfl⟩ : 3 ∣ m := by omega
      exact Or.inr (Or.inr ⟨m', by omega, Or.inr (Or.inl (Or.inl ⟨hq, ⟨e₁⟩⟩))⟩)
  ·
    exfalso
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = CFSG.Open.ordTwistedA 2 (2 ^ m) :=
      (Nat.card_congr e₁.toEquiv).trans (card_projSU_three_two hm)
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 m hU)).symm
        (center_unitaryPSU_three_eq_bot hU hq2)
    have hodd := not_oddCharStdModel_of_mulEquiv_projSU hm2 e₁
    rcases h.inducesStdKind with hk | hk
    · rcases inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with ⟨K, _, hK, hq, hkK⟩ | hO
      · obtain ⟨f₀, rfl, hC⟩ := isoPGUThree_barCentralizer_of_field hq ha3 hkK
        have hf₀ : Odd f₀ := (Nat.odd_mul.mp hmo).2
        exact false_of_e9Closed h h27 hAN hcyc hZ (hPGU _ f₀ hf₀ hC)
      · exact hodd hO
    · rcases inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with ⟨K, _, hK, -, hkK⟩ | hO
      · exact not_inducesKindPSU3_graphField hK hkK
      · exact hodd hO

theorem isList82One_of_statedSU (hPGU : KF82E9PGUThree) {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨e₂⟩ :=
      nonempty_statedSU_mulEquiv_projSU hm (two_pow_mod_three_of_even hme) hK
    exact isList82One_of_projSU h h27 hAN hcyc hPGU hm (e₁.trans e₂)
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    exfalso
    obtain rfl : m = 1 := by
      obtain ⟨k, rfl⟩ := hmo
      omega
    have := hU.finite
    have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have := Fintype.ofFinite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)
    have hsolv : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
        (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    exact false_of_isSolvable h
      (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)
  have hm3' : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one_of_odd hmo
  have hL : IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ m) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨e₁⟩⟩
  rcases h.inducesStdKind with hk | hk
  · obtain ⟨K', _, hU', hq', hk'⟩ := inducesKindSU3_of_inducesStdKind hm3 hm3' hL hk
    obtain ⟨f₀, rfl, -⟩ := isoSUThree_barCentralizer_of_field hq' ha3 hk'
    have hq : 2 ^ (3 * f₀) % 3 = 2 := two_pow_mod_three_of_odd hmo
    exact Or.inr (Or.inr ⟨f₀, by omega, Or.inr (Or.inr
      ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hq, ⟨e₁⟩⟩⟩)⟩)
  · exact (not_inducesStdKind_graphField_of_isoSUThree hm3 hm3' hL hk).elim

omit h27 hAN hcyc in
theorem isList82One_of_statedSL (hSL4 : KF82SLThreeFour) {n : ℕ} (hn : 2 ≤ n)
    (hq : 2 ^ n % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :
    IsList82One (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · exfalso
    obtain rfl : n = 2 := by omega
    obtain ⟨hnf, hng⟩ := hSL4 G L a K hK ⟨e₁⟩ ha3
    rcases h.inducesStdKind with hk | hk
    · exact hnf hk
    · exact hng hk
  have hL : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨e₁⟩⟩
  rcases h.inducesStdKind with hk | hk
  · obtain ⟨K', _, _, hK', E', hx, hf⟩ := inducesKindSL_of_inducesStdKind hn3 hq hL hk
    have : Finite (K' ≃+* K') := finite_ringAut Nat.prime_two hK'
    have h3 := three_dvd_card_of_isField (ψ := LinearFlag.fieldAut 3 K') rfl hf
      (descendAut_inducedAutHom_pow_three hx ha3)
    rw [card_ringAut_eq Nat.prime_two (by omega) hK'] at h3
    obtain ⟨k, rfl⟩ := h3
    exact Or.inr (Or.inr ⟨k, by omega, Or.inr (Or.inr
      ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, hq, ⟨e₁⟩⟩⟩)⟩)
  · exact (not_inducesStdKind_graphField_of_isoSLThree hn3 hq hL ha3 hk).elim

theorem false_of_suzuki {p n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (L ⧸ aschbacherSolvableCore 3 L) p n) : False :=
  false_of_not_three_dvd h h27 hAN hcyc (KP7.three_not_dvd_card hSz)

theorem false_of_projSp {n : ℕ}
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) : False := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  set E := e₁.trans (projSpEquivStatedProj 2 (GaloisField 2 n))
  obtain ⟨-, σ, -, -, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_sp4 ha3 h.inducesOuterTheta E
  have hE9 := (e9Closed_statedSp_two (F := CFSG.GH74.GLS.IVK.fixedField σ)).of_mulEquiv ι
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
    (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (GaloisField 2 n))
  exact false_of_e9Closed h h27 hAN hcyc hZ hE9

theorem false_of_g2 (hG2 : KF82E9GTwo) {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 n) :
    False := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hf3 : 3 ≤ 2 ^ n := hX.1.2.2.2
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n <;> norm_num at hf3
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨-, σ, -, hcard, ⟨ι⟩⟩ :=
    exists_barCentralizer_mulEquiv_g2 (ringChar.eq K 2) hK4 ha3 h.inducesOuterTheta E
  rw [hK] at hcard
  obtain ⟨j, hj, rfl⟩ := exists_eq_pow_of_pow_three_eq Nat.prime_two hcard
  have hjo : Odd j := (Nat.odd_mul.mp hn).2
  have hE9 := (hG2 _ j hjo hj).of_mulEquiv ι
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  exact false_of_e9Closed h h27 hAN hcyc hZ hE9

omit h27 hAN hcyc in
theorem e9Closed_barCentralizer_of_autFix
    (hE9 : E9Closed (autFix (thetaQuotMulAut L (compAction L ⟨a, h.a_mem_normalizer⟩)))) :
    E9Closed (barCentralizer (Subgroup.zpowers a) L) := by
  rw [barCentralizer_zpowers_eq_autFix h.a_mem_normalizer]
  exact hE9

theorem false_of_ree (hRee : KF82E9ReeF4) {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 n) :
    False := by
  have hE9 := e9Closed_barCentralizer_of_autFix h
    (hRee _ n hn hX _ h.induced_pow_three h.not_isInnerAut_induced)
  obtain ⟨-, b, -, -, K, _, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_reeGamma hX
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
    (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial b K hK)
  exact false_of_e9Closed h h27 hAN hcyc hZ hE9

theorem false_of_trialityD4 (hD4 : KF82E9TrialityD4) {n : ℕ}
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L)
      .trialityD4 2 n) : False := by
  have hE9 := e9Closed_barCentralizer_of_autFix h
    (hD4 _ n hX _ h.induced_pow_three h.not_isInnerAut_induced)
  obtain ⟨K, _, _, σ, -, -, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 hX
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
    (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  exact false_of_e9Closed h h27 hAN hcyc hZ hE9

omit hAN hcyc h27 in
theorem false_of_oddSLThree (hOdd : KF82OddSLThree) {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hX : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) : False := by
  obtain ⟨hnf, hng⟩ := hOdd G L a p e hp3 he1 he2 hX (h.mem_partTwoF.1.2 a h.a_mem)
  rcases h.inducesStdKind with hk | hk
  · exact hnf hk
  · exact hng hk

end CFSG.RankThree.PartTwo.Sec8.Item82OneProof
