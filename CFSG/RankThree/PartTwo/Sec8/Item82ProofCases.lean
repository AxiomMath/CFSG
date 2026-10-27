module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofBridge
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd
public import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofSL34

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec8.Item82OneProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial


theorem isoTrialityD4_of_model
    {X : Type} [Group X] {n : ℕ}
    (hn : 1 ≤ n) (hX : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n) :
    IsoTrialityD4 X n := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_D4 hX
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hqc : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q
  have hKq : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hqc]
    exact hK
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv rfl K hKq
    σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e₃ := CFSG.TauCetiBridge.Twisted.nativeEquiv
    (t := CFSG.Blueprint.Chevalley.TwistTag.D4) (σ := σ.toRingHom) Nat.prime_two hn hK hσ
  exact ⟨q, hv, rfl, rfl, ⟨E.trans (e₃.symm.trans e₂)⟩⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  (h : Hyp81 G A c L a) (h81 : Nat.card A = 81) (hAN : A ≤ Subgroup.normalizer (L : Set G))

include h h81 hAN

theorem false_of_psl2 (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (hP : KF82TwoNoE9PSL2) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hpe : p ≠ 3 ∨ e = 3)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p e)) : False := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hp : p.Prime := Fact.out
  have hK := card_galoisField p e he
  set E := e₁.trans (projSLEquivPSL (GaloisField p e))
  have hf := inducesKind_field_of_pow_three L ha3 h.inducesOuterTheta E
  obtain ⟨σ, -, hcard, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_of_field ha3 E hf
  rw [hK] at hcard
  obtain ⟨j, hj, hej⟩ := exists_eq_pow_of_pow_three_eq hp hcard
  have hpj : p ≠ 3 ∨ j = 1 := by
    rcases hpe with hp3 | he3
    · exact Or.inl hp3
    · exact Or.inr (by omega)
  have hE9 := (hP _ p j hp hj hpj).of_mulEquiv ι
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd E.symm
    (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  exact false_of_noE9 h h81 hAN hcyc hZ hE9

theorem false_of_projSL3_odd (hL3 : KF82TwoPSL3Odd) {n : ℕ} (hn : Odd n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) : False :=
  false_of_outerThreeRankTwo h h81 hAN ((hL3 n hn).of_mulEquiv e₁)

theorem isList82Two_of_projSU (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (hPGU : KF82TwoNoE9PGU) {m : ℕ} (hm : 1 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 m) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
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
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 m hU)).symm
      (center_unitaryPSU_three_eq_bot hU hq2)
  rcases Nat.even_or_odd m with hme | hmo
  ·
    exfalso
    have hq := Item82OneProof.two_pow_mod_three_of_even hme
    set E := e₁.trans (projSUEquivUnitaryPSU 2 m hU)
    rcases inducesKindPSU3_diagonal_or_field (h := hU) L hq2 ha3 hout E with hd | hf
    · exact false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd ha3
    · obtain ⟨f₀, rfl, hC⟩ := isoPGUThree_barCentralizer_of_field hq2 ha3 ⟨E, hf⟩
      have hf₀ : Even f₀ := by
        rcases Nat.even_or_odd f₀ with hfe | hfo
        · exact hfe
        · exact absurd hme (Nat.not_even_iff_odd.mpr (Nat.odd_mul.mpr ⟨by decide, hfo⟩))
      exact false_of_noE9 h h81 hAN hcyc hZ (hPGU _ f₀ hf₀ hC)
  ·
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = CFSG.Open.ordTwistedA 2 (2 ^ m) :=
      (Nat.card_congr e₁.toEquiv).trans (card_projSU_three_two hm)
    have hodd := not_oddCharStdModel_of_mulEquiv_projSU hm2 e₁
    rcases h.inducesStdKind with hk | hk
    · rcases inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with ⟨K, _, hK, hq, hkK⟩ | hO
      · obtain ⟨f₀, rfl, -⟩ := isoPGUThree_barCentralizer_of_field hq ha3 hkK
        exact ⟨f₀, (Nat.odd_mul.mp hmo).2,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁⟩))))⟩
      · exact (hodd hO).elim
    · rcases inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with ⟨K, _, hK, -, hkK⟩ | hO
      · exact (not_inducesKindPSU3_graphField hK hkK).elim
      · exact (hodd hO).elim

theorem isList82Two_of_statedSU (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (hPGU : KF82TwoNoE9PGU) {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨e₂⟩ :=
      nonempty_statedSU_mulEquiv_projSU hm (Item82OneProof.two_pow_mod_three_of_even hme) hK
    exact isList82Two_of_projSU h h81 hAN hcyc hPGU hm (e₁.trans e₂)
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
    exact ⟨f₀, (Nat.odd_mul.mp hmo).2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨K, inferInstance, inferInstance,
        Or.inr ⟨hK, Item82OneProof.two_pow_mod_three_of_odd hmo, ⟨e₁⟩⟩⟩))))⟩
  · exact (not_inducesStdKind_graphField_of_isoSUThree hm3 hm3' hL hk).elim

omit hAN in
theorem false_of_statedSL (hR : Item82TwoSLThree) {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) : False := by
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · obtain rfl : n = 2 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    obtain ⟨hnf, hng⟩ := kF82SLThreeFour G L a K (by rw [hK]; norm_num) ⟨e₁⟩
      (h.mem_partTwoF.1.2 a h.a_mem)
    rcases h.inducesStdKind with hk | hk
    · exact hnf hk
    · exact hng hk
  · exact (hR G A c L a h h81 n hn hn4 K hK).false e₁

omit h81 hAN in
theorem isList82Two_of_projSp {n : ℕ} (hn : Odd n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  set E := e₁.trans (projSpEquivStatedProj 2 (GaloisField 2 n))
  obtain ⟨-, σ, -, hcard, -⟩ := exists_barCentralizer_mulEquiv_sp4 ha3 h.inducesOuterTheta E
  rw [card_galoisField 2 n hn.pos] at hcard
  obtain ⟨j, -, rfl⟩ := exists_eq_pow_of_pow_three_eq Nat.prime_two hcard
  exact ⟨j, (Nat.odd_mul.mp hn).2, Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁⟩)))⟩

omit h81 hAN in
theorem isList82Two_of_g2 {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 n) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hf3 : 3 ≤ 2 ^ n := hX.1.2.2.2
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n <;> norm_num at hf3
    · exact h2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨-, σ, -, hcard, -⟩ :=
    exists_barCentralizer_mulEquiv_g2 (ringChar.eq K 2) hK4 ha3 h.inducesOuterTheta E
  rw [hK] at hcard
  obtain ⟨j, -, rfl⟩ := exists_eq_pow_of_pow_three_eq Nat.prime_two hcard
  obtain ⟨q, hq2, hqe, hG⟩ :=
    Item86ResProof.isoGTwo_of_mulEquiv_adjointGroup (f := 3 * j) (by omega) K hK E
  exact ⟨j, (Nat.odd_mul.mp hn).2, Or.inr (Or.inl ⟨q, hq2, hqe, hG⟩)⟩

omit h81 hAN in
theorem isList82Two_of_ree {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 n) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  obtain ⟨-, b, hb, hnb, K, _, _, _, hK, ⟨E⟩⟩ := exists_mulEquiv_reeGamma hX
  have hLang := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj b K hK
  have hk := inducesKindLargeRee_field L hb hK hLang ha3 h.inducesOuterTheta E
  have hk' := (inducesKindLargeRee_iff L hb hK E a .field).mp hk
  have : Finite (K ≃+* K) := finite_ringAut Nat.prime_two hK
  have h3 := three_dvd_card_of_inducesKind_field
    (ψ := CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAutHom K b) rfl hk' ha3
  rw [card_ringAut_eq Nat.prime_two (by omega) hK] at h3
  obtain ⟨j, hj⟩ := h3
  obtain ⟨hv, he⟩ := Item86ResProof.reeF4_of_mulEquiv_reeGamma b hb K hK E
  have hn3 : n = 3 * j := by omega
  have hjo : Odd j := (Nat.odd_mul.mp (hn3 ▸ hn)).2
  exact ⟨j, hjo, Or.inr (Or.inr (Or.inl ⟨b, hv, by omega, he⟩))⟩

theorem isList82Two_of_alt47
    (hP : KF82TwoNoE9PSL2) (hPGU : KF82TwoNoE9PGU) (hL3 : KF82TwoPSL3Odd)
    (hKind : KF82TwoLThreeKinds) (hOdd : KF82OddSLThree) (hR1 : Item82TwoSLThree)
    (hR2 : Item82TwoPSL2Three) (halt : Alt47 L a) :
    IsList82Two (L ⧸ aschbacherSolvableCore 3 L) := by
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcyc := outThreeCyclic_of_alt47 hq halt
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  rcases halt with ⟨p, e, _, hp2, he, ⟨e₁⟩, -⟩ | ⟨p, e, _, hp3, he1, he2, hX, -⟩ |
    ⟨h3, -⟩ | ⟨n, hn, hX, hdiag⟩ | ⟨n, hn, hD, -, -⟩
  ·
    exfalso
    rcases eq_or_ne p 3 with rfl | hp3
    · rcases Nat.lt_or_ge e 2 with he2 | he2
      · obtain rfl : e = 1 := by omega
        exact false_of_psl2 h h81 hAN hcyc hP (by norm_num) (Or.inr rfl) e₁
      · exact (hR2 G A c L a h h81 e he2).false e₁
    · exact false_of_psl2 h h81 hAN hcyc hP (by omega) (Or.inl hp3) e₁
  ·
    exact (false_of_oddSLThree h hOdd hp3 he1 he2 hX).elim
  ·
    rcases h3 with ⟨m, hm, he₁ | ⟨K, _, _, hK, ⟨e₁⟩⟩ | he₁ | ⟨K, _, _, hK, ⟨e₁⟩⟩⟩ |
      ⟨n, hn, hSz | he₁ | he₁ | hX | hX⟩
    · exact (false_of_psl2 h h81 hAN hcyc hP hm (Or.inl (by decide)) he₁.some).elim
    · exact isList82Two_of_statedSU h h81 hAN hcyc hPGU hm hK e₁
    · exact isList82Two_of_projSU h h81 hAN hcyc hPGU hm he₁.some
    · exact (false_of_statedSL h h81 hR1 ⟨m, by ring⟩ (by omega) hK e₁).elim
    · exact (KP7.three_not_dvd_card hSz (three_dvd_card_of_hyp81 h h81 hAN hcyc)).elim
    · exact (false_of_projSL3_odd h h81 hAN hL3 hn he₁.some).elim
    · exact isList82Two_of_projSp h hn he₁.some
    · exact isList82Two_of_g2 h hn hX
    · exact isList82Two_of_ree h hn hX
  ·
    rcases hX with ⟨K, _, _, ⟨hK, hq3, ⟨e₁⟩⟩ | ⟨hK, hq3, ⟨e₁⟩⟩⟩ | ⟨hq3, he₁⟩ | ⟨hq3, he₁⟩
    · have hne : Even n := by
        rcases Nat.even_or_odd n with hne | hno
        · exact hne
        · have := Item82OneProof.two_pow_mod_three_of_odd hno
          omega
      exact (false_of_statedSL h h81 hR1 hne hn hK e₁).elim
    · exact isList82Two_of_statedSU h h81 hAN hcyc hPGU hn hK e₁
    · exfalso
      have hne : Even n := by
        rcases Nat.even_or_odd n with hne | hno
        · exact hne
        · have := Item82OneProof.two_pow_mod_three_of_odd hno
          omega
      obtain ⟨hnf, hng⟩ := hKind G L a n hne hn he₁ ha3 hdiag
      rcases h.inducesStdKind with hk | hk
      · exact hnf hk
      · exact hng hk
    · exact isList82Two_of_projSU h h81 hAN hcyc hPGU hn he₁.some
  ·
    exact ⟨n, hn, Or.inl (isoTrialityD4_of_model hn.pos hD)⟩

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
