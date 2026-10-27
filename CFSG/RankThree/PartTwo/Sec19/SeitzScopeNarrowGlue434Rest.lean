module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434Seitz
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

@[expose] def OddPrimeFieldPlanesInner : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), 3 < q.p → q.exponent = 1 →
    (d.1 = .A 3 q ∨ d.1 = .twistedA 3 q ∨ d.1 = .B 2 q ∨ d.1 = .G2 q) →
    ∀ E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)),
      CFSG.Open.IsElemAbelian 3 E → InnerPlane d 3 E

@[expose] def SeitzThreeOddInner : Prop :=
  SeitzPlanes fun d p E => p = 3 ∧ InnerPlane d p E ∧
    ∃ q : TauCeti.PrimePower, d.1 = .A 3 q ∨ d.1 = .twistedA 3 q ∨ d.1 = .B 2 q ∨ d.1 = .G2 q

theorem seitzThreeOddInner_of
    (h1 : SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
      ∃ q : TauCeti.PrimePower, d.1 = .A 3 q ∨ d.1 = .twistedA 3 q ∨ d.1 = .B 2 q)
    (h2 : SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsG2Index d.1) :
    SeitzThreeOddInner := by
  rintro d p hp hp2 hpd hex E hE hc ⟨hp3, hin, q, hq | hq | hq | hq⟩
  · exact h1 d p hp hp2 hpd hex E hE hc ⟨hin, hp3, q, Or.inl hq⟩
  · exact h1 d p hp hp2 hpd hex E hE hc ⟨hin, hp3, q, Or.inr (Or.inl hq)⟩
  · exact h1 d p hp hp2 hpd hex E hE hc ⟨hin, hp3, q, Or.inr (Or.inr hq)⟩
  · exact h2 d p hp hp2 hpd hex E hE hc ⟨hin, hp3, q, hq⟩

namespace SeitzScopeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res6Seitz
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

theorem not_isD2SeitzException_odd {q : PrimePower} (hq : q.p ≠ 2) {d : LieTypeIndex}
    (hd : d = .A 3 q ∨ d = .twistedA 3 q ∨ d = .B 2 q ∨ d = .G2 q) :
    ¬ IsD2SeitzException 3 d := by
  have hch : d.characteristic = q.p := by
    rcases hd with rfl | rfl | rfl | rfl
    · exact LieTypeIndex.characteristic_A 3 q
    · exact LieTypeIndex.characteristic_twistedA 3 q
    · exact LieTypeIndex.characteristic_B 2 q
    · exact LieTypeIndex.characteristic_G2 q
  rintro (⟨-, (⟨q', h2, -, hdq⟩ | ⟨q', h2, -, hdq⟩ | ⟨q', h2, -, hdq⟩ |
    ⟨q', h2, -, hdq | hdq⟩ | hdt)⟩ | ⟨h5, -⟩)
  · rw [hdq, LieTypeIndex.characteristic_A, h2] at hch
    exact hq hch.symm
  · rw [hdq, LieTypeIndex.characteristic_A, h2] at hch
    exact hq hch.symm
  · rw [hdq, LieTypeIndex.characteristic_twistedA, h2] at hch
    exact hq hch.symm
  · rw [hdq, LieTypeIndex.characteristic_B, h2] at hch
    exact hq hch.symm
  · rw [hdq, LieTypeIndex.characteristic_B, h2] at hch
    exact hq hch.symm
  · rw [hdt] at hch
    exact hq (by simpa [LieTypeIndex.characteristic] using hch.symm)
  · omega

theorem seitzHyperGamma_eq_top_of_odd_carrier (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) {X : Type} [Group X] {d : ValidLieTypeIndex}
    {q : PrimePower} (hq3 : 3 < q.p) (hq1 : q.exponent = 1)
    (hd : d.1 = .A 3 q ∨ d.1 = .twistedA 3 q ∨ d.1 = .B 2 q ∨ d.1 = .G2 q)
    (ι : X ≃* (CFSGIndex.lie d).Group) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hq2 : q.p ≠ 2 := by omega
  have hch : d.1.characteristic = q.p := by
    rcases hd with h | h | h | h <;> rw [h]
    · exact LieTypeIndex.characteristic_A 3 q
    · exact LieTypeIndex.characteristic_twistedA 3 q
    · exact LieTypeIndex.characteristic_B 2 q
    · exact LieTypeIndex.characteristic_G2 q
  have hchar : 3 ≠ d.1.characteristic := by rw [hch]; omega
  have hexc := not_isD2SeitzException_odd hq2 hd
  have hEo : CFSG.Open.IsElemAbelian 3 E := ⟨hE.1, hE.2⟩
  exact Item434RowsProof.seitzHyperGamma_eq_top_of_closure hE.2 h9
    (closure_fixSet_eq_top_of_seitzPlanes hI hchar hexc ι E hEo h9
      ⟨rfl, hOut d q hq3 hq1 hd _ (isElemAbelian_mapAut hEo ι), q, hd⟩)

theorem seitzHyperGamma_eq_top_of_projSL_four_odd (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (φ : X ≃* projSL 4 (GaloisField p 1)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, 1, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ 1 := PrimePower.card_def q
  have hv : (LieTypeIndex.A 3 q).Valid := by
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    change ¬ ((3 = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (3 = 2 ∧ q.card = 2) ∨
      (3 = 3 ∧ q.card = 2))
    rw [hqc, pow_one]
    omega
  exact seitzHyperGamma_eq_top_of_odd_carrier hI hOut (d := ⟨.A 3 q, hv⟩) (q := q) hp3 rfl
    (Or.inl rfl)
    (φ.trans ((Sec4.projSLEquivPSLn (3 + 1) _).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv).symm)) hE h9

theorem seitzHyperGamma_eq_top_of_projSU_four_odd (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (φ : X ≃* projSU 4 p 1) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, 1, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ 1 := PrimePower.card_def q
  have hv : (LieTypeIndex.twistedA 3 q).Valid :=
    ⟨⟨by omega, fun _ => by rw [hqc, pow_one]; omega⟩, fun h => h⟩
  exact seitzHyperGamma_eq_top_of_odd_carrier hI hOut (d := ⟨.twistedA 3 q, hv⟩) (q := q) hp3 rfl
    (Or.inr (Or.inl rfl))
    (φ.trans ((Sec4.projSUEquivStatedProj (3 + 1) p 1).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv).symm)) hE h9

theorem seitzHyperGamma_eq_top_of_projSp_two_odd (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (φ : X ≃* projSp 2 (GaloisField p 1)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, 1, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ 1 := PrimePower.card_def q
  have hv : (LieTypeIndex.B 2 q).Valid := by
    refine ⟨⟨le_rfl, ?_⟩, ?_⟩
    · rw [hqc, pow_one]
      omega
    · change ¬ (2 = 2 ∧ q.card = 3)
      rw [hqc, pow_one]
      omega
  have : Fact q.p.Prime := ⟨hp⟩
  exact seitzHyperGamma_eq_top_of_odd_carrier hI hOut (d := ⟨.B 2 q, hv⟩) (q := q) hp3 rfl
    (Or.inr (Or.inr (Or.inl rfl)))
    (φ.trans (Census.typeB2GroupEquivProjSp q hv).symm) hE h9

theorem seitzHyperGamma_eq_top_of_L3Pi_narrow
    (hA : SeitzThreeLThreePi)
    (h199 : Seitz199L3) {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hpe : p = 2 ∨ e ≤ 2) (hp3 : p ≠ 3) (h5 : 5 ≤ p ^ e)
    (hpi : IsoLThreePi (X ⧸ Subgroup.center X) p e) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  by_cases hZ : Subgroup.center X = ⊥
  · have hiso : Sec4.IsoLThreePi X p e := by
      rcases hpi with ⟨h1, ⟨θ⟩⟩ | ⟨h2, ⟨θ⟩⟩
      · exact Or.inl ⟨h1, ⟨equivOfCenterEqBot hZ θ⟩⟩
      · exact Or.inr ⟨h2, ⟨equivOfCenterEqBot hZ θ⟩⟩
    have h4 : ¬ (p = 2 ∧ e = 2) := by
      rintro ⟨rfl, rfl⟩
      norm_num at h5
    exact Item434RowsProof.seitzHyperGamma_eq_top_of_closure hE.2 h9
      (closure_fixSet_of_lThreePi hA he (by omega) hiso h4 E ⟨hE.1, hE.2⟩ h9)
  · have hq3 : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
      rcases hpi with ⟨h1, -⟩ | ⟨h2, -⟩ <;> omega
    have hSL : Sec4.IsSLThreePi X :=
      ⟨p ^ e, KFacts.isSLThreePiAt_of_isSLThreeEpsAt he
        (Census.coverSLThree46 X hq hZ3 hZ p e he hpe hpi) hq3 hZ⟩
    refine Item434RowsProof.seitzHyperGamma_eq_top_of_closure hE.2 h9
      (h199 X E hE.2 h9 ⟨hq, hSL, ?_⟩)
    rintro ⟨⟨ψ⟩, -⟩
    have hlt := lt_card_of_isoLThreePi he h5 hpi
    have hK : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hSL4 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
      have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
      decide
    have hle : Nat.card (X ⧸ Subgroup.center X) ≤ Nat.card X :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [Nat.card_congr ψ.toEquiv, hSL4] at hle
    omega

end SeitzScopeProof

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof CFSG.RankThree.PartTwo.Sec4.Res6Seitz
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open TauCeti

section CertsRestNine



theorem seitzHyperGamma_eq_top_rest_nine_narrow (hS2 : SeitzThreePartTwoChar2)
    (hA : SeitzThreeLThreePi) (h199 : Seitz199L3) (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) (hL : IsLie42GenericRest (X ⧸ Subgroup.center X))
    (hD4 : ¬ IsLie42GenericD4 (X ⧸ Subgroup.center X)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  rcases hL with ⟨p, e, hp, hp3, he, he2, hpi⟩ | ⟨p, hp, hp3, hG2 | hSp | hL4 | hU4⟩ |
    ⟨n, hn4, hn6, hpi | ⟨h3n, hL3 | hU3⟩ | hSp | hU4⟩ | ⟨q, hq2, hq4, hq6, hv, ⟨θ⟩⟩ | hd |
    ⟨m, hm, -, ⟨θ⟩⟩
  ·
    have h5 : 5 ≤ p ^ e :=
      le_trans (five_le_of_prime hp.out hp3) (Nat.le_self_pow (by omega) p)
    exact seitzHyperGamma_eq_top_of_L3Pi_narrow hA h199 hq hZ3 he (Or.inr he2) (by omega) h5 hpi hE
      h9
  ·
    obtain ⟨q, hqp, hq1, hv, ⟨θ⟩⟩ := hG2
    have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
      (Census.chevalleyExceptionalModel_G2_of_odd q hv (by rw [hqp]; omega))
    have h5 : 5 ≤ q.p ^ q.exponent := by
      rw [hqp, hq1, pow_one]
      exact five_le_of_prime hp.out hp3
    have hZ := center_eq_bot_of_G2 hq hmod h5
    exact seitzHyperGamma_eq_top_of_odd_carrier hI hOut (d := ⟨.G2 q, hv⟩) (q := q)
      (by omega) hq1 (Or.inr (Or.inr (Or.inr rfl))) (equivOfCenterEqBot hZ θ) hE h9
  ·
    obtain ⟨θ⟩ := hSp
    have hK : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 (by norm_num), pow_one]
    have h5 := five_le_of_prime hp.out hp3
    have hZ := center_eq_bot_of_projSp_two hq hZ3 (by rw [hK]; exact h5) θ
    exact seitzHyperGamma_eq_top_of_projSp_two_odd hI hOut (by omega) (equivOfCenterEqBot hZ θ) hE
      h9
  ·
    obtain ⟨θ⟩ := hL4
    have hK : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 (by norm_num), pow_one]
    have h5 := five_le_of_prime hp.out hp3
    have hZ := center_eq_bot_of_projSL_four hq hZ3 (by rw [hK]; exact h5) θ
    exact seitzHyperGamma_eq_top_of_projSL_four_odd hI hOut (by omega) (equivOfCenterEqBot hZ θ) hE
      h9
  ·
    obtain ⟨θ⟩ := hU4
    have h5 := five_le_of_prime hp.out hp3
    have hZ := center_eq_bot_of_projSU_four hq hZ3 le_rfl (by rw [pow_one]; omega) θ
    exact seitzHyperGamma_eq_top_of_projSU_four_odd hI hOut (by omega) (equivOfCenterEqBot hZ θ) hE
      h9
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    exact seitzHyperGamma_eq_top_of_L3Pi_narrow hA h199 hq hZ3 (by omega) (Or.inl rfl)
      (by norm_num) (by omega) hpi hE h9
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨θ⟩ := hL3
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    rcases pow_mod_three_cases (e := n) Nat.prime_two (by norm_num) with h1 | h2
    · exact seitzHyperGamma_eq_top_of_L3Pi_narrow hA h199 hq hZ3 (by omega) (Or.inl rfl)
        (by norm_num) (by omega) (Or.inl ⟨h1, ⟨θ⟩⟩) hE h9
    · have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      have hZ := center_eq_bot_of_projSL_three hq hZ3 (by rw [hK]; exact h2) θ
      exact seitzHyperGamma_eq_top_of_projSL_char2 hS2 (r := 2) le_rfl (by omega) rfl (by omega)
        (by omega) (equivOfCenterEqBot hZ θ) hE h9
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨θ⟩ := hU3
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    rcases pow_mod_three_cases (e := n) Nat.prime_two (by norm_num) with h1 | h2
    · have hZ := center_eq_bot_of_projSU_three hq hZ3 (by omega) h1 θ
      exact seitzHyperGamma_eq_top_of_projSU_char2 hS2 (r := 2) le_rfl (by omega) rfl (by omega)
        (equivOfCenterEqBot hZ θ) hE h9
    · exact seitzHyperGamma_eq_top_of_L3Pi_narrow hA h199 hq hZ3 (by omega) (Or.inl rfl)
        (by norm_num) (by omega) (Or.inr ⟨h2, ⟨θ⟩⟩) hE h9
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨θ⟩ := hSp
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hZ := center_eq_bot_of_projSp_two hq hZ3 (by rw [hK]; omega) θ
    exact seitzHyperGamma_eq_top_of_projSp_char2 hS2 (by omega) rfl (by omega)
      (equivOfCenterEqBot hZ θ) hE h9
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨θ⟩ := hU4
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have hZ := center_eq_bot_of_projSU_four hq hZ3 (by omega) (by omega) θ
    exact seitzHyperGamma_eq_top_of_projSU_char2 hS2 (r := 3) (by norm_num) (by omega) rfl
      (by omega) (equivOfCenterEqBot hZ θ) hE h9
  ·
    have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
      (Census.bridgeExceptional46.g2Even q hv hq2)
    have h16 : 2 ^ 4 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hq4
    have hZ := center_eq_bot_of_G2 hq hmod (by omega)
    refine seitzHyperGamma_eq_top_of_carrier_char2 hS2 (d := ⟨.G2 q, hv⟩) (scope_G2 q) ?_
      (not_isD2SeitzException_G2 q) (equivOfCenterEqBot hZ θ) hE h9
    change (LieTypeIndex.G2 q).characteristic = 2
    rw [LieTypeIndex.characteristic_G2, hq2]
  · exact absurd hd hD4
  ·
    have hZ := center_eq_bot_of_reeF4 hq hZ3 hm θ
    refine seitzHyperGamma_eq_top_of_carrier_char2 hS2 (d := ⟨.reeF4 m, hm⟩) (scope_reeF4 m) ?_
      (not_isD2SeitzException_reeF4 m) (equivOfCenterEqBot hZ θ) hE h9
    change (LieTypeIndex.reeF4 m).characteristic = 2
    rw [LieTypeIndex.characteristic_reeF4]

theorem seitz434Rest_of_narrow (hS2 : SeitzThreePartTwoChar2) (hA : SeitzThreeLThreePi)
    (h199 : Seitz199L3) (hI : SeitzThreeOddInner) (hOut : OddPrimeFieldPlanesInner)
    (h27 : Seitz434RestTwentySeven) : Seitz434Rest := by
  intro X _ _ hq hZ3 hL E hE hc
  rcases hc with ⟨h9, hD4⟩ | ⟨h27', hZ⟩
  · exact seitzHyperGamma_eq_top_rest_nine_narrow hS2 hA h199 hI hOut hq hZ3 hL hD4 hE h9
  · exact h27 X hq hZ hL E hE h27'

theorem seitz434_of_narrow_scopes (hS2 : SeitzThreePartTwoChar2) (hA : SeitzThreeLThreePi)
    (h199L3 : Seitz199L3) (h199D4 : Seitz199D4Two) (hI : SeitzThreeOddInner)
    (hOut : OddPrimeFieldPlanesInner) (h27 : Seitz434RestTwentySeven) : Seitz434 :=
  seitz434_of_rest_narrow h199D4 (seitz434Rest_of_narrow hS2 hA h199L3 hI hOut h27)

end CertsRestNine

end CFSG.RankThree.PartTwo.Sec4
