module

public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Two
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
import CFSG.LocalAnalysis.StandardType.GGTwE6K1Toral
import CFSG.LocalAnalysis.StandardType.GGTwE6K1D4
import CFSG.LocalAnalysis.StandardType.GGTwE6K1A2InnerRank
import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2TwoModel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.Walter.J1Props
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

private theorem a5kType_card_centerQuot {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) :
    Nat.card (X ⧸ Subgroup.center X) = CFSG.Open.ordTwistedA 5 (2 ^ n) := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ :=
    largeEvenRawDatum_exists ((largeEvenRawDatum_legacy _ _).2 hraw)
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .PSU) (n := 6) (f := n)
    ⟨⟨Nat.prime_two, hn, by norm_num, by simp⟩, K, inferInstance, inferInstance, hK, ⟨θ⟩⟩).2.1 rfl

private theorem a5kType_card_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card (Y ⧸ Subgroup.center Y) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

private theorem a5kType_false {X : Type*} {n m N : ℕ} {Z : ℕ → Prop} (hn : 1 ≤ n)
    (hP : CFSG.Timmesfeld.Orders.Profile m N Z) (hN : N ≠ n * 15)
    (hX : Nat.card X = CFSG.Open.ordTwistedA 5 (2 ^ n)) (hX' : Nat.card X = m) : False := by
  have hU := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 5) (g := n) (by norm_num) hn
  rw [← hX, hX'] at hU
  exact hN (hP.transfer hU).1


theorem twE6MatFixDim_eq_36_of_twA5 (hS : E6LeviThreeToralBar)
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {h : twistedE6InndiagGL K σ} (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hfE : twistedE6InndiagConj K σ h ∈ E)
    (hEI : E ≤ (twistedE6InndiagConj K σ).range)
    (hnt : ¬ E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
      (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))))
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hEJ : ∀ e ∈ E, J.map e.toMonoidHom = J)
    (hCJ : ∀ e ∈ E, (∀ c ∈ J, e c = c) → e ∈ Subgroup.zpowers (twistedE6InndiagConj K σ h))
    (hmark : LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    twE6MatFixDim K σ h = 36 := by
  have hJc := a5kType_card_centerQuot hn hmark
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by
    rw [hchar]
    decide
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ (2 ^ n) hσ hK hq2
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ (2 ^ n) hK3 hσ hK hq2 h hh1 hh3
  have he : D.e = n := by
    have h1 := D.hqe
    rw [hchar] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  obtain ⟨i, -, hJi⟩ := D.exists_rationalComponent hJ
  have hJR := a5kType_card_congr
    ((J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi))
  have hmem := twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h24 | h28 | h30 | h36 | h46
  ·
    exfalso
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      obtain ⟨-, hm⟩ := statedClassicalModel_component_threeA2_two hK hσ hh1 hh3 h24 hJ
      exact a5kType_false le_rfl
        (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := 3) le_rfl (by norm_num))
        (by decide) hJc ((CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.1 rfl)
    have hq2' : 2 ^ n ≠ 2 := by
      intro h22
      have h21 : 2 ^ n = 2 ^ 1 := h22.trans (pow_one 2).symm
      have := Nat.pow_right_injective (le_refl 2) h21
      omega
    by_cases hin : twistedE6InndiagConj K σ h ∈ twistedE6Inn K σ
    · obtain ⟨s, hs, hs3, -, hsd⟩ := exists_inner_of_mem_twistedE6Inn hσ hK hq2 hh3 hh1 hin
      rw [← hs] at hfE hJ hCJ
      exact false_of_inner_threeA2 hK3 hσ hK h3 hq2' hs3 (hsd.trans h24) hE hcard hEI hfE hJ
        hEJ hCJ
    obtain ⟨-, -, hm⟩ := D.rationalComponent_a2out h24 h3 hq2' hin i
    rw [hchar, he] at hm
    exact a5kType_false hn
      (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := n * 3) le_rfl (by omega))
      (by show n * 3 * 3 ≠ n * 15; omega) hJc
      (hJR.trans ((CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.1 rfl))
  ·
    exact absurd (e6AdToral_of_conn_line hS D (Or.inl h28) (isElemAbelian_baseChange_comap hinj hE)
      (baseChange_comap_le_adjointGroup E) (baseChange_comap_commute hinj hE hfE)) hnt
  ·
    exfalso
    rcases lieModel_rationalComponent_d4t2 D h3 h30 i with hm | hm <;> rw [hchar, he] at hm
    · rcases hm with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact a5kType_false hn
          (CFSG.Timmesfeld.Orders.profile_ordD (n := 4) (by norm_num) hn)
          (by show n * 12 ≠ n * 15; omega) hJc
          (hJR.trans ((CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl))
      all_goals exact absurd h0 (by decide)
    · rcases hm with ⟨hc, -⟩ | ⟨-, -, hm⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
      · exact absurd hc (by decide)
      · exact a5kType_false hn (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hn) (by omega) hJc
          (hJR.trans (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm))
      all_goals exact absurd hc (by decide)
  ·
    exact h36
  ·
    exact absurd (e6AdToral_of_conn_line hS D (Or.inr h46) (isElemAbelian_baseChange_comap hinj hE)
      (baseChange_comap_le_adjointGroup E) (baseChange_comap_commute hinj hE hfE)) hnt

end CFSG.StandardType.SCFourCover

end
