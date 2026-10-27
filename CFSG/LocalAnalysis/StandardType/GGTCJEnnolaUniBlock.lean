module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniBlock
import CFSG.LieType.SemisimpleCentralizers.HeldUCDForm
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.Sporadic.HeldB.Common
import Certificates.Certificate14953
import Certificates.Certificate7233Base
import Certificates.Certificate8166

public section

namespace CFSG.StandardType.TCJ

open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldUCD
  Polynomial Matrix
open CFSG.LocalAnalysis.GLTheoremA.K1419 (k1419ClsUniBlockPair)

private theorem adjM_aeval_eq_pow {L : Type} [Field L] [Finite L] {n Q t : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (ht : Odd t) (s : Matrix (Fin n) (Fin n) L)
    (hs : adjM τ s * s = 1) (hst : s ^ (Q ^ t + 1) = 1) (q : L[X]) :
    adjM τ (aeval s q) = aeval s q ^ (Q ^ t) := by
  classical
  obtain ⟨j, rfl⟩ := hQ
  haveI : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card hL)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = (2 ^ j) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hL
  obtain ⟨k, hk⟩ := ht
  have hx : ∀ y : L, y ^ ((2 ^ j) ^ 2) = y := fun y => by
    rw [← hcardL]; exact FiniteField.pow_card y
  have hxk : ∀ (y : L) (m : ℕ), y ^ (((2 ^ j) ^ 2) ^ m) = y := by
    intro y m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hx]
  have hfrob : ∀ x : L, x ^ ((2 ^ j) ^ t) = τ x := by
    intro x
    rw [hk, pow_succ, pow_mul (2 ^ j) 2 k, pow_mul x, hxk x k, hτQ]
  have hit : iterateFrobenius L 2 (j * t) = (τ : L →+* L) := by
    ext x
    rw [iterateFrobenius_def, pow_mul]
    exact hfrob x
  have hpoly : q ^ ((2 ^ j) ^ t) = expand L ((2 ^ j) ^ t) (q.map (τ : L →+* L)) := by
    rw [← pow_mul, ← Polynomial.map_iterateFrobenius_expand (p := 2) q (j * t),
      Polynomial.map_expand, hit]
  have hadj : adjM τ s = s ^ ((2 ^ j) ^ t) := by
    have h := adjM_eq_pow τ hτ (m := (2 ^ j) ^ t + 1) (Nat.succ_pos _) s hst hs
    simpa using h
  calc adjM τ (aeval s q) = aeval (adjM τ s) (q.map (τ : L →+* L)) := adjM_aeval τ hτ s q
    _ = aeval (s ^ ((2 ^ j) ^ t)) (q.map (τ : L →+* L)) := by rw [hadj]
    _ = aeval s (expand L ((2 ^ j) ^ t) (q.map (τ : L →+* L))) :=
        (Polynomial.expand_aeval _ _ _).symm
    _ = aeval s (q ^ ((2 ^ j) ^ t)) := by rw [hpoly]
    _ = aeval s q ^ ((2 ^ j) ^ t) := by rw [map_pow]

theorem k1419ClsUniEnnola {L : Type} [Field L] [Finite L] {n Q t : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (ht : Odd t)
    (s : GL (Fin n) L) (hs : s ∈ heldGU n L τ hτ) (hst : s ^ (Q ^ t + 1) = 1)
    (M : Subgroup (GL (Fin n) L))
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    ∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ dd ∣ t ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
          Nonempty (M ≃* heldSU a E τ' hτ') := by
  classical
  have hsm : (s : Matrix (Fin n) (Fin n) L) ^ (Q ^ t + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hst, Units.val_one]
  have hsa : adjM τ (s : Matrix (Fin n) (Fin n) L) * (s : Matrix (Fin n) (Fin n) L) = 1 :=
    mem_heldGU.mp hs
  have hQ' := hQ
  obtain ⟨j, hj⟩ := hQ'
  have ht1 : t ≠ 0 := by
    obtain ⟨k, hk⟩ := ht
    omega
  have hQ2 : 2 ∣ Q := by
    have h1 : 1 < Nat.card L := Finite.one_lt_card
    rw [hL] at h1
    have hQ1 : Q ≠ 1 := by
      rintro rfl
      simp at h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hQ1 (by simpa using hj)
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hodd : Odd (Q ^ t + 1) :=
    (even_iff_two_dvd.mpr (dvd_pow hQ2 ht1)).add_one
  haveI hchar : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card (n := j) (by rw [hL, hj]))
  have hord : (orderOf s : L) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff L 2] at h0
    have hd : orderOf s ∣ Q ^ t + 1 := orderOf_dvd_of_pow_eq_one hst
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h0.trans hd))
  obtain ⟨W, U, _, hW, _, hbr⟩ := k1419ClsUniBlockPair hτ hτQ hL s hs hord M hM
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    have h1 : 0 < Nat.card L := Nat.card_pos
    rw [hL] at h1
    simp at h1
  obtain ⟨c, hc⟩ : ∃ c, Q ^ t = c + 1 := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero t hQ0)
  rcases hbr with ⟨a, dd, E, hE, hEf, τ', hτ', P, ha, hτ'Q, hcardE, hMe, hPirr, hdeg, hPW⟩ |
    ⟨b, e, E, hE, _, X, Y, P, P', _, _, _, _, _, _, _, _, hPirr, _,
      hP'irr, hPX, hPY, hPmon, hP'mon, hPne, ⟨x, hx, y, hy, hxy⟩, _⟩
  · refine ⟨a, dd, E, hE, hEf, τ', hτ', ha, ?_, hτ'Q, hcardE, hMe⟩
    have hdvdP : P ∣ (X ^ (Q ^ t + 1) - 1 : L[X]) := by
      by_contra hnd
      obtain ⟨u, v, huv⟩ := (hPirr.coprime_iff_not_dvd).mpr hnd
      have h1 : aeval (s : Matrix (Fin n) (Fin n) L) u * aeval (s : Matrix (Fin n) (Fin n) L) P =
          1 := by
        have h2 := congrArg (aeval (s : Matrix (Fin n) (Fin n) L)) huv
        simp only [map_add, map_mul, map_one, map_sub, map_pow, aeval_X, hsm, sub_self, mul_zero,
          add_zero] at h2
        exact h2
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have h3 := congrArg (fun m => Matrix.mulVec m w) h1
      simp only [← Matrix.mulVec_mulVec, hPW w hwW, Matrix.mulVec_zero, Matrix.one_mulVec] at h3
      exact hw0 h3.symm
    have hdvd2 : P ∣ (X ^ (Nat.card L) ^ t - X : L[X]) := by
      refine hdvdP.trans ?_
      have h1 : (X ^ (Nat.card L) ^ t - X : L[X]) = X * ((X ^ (c + 2)) ^ c - 1) := by
        have h2 : (Nat.card L) ^ t = (c + 2) * c + 1 := by
          rw [hL, ← pow_mul, mul_comm, pow_mul, hc]
          ring
        rw [h2, pow_succ, pow_mul]
        ring
      rw [h1]
      refine Dvd.dvd.mul_left ?_ X
      have h3 := sub_dvd_pow_sub_pow (X ^ (c + 2) : L[X]) 1 c
      rw [one_pow] at h3
      have h4 : Q ^ t + 1 = c + 2 := by omega
      rw [h4]
      exact h3
    have h5 := hPirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd2
    rwa [hdeg] at h5
  · exfalso
    obtain ⟨u, v, huv⟩ : IsCoprime P P' := by
      rw [hPirr.coprime_iff_not_dvd]
      intro hdv
      exact hPne (Polynomial.eq_of_monic_of_associated hPmon hP'mon
        (hPirr.associated_of_dvd hP'irr hdv))
    set A : Matrix (Fin n) (Fin n) L := aeval (s : Matrix (Fin n) (Fin n) L) (u * P) with hA
    set B' : Matrix (Fin n) (Fin n) L := aeval (s : Matrix (Fin n) (Fin n) L) (v * P') with hB'
    have hAB : A + B' = 1 := by
      rw [hA, hB', ← map_add, huv, map_one]
    have hAx : A *ᵥ x = 0 := by
      rw [hA, map_mul, ← Matrix.mulVec_mulVec, hPX x hx, Matrix.mulVec_zero]
    have hBy : B' *ᵥ y = 0 := by
      rw [hB', map_mul, ← Matrix.mulVec_mulVec, hPY y hy, Matrix.mulVec_zero]
    have hy' : y = A *ᵥ y := by
      have h2 : (A + B') *ᵥ y = y := by rw [hAB, Matrix.one_mulVec]
      rw [Matrix.add_mulVec, hBy, add_zero] at h2
      exact h2.symm
    have hadj : adjM τ A = A ^ (Q ^ t) :=
      adjM_aeval_eq_pow hτ hτQ hL hQ ht _ hsa hsm (u * P)
    have hAp : A ^ (Q ^ t) *ᵥ x = 0 := by
      rw [hc, pow_succ, ← Matrix.mulVec_mulVec, hAx, Matrix.mulVec_zero]
    apply hxy
    calc hfm τ x y = hfm τ x (A *ᵥ y) := by rw [← hy']
      _ = hfm τ (adjM τ A *ᵥ x) y := by rw [hfm_mulVec, adjM_adjM τ hτ]
      _ = 0 := by rw [hadj, hAp]; simp [hfm]

end CFSG.StandardType.TCJ

end
