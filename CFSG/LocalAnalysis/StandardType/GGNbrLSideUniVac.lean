module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniType
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniNu
import CFSG.LieType.AschbacherSeitz.UnitaryInvolutionRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
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
import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)
open CFSG.LieType.SemisimpleCentralizers.HeldUCD (hfm)

theorem hfm_finrank_le_two_four {L : Type} [Field L] [Finite L] {j : ℕ} (hj : 1 ≤ j)
    {τ : L ≃+* L} (hτQ : ∀ x, τ x = x ^ 2 ^ j) (hL : Nat.card L = (2 ^ j) ^ 2)
    (X : Submodule L (Fin 4 → L)) (hX : ∀ x ∈ X, ∀ x' ∈ X, hfm τ x x' = 0) :
    Module.finrank L ↥X ≤ 2 := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 j L :=
    ⟨Nat.prime_two, hj, by rw [hL, ← pow_mul, mul_comm]⟩
  refine CFSG.LieType.AschbacherSeitz.finrank_le_two_of_totallyIsotropic h rfl X ?_
  intro x hx y hy
  have h0 := hX x hx y hy
  simpa [CFSG.LinearGroups.stdHermForm_apply, CFSG.LieType.SemisimpleCentralizers.HeldUCD.hfm,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, hτQ] using h0

private lemma pairMod3_three_dvd_four_pow_sub_one (m : ℕ) : 3 ∣ 4 ^ m - 1 := by
  have h4mod : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have hpow : (4 : ℕ) ^ m ≡ 1 [MOD 3] := by simpa using h4mod.pow m
  exact hpow.symm.dvd'

private lemma pairMod3_three_dvd_sq_two_pow_sub_one (j : ℕ) : 3 ∣ (2 ^ j) ^ 2 - 1 := by
  have h : (2 ^ j) ^ 2 = 4 ^ j := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h]
  exact pairMod3_three_dvd_four_pow_sub_one j

private lemma pairMod3_exists_cube_root_unity_of_three_dvd {L : Type} [Field L] [Finite L]
    (h : 3 ∣ Nat.card L - 1) : ∃ w : L, w ^ 3 = 1 ∧ w ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3u : 3 ∣ Nat.card Lˣ := by rwa [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) 3 h3u
  have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
  have hωne : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    omega
  exact ⟨(ω : L), by simpa using congrArg (fun u : Lˣ => (u : L)) hω3,
    fun h1 => hωne (Units.ext h1)⟩

private lemma pairMod3_dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero {L : Type} [Field L]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) L) {P : Polynomial L} (hirr : Irreducible P)
    {x : Fin n → L} (hx : x ≠ 0) {c : L} (hP : Polynomial.aeval A P *ᵥ x = 0)
    (hA3 : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) L)) :
    P ∣ Polynomial.X ^ 3 - Polynomial.C c := by
  have hCc : Polynomial.aeval A (Polynomial.X ^ 3 - Polynomial.C c) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hA3,
      Algebra.algebraMap_eq_smul_one, sub_self]
  by_contra hndvd
  have hcop : IsCoprime P (Polynomial.X ^ 3 - Polynomial.C c) :=
    hirr.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨u, v, huv⟩ := hcop
  have key : Polynomial.aeval A (u * P + v * (Polynomial.X ^ 3 - Polynomial.C c)) *ᵥ x = 0 := by
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_mul, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hCc]
    simp
  rw [huv, Polynomial.aeval_one, Matrix.one_mulVec] at key
  exact hx key

private lemma pairMod3_pow_three_eq_of_eigenvalue {L : Type} [Field L] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) L} {c p : L}
    (hA3 : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) L)) {x : Fin n → L} (hx : x ≠ 0)
    (hpx : A *ᵥ x = p • x) : p ^ 3 = c := by
  have hk : ∀ k : ℕ, A ^ k *ᵥ x = p ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hpx, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ']
  have h : A ^ 3 *ᵥ x = c • x := by rw [hA3, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : (p ^ 3 - c) • x = 0 := by
    rw [sub_smul, ← hk 3, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)

private lemma pairMod3_splits_X_pow_three_sub_C {L : Type} [Field L] {c p w : L}
    (hw3 : w ^ 3 = 1) (hwne : w ≠ 1) (hp3 : p ^ 3 = c) :
    (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).Splits := by
  have hζ : IsPrimitiveRoot w 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    have h : orderOf w ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hw3
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf w) h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hwne
    · exact h3
  exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ hp3

private lemma pairMod3_eigenvalue_of_eq_X_add_C {L : Type} [Field L] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) L} {P : Polynomial L} {b : L}
    (hP : P = Polynomial.X + Polynomial.C b) {X : Submodule L (Fin n → L)}
    (hPX : ∀ x ∈ X, Polynomial.aeval A P *ᵥ x = 0) :
    ∀ x ∈ X, A *ᵥ x = (-b) • x := by
  intro x hx
  have h := hPX x hx
  rw [hP, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, add_eq_zero_iff_eq_neg] at h
  rw [h, neg_smul]

theorem ggNbrLSideUni_pairedModThree {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (hQ : ∃ j : ℕ, Q = 2 ^ j) (A : GL (Fin n) L) (hA : A ∈ heldGU n L τ hτ) (c : L)
    (hA3 : ((A ^ 3 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      c • (1 : Matrix (Fin n) (Fin n) L))
    (X Y : Submodule L (Fin n → L)) (P P' : Polynomial L)
    (hirr : Irreducible P) (hirr' : Irreducible P') (hm : P.Monic) (hm' : P'.Monic)
    (hne : P ≠ P')
    (hPk : ∀ x ∈ X, (Polynomial.aeval (A : Matrix (Fin n) (Fin n) L) P) *ᵥ x = 0)
    (hPk' : ∀ y ∈ Y, (Polynomial.aeval (A : Matrix (Fin n) (Fin n) L) P') *ᵥ y = 0)
    (hpair : ∃ x ∈ X, ∃ y ∈ Y, hfm τ x y ≠ 0) :
    Q % 3 = 1 := by
  obtain ⟨x, hxX, y, hyY, hxy⟩ := hpair
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxy
    rw [hx]
    simp [hfm]
  have hy0 : y ≠ 0 := by
    intro hy
    apply hxy
    rw [hy]
    simp [hfm]
  have hA3mat : (A : Matrix (Fin n) (Fin n) L) ^ 3 =
      c • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [← Units.val_pow_eq_pow_val]
    exact hA3
  have hdvdP : P ∣ Polynomial.X ^ 3 - Polynomial.C c :=
    pairMod3_dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero
      (A : Matrix (Fin n) (Fin n) L) hirr hx0 (hPk x hxX) hA3mat
  have hdvdP' : P' ∣ Polynomial.X ^ 3 - Polynomial.C c :=
    pairMod3_dvd_X_pow_three_sub_C_of_aeval_mulVec_eq_zero
      (A : Matrix (Fin n) (Fin n) L) hirr' hy0 (hPk' y hyY) hA3mat
  have hndvd : ¬ P ∣ P' := by
    intro hdvd
    exact hne (Polynomial.eq_of_monic_of_associated hm hm'
      (hirr.associated_of_dvd hirr' hdvd))
  have hcop : IsCoprime P P' := hirr.coprime_iff_not_dvd.mpr hndvd
  have hdvdProd : P * P' ∣ Polynomial.X ^ 3 - Polynomial.C c :=
    hcop.mul_dvd hdvdP hdvdP'
  have htarget_ne : (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 3) c
  have hdegsum : P.natDegree + P'.natDegree ≤ 3 := by
    have hle := Polynomial.natDegree_le_of_dvd hdvdProd htarget_ne
    have hmul : (P * P').natDegree = P.natDegree + P'.natDegree :=
      Polynomial.natDegree_mul hm.ne_zero hm'.ne_zero
    have hX3 : (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).natDegree = 3 :=
      Polynomial.natDegree_X_pow_sub_C
    omega
  have h3L : 3 ∣ Nat.card L - 1 := by
    obtain ⟨j, rfl⟩ := hQ
    rw [hL]
    exact pairMod3_three_dvd_sq_two_pow_sub_one j
  obtain ⟨w, hw3, hwne⟩ := pairMod3_exists_cube_root_unity_of_three_dvd h3L
  by_cases hP1 : P.natDegree = 1
  ·
    set p : L := -(P.coeff 0) with hpdef
    have hPform : P = Polynomial.X + Polynomial.C (P.coeff 0) := hm.eq_X_add_C hP1
    have hp : ∀ x ∈ X, (A : Matrix (Fin n) (Fin n) L) *ᵥ x = p • x := by
      intro x hx
      have h := pairMod3_eigenvalue_of_eq_X_add_C
        (A := (A : Matrix (Fin n) (Fin n) L)) hPform (X := X) hPk x hx
      rw [hpdef]
      exact h
    have hp3 : p ^ 3 = c :=
      pairMod3_pow_three_eq_of_eigenvalue hA3mat hx0 (hp x hxX)
    have hsplit : (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).Splits :=
      pairMod3_splits_X_pow_three_sub_C hw3 hwne hp3
    have hsplitP' : P'.Splits := hsplit.of_dvd htarget_ne hdvdP'
    have hP'1 : P'.natDegree = 1 := hsplitP'.natDegree_eq_one_of_irreducible hirr'
    set q : L := -(P'.coeff 0) with hqdef
    have hP'form : P' = Polynomial.X + Polynomial.C (P'.coeff 0) := hm'.eq_X_add_C hP'1
    have hq : ∀ y ∈ Y, (A : Matrix (Fin n) (Fin n) L) *ᵥ y = q • y := by
      intro y hy
      have h := pairMod3_eigenvalue_of_eq_X_add_C
        (A := (A : Matrix (Fin n) (Fin n) L)) hP'form (X := Y) hPk' y hy
      rw [hqdef]
      exact h
    have hpq : p ≠ q := by
      intro hpq
      apply hne
      have hb : P.coeff 0 = P'.coeff 0 := by
        have h : -(P.coeff 0) = -(P'.coeff 0) := by
          rw [← hpdef, ← hqdef]
          exact hpq
        exact neg_inj.mp h
      rw [hPform, hP'form, hb]
    exact CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsUniNuOfPair hτ hτQ hL hQ A hA c hA3
      X Y ⟨x, hxX, y, hyY, hxy⟩ p q hp hq hpq
  ·
    have hP'1 : P'.natDegree = 1 := by
      have h1 : 1 ≤ P.natDegree := hirr.natDegree_pos
      have h2 : 1 ≤ P'.natDegree := hirr'.natDegree_pos
      omega
    set q : L := -(P'.coeff 0) with hqdef
    have hP'form : P' = Polynomial.X + Polynomial.C (P'.coeff 0) := hm'.eq_X_add_C hP'1
    have hq : ∀ y ∈ Y, (A : Matrix (Fin n) (Fin n) L) *ᵥ y = q • y := by
      intro y hy
      have h := pairMod3_eigenvalue_of_eq_X_add_C
        (A := (A : Matrix (Fin n) (Fin n) L)) hP'form (X := Y) hPk' y hy
      rw [hqdef]
      exact h
    have hq3 : q ^ 3 = c :=
      pairMod3_pow_three_eq_of_eigenvalue hA3mat hy0 (hq y hyY)
    have hsplit : (Polynomial.X ^ 3 - Polynomial.C c : Polynomial L).Splits :=
      pairMod3_splits_X_pow_three_sub_C hw3 hwne hq3
    have hsplitP : P.Splits := hsplit.of_dvd htarget_ne hdvdP
    have hP1' : P.natDegree = 1 := hsplitP.natDegree_eq_one_of_irreducible hirr
    set p : L := -(P.coeff 0) with hpdef
    have hPform : P = Polynomial.X + Polynomial.C (P.coeff 0) := hm.eq_X_add_C hP1'
    have hp : ∀ x ∈ X, (A : Matrix (Fin n) (Fin n) L) *ᵥ x = p • x := by
      intro x hx
      have h := pairMod3_eigenvalue_of_eq_X_add_C
        (A := (A : Matrix (Fin n) (Fin n) L)) hPform (X := X) hPk x hx
      rw [hpdef]
      exact h
    have hpq : p ≠ q := by
      intro hpq
      apply hne
      have hb : P.coeff 0 = P'.coeff 0 := by
        have h : -(P.coeff 0) = -(P'.coeff 0) := by
          rw [← hpdef, ← hqdef]
          exact hpq
        exact neg_inj.mp h
      rw [hPform, hP'form, hb]
    exact CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsUniNuOfPair hτ hτQ hL hQ A hA c hA3
      X Y ⟨x, hxX, y, hyY, hxy⟩ p q hp hq hpq

theorem ggNbrLSideUni_noPSL3 (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {K : Type} [Field K] [Finite K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x) {j d : ℕ}
    (hj : 1 ≤ j) (hτQ : ∀ x, τ x = x ^ 2 ^ j) (hK : Nat.card K = (2 ^ j) ^ 2) (hd : 3 ≤ d)
    (hsplit : d = 4 ∨ 3 ∣ 2 ^ j + 1)
    (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ)
    (hA3 : ∃ c : K, ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      c • (1 : Matrix (Fin d) (Fin d) K))
    (hAns : ∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K))
    (M : Subgroup (GL (Fin d) K))
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ))
    {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F)
    (e : ↥M ⧸ Subgroup.center ↥M ≃* projectiveSL 3 F) : False := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc⟩ := hA3
  have h2 : (2 : K) = 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card (K := K) (n := j) hK
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd1 A
      (by norm_num : Odd 3) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hMgu : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldGU d K τ hτ) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isComponentOf_centralizer_gu_of_su hτ A hM
  have hqs : CFSG.IsQuasisimple ↥M :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥M).2.2.1).2 hM.2.2
  obtain ⟨W, U, hWU, hWne, hfix, htype⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsUniBlockPair hτ hτQ hK A hA hord M hMgu
  rcases htype with ⟨a, dd, E, hEfld, hEfin, τ', hτ', P, ha2, hτ'Q, hEcard, ⟨eM⟩, hirrP,
      hPdeg, hPkill⟩ | ⟨b, e', E, hEfld, hEfin, X, Y, P, P', hb2, hEcard, ⟨eM⟩, hWXY,
      hXne, hYne, hXi, hYi, hirrP, hPdeg, hirrP', hPkill, hP'kill, hm, hm', hne, hpair, hfin⟩
  ·
    have hdd : 0 < dd := hPdeg ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirrP)
    have hQd : (2 ^ j) ^ dd = 2 ^ (j * dd) := (pow_mul 2 j dd).symm
    have hEc : Nat.card E = (2 ^ (j * dd)) ^ 2 := by rw [hEcard, hQd]
    have hτ'Q' : ∀ y : E, τ' y = y ^ 2 ^ (j * dd) := fun y => by rw [hτ'Q y, hQd]
    obtain ⟨t, m, htm, hmodel⟩ :=
      ggNbrLSideUni_typeSU (Nat.mul_pos hj hdd) hEc hτ'Q' eM hqs
    obtain ⟨ht, hm3, -⟩ := ggNbrLSideExcl hDet hO hF4 e hmodel
    rcases htm with ⟨h1, -⟩ | ⟨-, h2'⟩
    · rw [h1] at ht
      exact absurd ht (by decide)
    · omega
  ·
    have he1 : 0 < e' := hPdeg ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirrP)
    rcases hsplit with rfl | h3
    ·
      have hX2 := hfm_finrank_le_two_four hj hτQ hK X hXi
      have hb : b ≤ 2 := by
        have : b ≤ e' * b := Nat.le_mul_of_pos_left b he1
        omega
      have hE : Nat.card E = 2 ^ (j * (2 * e')) := by rw [hEcard, ← pow_mul]
      have hfpos : 1 ≤ j * (2 * e') := Nat.mul_pos hj (by omega)
      have hmodel := ggNbrLSideUni_typeSL hfpos hE eM hqs
      obtain ⟨-, hm3, -⟩ := ggNbrLSideExcl hDet hO hF4 e hmodel
      omega
    ·
      have hmod := ggNbrLSideUni_pairedModThree hτ hτQ hK ⟨j, rfl⟩ A hA c hc X Y P P'
        hirrP hirrP' hm hm' hne hPkill hP'kill hpair
      generalize 2 ^ j = N at hmod h3
      omega

end CFSG.StandardType
