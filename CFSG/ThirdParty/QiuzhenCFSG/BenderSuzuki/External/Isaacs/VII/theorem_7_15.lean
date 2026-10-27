module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Isaacs Corollary 7.15

An equal-degree family of at least two irreducible characters is coherent for
any integral isometry on its degree-zero character lattice.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace VII

open Section1 Section5

universe u

private theorem isaacs_7_15_positive_degree_nat
    {L : Type u} [Group L] [Finite L]
    {chi : ClassFunction L}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    exists n : Nat, 0 < n /\ degree chi = (n : Complex) := by
  rcases hchi with ⟨n, rho, hrho, hchar⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : degree chi = 0 := by
      simp [hchar, degree_representation_character rho, hn0]
    exact Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup chi
      ⟨n, rho, hrho, hchar⟩ hdeg
  · rw [hchar]
    simpa using degree_representation_character rho

private theorem isaacs_7_15_agrees_on_equal_degree_lattice
    {N G : Type u} [Group N] [Finite N] [Group G] [Finite G]
    (Y : Finset (ClassFunction N))
    (tau Tnew : ClassFunction N →ₗ[Complex] ClassFunction G)
    (X : Y)
    (hXdegree : degree (X : ClassFunction N) ≠ 0)
    (hdegree : forall Z : Y,
      degree (Z : ClassFunction N) = degree (X : ClassFunction N))
    (hsplit : forall Z : Y,
      tau ((X : ClassFunction N) - (Z : ClassFunction N)) =
        Tnew (X : ClassFunction N) - Tnew (Z : ClassFunction N)) :
    agreesOnIntegerSpanOn Y puncturedSet tau Tnew := by
  classical
  intro phi hphi
  rcases hphi with ⟨⟨v, hv⟩, hphiSupport⟩
  let sourceFamily : Y → ClassFunction N := fun Z => (Z : ClassFunction N)
  let s : Int := ∑ Z : Y, v Z
  have hphiDegree : degree phi = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero phi).1 hphiSupport
  have hdegreeEval :
      degree phi =
        ∑ Z : Y, (v Z : Complex) * degree (Z : ClassFunction N) := by
    rw [hv, Section1.evalCoeff, Section1.degree_apply]
    simp [Section1.degree_apply]
  have hfactor :
      ∑ Z : Y, (v Z : Complex) * degree (Z : ClassFunction N) =
        (s : Complex) * degree (X : ClassFunction N) := by
    calc
      ∑ Z : Y, (v Z : Complex) * degree (Z : ClassFunction N) =
          ∑ Z : Y, (v Z : Complex) * degree (X : ClassFunction N) := by
            refine Finset.sum_congr rfl ?_
            intro Z _
            rw [hdegree Z]
      _ = (s : Complex) * degree (X : ClassFunction N) := by
            simp [s, Finset.sum_mul]
  have hsum0 : (s : Complex) = 0 := by
    have hmul : (s : Complex) * degree (X : ClassFunction N) = 0 := by
      rw [← hfactor, ← hdegreeEval, hphiDegree]
    exact (mul_eq_zero.mp hmul).resolve_right hXdegree
  have hsourceEval :
      Section1.evalCoeff
          (fun Z : Y => (X : ClassFunction N) - (Z : ClassFunction N)) v =
        ((s : Complex) • (X : ClassFunction N)) - phi := by
    rw [hv]
    ext g
    simp [Section1.evalCoeff, s, Pi.smul_apply, mul_comm, mul_sub]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Z _
    ring
  have htargetEval :
      Section1.evalCoeff
          (fun Z : Y => tau ((X : ClassFunction N) - (Z : ClassFunction N))) v =
        ((s : Complex) • Tnew (X : ClassFunction N)) -
          Section1.evalCoeff (fun Z : Y => Tnew (Z : ClassFunction N)) v := by
    have hsplitEval :
        Section1.evalCoeff
            (fun Z : Y => tau ((X : ClassFunction N) - (Z : ClassFunction N))) v =
          Section1.evalCoeff
            (fun Z : Y =>
              Tnew (X : ClassFunction N) - Tnew (Z : ClassFunction N)) v := by
      congr 1
      funext Z
      exact hsplit Z
    rw [hsplitEval]
    ext g
    simp [Section1.evalCoeff, s, Pi.smul_apply, mul_sub,
      Finset.sum_sub_distrib, Finset.sum_mul]
  have hmapSource :
      Section1.evalCoeff
          (fun Z : Y => tau ((X : ClassFunction N) - (Z : ClassFunction N))) v =
        tau (Section1.evalCoeff
          (fun Z : Y => (X : ClassFunction N) - (Z : ClassFunction N)) v) := by
    simp [Section1.evalCoeff]
  have hnewEval :
      Section1.evalCoeff (fun Z : Y => Tnew (Z : ClassFunction N)) v = tau phi := by
    have hEq :
        ((s : Complex) • Tnew (X : ClassFunction N)) -
            Section1.evalCoeff (fun Z : Y => Tnew (Z : ClassFunction N)) v =
          tau (((s : Complex) • (X : ClassFunction N)) - phi) := by
      calc
        ((s : Complex) • Tnew (X : ClassFunction N)) -
            Section1.evalCoeff (fun Z : Y => Tnew (Z : ClassFunction N)) v =
          Section1.evalCoeff
            (fun Z : Y => tau ((X : ClassFunction N) - (Z : ClassFunction N))) v :=
              htargetEval.symm
        _ = tau (Section1.evalCoeff
            (fun Z : Y => (X : ClassFunction N) - (Z : ClassFunction N)) v) :=
              hmapSource
        _ = tau (((s : Complex) • (X : ClassFunction N)) - phi) := by
              rw [hsourceEval]
    simp [hsum0] at hEq
    exact hEq
  calc
    Tnew phi = Tnew (Section1.evalCoeff sourceFamily v) := by rw [hv]
    _ = Section1.evalCoeff (fun Z : Y => Tnew (Z : ClassFunction N)) v := by
      simp [sourceFamily, Section1.evalCoeff]
    _ = tau phi := hnewEval

private theorem isaacs_7_15_equal_degree_extension_fields
    {N G : Type u} [Group N] [Finite N] [Group G] [Finite G]
    (Y : Finset (ClassFunction N))
    (tau : ClassFunction N →ₗ[Complex] ClassFunction G)
    (hirr : forall X : Y,
      IsIrreducibleCharacterOnGroup (X : ClassFunction N))
    (hisometry : isCFLinearIsometryOnSpanOn Y puncturedSet tau)
    (hdegreeZero :
      forall chi : ClassFunction N, integerSpanOn Y puncturedSet chi ->
        Theory.Character.IsVirtualCharacter (tau chi) /\
          supportedOn (tau chi) puncturedSet)
    (hdeg : forall X Z : Y,
      degree (X : ClassFunction N) = degree (Z : ClassFunction N))
    (hcard : 2 <= Y.card) :
    exists Tnew : ClassFunction N →ₗ[Complex] ClassFunction G,
      isCFLinearIsometryOnSpan Y Tnew /\
        mapsIntegerSpanToVirtualCharacters Y Tnew /\
          agreesOnIntegerSpanOn Y puncturedSet tau Tnew := by
  classical
  let n : Nat := Y.card
  have hn : 2 <= n := by simpa [n] using hcard
  letI : NeZero n := ⟨by omega⟩
  let e : Fin n ≃ Y := by
    simpa [n] using (Fintype.equivFin Y).symm
  let chi : Fin n -> ClassFunction N := fun i => (e i : ClassFunction N)
  have hchiBasis : IsIrreducibleCharacterBasis chi := by
    constructor
    · intro i
      exact hirr (e i)
    · intro i j hij hEq
      apply hij
      apply e.injective
      exact Subtype.ext hEq
  have hchiOrth : IsOrthonormalFamily chi := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hself :=
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (hirr (e i))).2
      change scalarProduct N (e i : ClassFunction N) (e i : ClassFunction N) = 1 at hself
      simpa [chi] using hself
    · have hne : (e i : ClassFunction N) ≠ (e j : ClassFunction N) := by
        intro hEq
        apply hij
        apply e.injective
        exact Subtype.ext hEq
      simpa [chi, hij] using scalarProduct_isBookIrreducible_ne
        (e i : ClassFunction N) (e j : ClassFunction N)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hirr (e i)))
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hirr (e j))) hne
  have hchiDeg : forall i : Fin n, degree (chi i) = degree (chi 0) := by
    intro i
    exact hdeg (e i) (e 0)

  let basisExist := Theory.Character.irreducible_characters_form_basis (G := G)
  let iota := Classical.choose basisExist
  let basisExist1 := Classical.choose_spec basisExist
  let instIota : Fintype iota := Classical.choose basisExist1
  let basisExist2 := Classical.choose_spec basisExist1
  let targetChi := Classical.choose basisExist2
  have htargetChi : Theory.Character.IsCompleteIrreducibleCharacterFamily targetChi :=
    (Classical.choose_spec basisExist2).1
  let basisExist3 := (Classical.choose_spec basisExist2).2
  let b := Classical.choose basisExist3
  have hb : forall i : iota, b i = targetChi i := Classical.choose_spec basisExist3
  letI : Fintype iota := instIota
  letI : DecidableEq iota := Classical.decEq iota
  let muBasis : iota -> ClassFunction G := fun i => ofConjClassFunction (targetChi i)
  have hmuBasis : IsIrreducibleCharacterBasis muBasis := by
    constructor
    · intro i
      exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (htargetChi.1 i)
    · intro i j hij hEq
      apply hij
      apply htargetChi.2.2
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      have hEqg := congrFun hEq g
      simpa [muBasis, ofConjClassFunction] using hEqg
  let d : iota -> Nat := fun i =>
    Classical.choose (isaacs_7_15_positive_degree_nat (hmuBasis.1 i))
  have hdpos : forall i, 0 < d i := by
    intro i
    exact (Classical.choose_spec
      (isaacs_7_15_positive_degree_nat (hmuBasis.1 i))).1
  have hmuDeg : forall i, degree (muBasis i) = (d i : Complex) := by
    intro i
    exact (Classical.choose_spec
      (isaacs_7_15_positive_degree_nat (hmuBasis.1 i))).2

  let alpha : Fin n -> ClassFunction N := fun i => chi i - chi 0
  have halphaSpan : forall i : Fin n, integerSpanOn Y puncturedSet (alpha i) := by
    intro i
    refine ⟨integerSpan_sub
      (integerSpan_of_mem Y (e i).2)
      (integerSpan_of_mem Y (e 0).2), ?_⟩
    apply (supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change degree (chi i) - degree (chi 0) = 0
    rw [hchiDeg i]
    simp
  have hTauVirt : forall i : Fin n,
      Theory.Character.IsVirtualCharacter (tau (alpha i)) := by
    intro i
    exact (hdegreeZero (alpha i) (halphaSpan i)).1
  have hTauDeg : forall i : Fin n, degree (tau (alpha i)) = 0 := by
    intro i
    exact (supportedOn_puncturedSet_iff_degree_eq_zero _).1
      (hdegreeZero (alpha i) (halphaSpan i)).2
  have hInt : forall i : Fin n, forall j : iota,
      exists z : Int, scalarProduct G (tau (alpha i)) (muBasis j) = (z : Complex) := by
    intro i j
    exact Section3.scalarProduct_isVirtualCharacter_eq_int (hTauVirt i)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hmuBasis.1 j))
  let rawCoeff : Fin n -> CoeffVector iota := fun i =>
    Section3.irreducibleBasisCoeff (tau (alpha i)) (hInt i)
  have hEvalRaw : forall i : Fin n,
      evalCoeff muBasis (rawCoeff i) = tau (alpha i) := by
    intro i
    exact Section3.irreducibleBasis_evalCoeff_coeff htargetChi b hb (tau (alpha i))
      (Section3.isVirtualCharacter_isClassFunction (hTauVirt i)) (hInt i)
  let coeff : Fin n -> CoeffVector iota := fun i => if i = 0 then 0 else rawCoeff i
  have hcoeff0 : coeff 0 = 0 := by simp [coeff]
  have hCoeffIso : forall i j : Fin n,
      (coeffDot (coeff i) (coeff j) : Complex) =
        scalarProduct N (alpha i) (alpha j) := by
    intro i j
    by_cases hi : i = 0
    · subst i
      simp [coeff, alpha, scalarProduct, coeffDot]
    by_cases hj : j = 0
    · subst j
      simp [coeff, alpha, hi, scalarProduct, coeffDot]
    have hcoeffRaw :
        (coeffDot (coeff i) (coeff j) : Complex) =
          (coeffDot (rawCoeff i) (rawCoeff j) : Complex) := by
      simp [coeff, hi, hj]
    calc
      (coeffDot (coeff i) (coeff j) : Complex) =
          (coeffDot (rawCoeff i) (rawCoeff j) : Complex) := hcoeffRaw
      _ = scalarProduct G (evalCoeff muBasis (rawCoeff i))
            (evalCoeff muBasis (rawCoeff j)) := by
          exact (Section3.irreducibleBasis_scalarProduct_evalCoeff
            htargetChi (rawCoeff i) (rawCoeff j)).symm
      _ = scalarProduct G (tau (alpha i)) (tau (alpha j)) := by
          rw [hEvalRaw i, hEvalRaw j]
      _ = scalarProduct N (alpha i) (alpha j) :=
          hisometry (alpha i) (alpha j) (halphaSpan i) (halphaSpan j)
  have hTauCoeff : forall i : Fin n,
      tau (alpha i) = evalCoeff muBasis (coeff i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [coeff, alpha, evalCoeff]
    · simpa [coeff, hi] using (hEvalRaw i).symm
  have hIntegral : IsIntegralIsometryOnCharacterDifferences muBasis d chi tau := by
    refine ⟨hmuDeg, hdpos, coeff, hcoeff0, ?_, ?_, ?_⟩
    · simpa [alpha] using hTauDeg
    · simpa [alpha] using hCoeffIso
    · simpa [alpha] using hTauCoeff

  rcases proposition_1_4_source hn muBasis hmuBasis d chi hchiBasis hchiDeg
      hchiOrth tau hIntegral with
    ⟨eps, heps, mu, hmu, hsplitMu⟩
  let X : Y := e 0
  let img : Y -> ClassFunction G := fun Z => eps • mu (e.symm Z)
  have himgVirt : forall Z : Y, Theory.Character.IsVirtualCharacter (img Z) := by
    intro Z
    exact Section3.isVirtualCharacter_of_signedIrreducible_pf35
      ⟨eps, heps, mu (e.symm Z), hmu.1 (e.symm Z), rfl⟩
  have himgSplit : forall Z : Y,
      tau ((X : ClassFunction N) - (Z : ClassFunction N)) = img X - img Z := by
    intro Z
    calc
      tau ((X : ClassFunction N) - (Z : ClassFunction N)) =
          tau (-((Z : ClassFunction N) - (X : ClassFunction N))) := by
            congr 1
            abel
      _ = -tau ((Z : ClassFunction N) - (X : ClassFunction N)) := by
        rw [map_neg]
      _ = -(eps • (mu (e.symm Z) - mu 0)) := by
        rw [show (Z : ClassFunction N) = chi (e.symm Z) by simp [chi],
          show (X : ClassFunction N) = chi 0 by simp [X, chi], hsplitMu]
      _ = img X - img Z := by
        ext g
        simp [img, X]
        ring
  have hepsNorm : eps * star eps = 1 := by
    rcases heps with rfl | rfl <;> norm_num
  have hsourceSelf : forall Z : Y,
      scalarProduct N (Z : ClassFunction N) (Z : ClassFunction N) = 1 := by
    intro Z
    exact (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hirr Z)).2
  have himgSelf : forall Z : Y,
      scalarProduct G (img Z) (img Z) =
        scalarProduct N (Z : ClassFunction N) (Z : ClassFunction N) := by
    intro Z
    rw [scalarProduct_smul_left, scalarProduct_smul_right,
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hmu.1 (e.symm Z))).2,
      hsourceSelf Z]
    simpa using hepsNorm
  have hsourceCross : hypothesis_5_2_c_statement Y := by
    intro Z W hZ hW hZW
    exact scalarProduct_isBookIrreducible_ne Z W
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hirr ⟨Z, hZ⟩))
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hirr ⟨W, hW⟩)) hZW
  have himgCross : forall Z W : Y,
      (Z : ClassFunction N) ≠ (W : ClassFunction N) ->
        scalarProduct G (img Z) (img W) = 0 := by
    intro Z W hZW
    have hsub : e.symm Z ≠ e.symm W := by
      intro heq
      exact hZW (by simpa using congrArg (fun i => (e i : ClassFunction N)) heq)
    have hmune : mu (e.symm Z) ≠ mu (e.symm W) := hmu.2 hsub
    have hzero := scalarProduct_isBookIrreducible_ne
      (mu (e.symm Z)) (mu (e.symm W))
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hmu.1 (e.symm Z)))
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hmu.1 (e.symm W))) hmune
    rw [scalarProduct_smul_left, scalarProduct_smul_right]
    simp [hzero]
  have hgram : forall Z W : Y,
      scalarProduct G (img Z) (img W) =
        scalarProduct N (Z : ClassFunction N) (W : ClassFunction N) := by
    intro Z W
    by_cases hZW : (Z : ClassFunction N) = (W : ClassFunction N)
    · have hsub : Z = W := Subtype.ext hZW
      subst W
      exact himgSelf Z
    · rw [himgCross Z W hZW]
      exact (hsourceCross Z.2 W.2 hZW).symm
  have hselfNe : forall Z : Y,
      scalarProduct N (Z : ClassFunction N) (Z : ClassFunction N) ≠ 0 := by
    intro Z
    rw [hsourceSelf Z]
    norm_num
  apply exists_extension_fields_of_image_family_pf57 Y tau img hsourceCross hselfNe
    himgVirt hgram
  intro Tnew hTnew
  apply isaacs_7_15_agrees_on_equal_degree_lattice Y tau Tnew X
  · exact degree_ne_zero_of_isBookIrreducibleCharacter
      (X : ClassFunction N)
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hirr X))
  · intro Z
    exact hdeg Z X
  · intro Z
    rw [hTnew X, hTnew Z]
    exact himgSplit Z

/-- Isaacs, Character Theory of Finite Groups, Corollary 7.15. -/
public theorem isaacs_theorem_7_15
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G)
    (Y : Finset (ClassFunction N))
    (tau : ClassFunction N →ₗ[Complex] ClassFunction G)
    (hirreducible :
      forall chi : Y, IsIrreducibleCharacterOnGroup (chi : ClassFunction N))
    (hisometry : isCFLinearIsometryOnSpanOn Y puncturedSet tau)
    (hdegreeZero :
      forall phi : ClassFunction N, integerSpanOn Y puncturedSet phi ->
        Theory.Character.IsVirtualCharacter (tau phi) /\
          supportedOn (tau phi) puncturedSet)
    (hequalDegree :
      forall chi psi : Y,
        degree (chi : ClassFunction N) = degree (psi : ClassFunction N))
    (hcard : 2 <= Y.card) :
    IsCoherentTriple puncturedSet Y tau := by
  classical
  have hsource : sourceVirtualCharacters Y := by
    intro chi hchi
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hirreducible ⟨chi, hchi⟩)
  have hcard' : 1 < Y.card := by omega
  rcases Finset.one_lt_card.mp hcard' with ⟨chi, hchi, psi, hpsi, hne⟩
  have hnonempty : integerSpanOnNonempty Y puncturedSet := by
    refine ⟨chi - psi, ?_, sub_ne_zero.mpr hne⟩
    refine ⟨integerSpan_sub (integerSpan_of_mem Y hchi)
      (integerSpan_of_mem Y hpsi), ?_⟩
    apply (supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change degree chi - degree psi = 0
    rw [hequalDegree ⟨chi, hchi⟩ ⟨psi, hpsi⟩]
    simp
  refine ⟨hsource, hnonempty, ?_⟩
  exact isaacs_7_15_equal_degree_extension_fields Y tau hirreducible
    hisometry hdegreeZero hequalDegree hcard

end VII
end Isaacs
end External
end CFSG.BenderSuzuki
