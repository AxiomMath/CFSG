module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Isaacs Theorem 7.14

A source-faithful formulation of the one-character coherence extension
criterion. The source inequality is multiplied by the positive quantity
2 * psi(1), avoiding division without changing its meaning.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace VII

open Section1 Section5

universe u

private theorem isaacs_7_14_positive_degree_nat
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

private theorem isaacs_7_14_isVirtualCharacter_zsmul
    {G : Type u} [Group G] [Finite G]
    (n : Int) {phi : ClassFunction G}
    (hphi : Theory.Character.IsVirtualCharacter phi) :
    Theory.Character.IsVirtualCharacter ((n : Complex) • phi) := by
  classical
  rcases hphi with ⟨r, m, k, rho, rfl⟩
  refine ⟨r, fun i => n * m i, k, rho, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isaacs_7_14_isVirtualCharacter_finset_sum
    {G : Type u} [Group G] [Finite G]
    {I : Type*} (s : Finset I) (Phi : I -> ClassFunction G)
    (hPhi : forall i, i ∈ s -> Theory.Character.IsVirtualCharacter (Phi i)) :
    Theory.Character.IsVirtualCharacter (∑ i ∈ s, Phi i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero := Section3.isVirtualCharacter_sub
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G))
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G))
      simpa using hzero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Section3.isVirtualCharacter_add
        (hPhi a (Finset.mem_insert_self a s))
        (ih (fun i hi => hPhi i (Finset.mem_insert_of_mem hi)))

private theorem isaacs_7_14_degree_ne_zero_of_virtual_norm_one
    {G : Type u} [Group G] [Finite G]
    {phi : ClassFunction G}
    (hvirt : Theory.Character.IsVirtualCharacter phi)
    (hself : scalarProduct G phi phi = 1) :
    degree phi ≠ 0 := by
  rcases Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself with
    ⟨eps, heps, mu, hmu, rfl⟩
  rcases heps with rfl | rfl
  · simpa using Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup mu hmu
  · rw [neg_one_smul]
    change -degree mu ≠ 0
    exact neg_ne_zero.mpr
      (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup mu hmu)

private theorem isaacs_7_14_distinguished_coefficient_eq_zero
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I) (d : Nat) (w : I -> Nat) (b : I -> Int)
    (A : ClassFunction G) (a : Complex)
    (hd : 0 < d) (hw : forall i, 0 < w i)
    (hrel : forall i, (w p : Int) * b i = (w i : Int) * b p)
    (hnorm :
      scalarProduct G A A + ((∑ i : I, (b i) ^ 2 : Int) : Complex) =
        ((1 + 2 * (d : Int) * b p : Int) : Complex))
    (hdegree :
      degree A + ((∑ i : I, b i * (w i : Int) : Int) : Complex) * a =
        ((d * w p : Nat) : Complex) * a)
    (ha : a ≠ 0)
    (hgrowth : 2 * d * (w p) ^ 2 < ∑ i : I, (w i) ^ 2) :
    b p = 0 := by
  classical
  let S : Int := ∑ i : I, (b i) ^ 2
  let W : Int := ∑ i : I, ((w i : Int) ^ 2)
  have hSnonneg : 0 <= S := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  have hnormRe :
      cfNormSq A + (S : Real) =
        ((1 + 2 * (d : Int) * b p : Int) : Real) := by
    change scalarProduct G A A + (S : Complex) =
      ((1 + 2 * (d : Int) * b p : Int) : Complex) at hnorm
    have h := congrArg Complex.re hnorm
    change (scalarProduct G A A).re + (S : Real) =
      ((1 + 2 * (d : Int) * b p : Int) : Real) at h
    simpa [cfNormSq] using h
  by_contra hbp
  rcases lt_or_gt_of_ne hbp with hbpneg | hbppos
  · have hdZ : (0 : Int) < d := by exact_mod_cast hd
    have hrhs : (1 + 2 * (d : Int) * b p : Int) < 0 := by
      nlinarith
    have hnormnonneg := cfNormSq_nonneg A
    have hrhsR : (((1 + 2 * (d : Int) * b p : Int) : Int) : Real) < 0 := by
      exact_mod_cast hrhs
    have hSnonnegR : (0 : Real) <= (S : Real) := by exact_mod_cast hSnonneg
    nlinarith
  · have hdZ : (0 : Int) < d := by exact_mod_cast hd
    have hwpZ : (0 : Int) < w p := by exact_mod_cast hw p
    have hterm :
        forall i : I,
          (w p : Int) ^ 2 * (b i) ^ 2 =
            (b p) ^ 2 * (w i : Int) ^ 2 := by
      intro i
      have hi := hrel i
      calc
        (w p : Int) ^ 2 * (b i) ^ 2 =
            ((w p : Int) * b i) ^ 2 := by ring
        _ = ((w i : Int) * b p) ^ 2 := by rw [hi]
        _ = (b p) ^ 2 * (w i : Int) ^ 2 := by ring
    have hsqEq : (w p : Int) ^ 2 * S = (b p) ^ 2 * W := by
      calc
        (w p : Int) ^ 2 * S =
            ∑ i : I, (w p : Int) ^ 2 * (b i) ^ 2 := by
              simp [S, Finset.mul_sum]
        _ = ∑ i : I, (b p) ^ 2 * (w i : Int) ^ 2 := by
              exact Finset.sum_congr rfl fun i _ => hterm i
        _ = (b p) ^ 2 * W := by simp [W, Finset.mul_sum]
    have hgrowthZ :
        2 * (d : Int) * (w p : Int) ^ 2 < W := by
      dsimp [W]
      exact_mod_cast hgrowth
    have hbpSqPos : (0 : Int) < (b p) ^ 2 := sq_pos_of_pos hbppos
    have hmul : (2 * (d : Int) * (w p : Int) ^ 2) * (b p) ^ 2 <
        W * (b p) ^ 2 := by
      have hdiff : (0 : Int) <
          W - 2 * (d : Int) * (w p : Int) ^ 2 := sub_pos.mpr hgrowthZ
      have hprodpos : (0 : Int) <
          (W - 2 * (d : Int) * (w p : Int) ^ 2) * (b p) ^ 2 :=
        mul_pos hdiff hbpSqPos
      nlinarith
    have hwpSqPos : (0 : Int) < (w p : Int) ^ 2 := sq_pos_of_pos hwpZ
    have hscaled :
        (w p : Int) ^ 2 * (2 * (d : Int) * (b p) ^ 2) <
          (w p : Int) ^ 2 * S := by
      calc
        (w p : Int) ^ 2 * (2 * (d : Int) * (b p) ^ 2) =
            (2 * (d : Int) * (w p : Int) ^ 2) * (b p) ^ 2 := by ring
        _ < W * (b p) ^ 2 := hmul
        _ = (w p : Int) ^ 2 * S := by
          rw [mul_comm W, ← hsqEq]
    have hmain : 2 * (d : Int) * (b p) ^ 2 < S := by
      by_contra hnot
      have hle : S <= 2 * (d : Int) * (b p) ^ 2 := le_of_not_gt hnot
      have hscaled_le :
          (w p : Int) ^ 2 * S <=
            (w p : Int) ^ 2 * (2 * (d : Int) * (b p) ^ 2) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hwpSqPos)
      exact (not_lt_of_ge hscaled_le) hscaled
    have hbp_le_sq : b p <= (b p) ^ 2 := by nlinarith
    have hbound : (1 + 2 * (d : Int) * b p : Int) <= S := by
      nlinarith
    have hnormnonneg := cfNormSq_nonneg A
    have hboundR :
        (((1 + 2 * (d : Int) * b p : Int) : Int) : Real) <= (S : Real) := by
      exact_mod_cast hbound
    have hnormzero : cfNormSq A = 0 := by nlinarith
    have hAzero : A = 0 := cfNormSq_eq_zero hnormzero
    have hSformula : S = 1 + 2 * (d : Int) * b p := by
      rw [hnormzero, zero_add] at hnormRe
      exact_mod_cast hnormRe
    have hbpone : b p = 1 := by
      have hlt : 2 * (d : Int) * (b p) ^ 2 <
          1 + 2 * (d : Int) * b p := by
        simpa [hSformula] using hmain
      nlinarith
    have hdegree' := hdegree
    rw [hAzero] at hdegree'
    have hcoefC :
        ((∑ i : I, b i * (w i : Int) : Int) : Complex) * a =
          ((d * w p : Nat) : Complex) * a := by
      simpa only [degree, Pi.zero_apply, zero_add] using hdegree'
    have hcoefC' :
        ((∑ i : I, b i * (w i : Int) : Int) : Complex) =
          ((d * w p : Nat) : Complex) :=
      mul_right_cancel₀ ha hcoefC
    have hcoefZ :
        (∑ i : I, b i * (w i : Int) : Int) =
          ((d * w p : Nat) : Int) := by
      exact_mod_cast hcoefC'
    have hsumBW :
        (∑ i : I, b i * (w i : Int) : Int) = (w p : Int) * S := by
      calc
        (∑ i : I, b i * (w i : Int) : Int) =
            ∑ i : I, b i * ((w p : Int) * b i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              have hi := hrel i
              rw [hbpone, mul_one] at hi
              rw [← hi]
        _ = ∑ i : I, (w p : Int) * (b i) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = (w p : Int) * S := by simp [S, Finset.mul_sum]
    have hprod :
        (w p : Int) * S = (w p : Int) * (d : Int) := by
      calc
        (w p : Int) * S =
            (∑ i : I, b i * (w i : Int) : Int) := hsumBW.symm
        _ = ((d * w p : Nat) : Int) := hcoefZ
        _ = (w p : Int) * (d : Int) := by
              push_cast
              ring
    have hS_eq_d : S = (d : Int) :=
      mul_left_cancel₀ (ne_of_gt hwpZ) hprod
    rw [hbpone] at hSformula
    nlinarith
private theorem isaacs_7_14_extension_fields
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G)
    (Y0 : Finset (ClassFunction N))
    (chi : ClassFunction N)
    (hchi_not_mem : chi ∉ Y0)
    (psi : Y0)
    (tau : ClassFunction N →ₗ[Complex] ClassFunction G)
    (hirreducible0 :
      forall xi : Y0, IsIrreducibleCharacterOnGroup (xi : ClassFunction N))
    (hchi_irreducible : IsIrreducibleCharacterOnGroup chi)
    (hisometry :
      isCFLinearIsometryOnSpanOn (insert chi Y0) puncturedSet tau)
    (hdegreeZero :
      forall phi : ClassFunction N,
        integerSpanOn (insert chi Y0) puncturedSet phi ->
          And (Theory.Character.IsVirtualCharacter (tau phi))
            (supportedOn (tau phi) puncturedSet))
    (hcoherent : IsCoherentTriple puncturedSet Y0 tau)
    (hdiv :
      exists d : Nat,
        degree chi = (d : Complex) * degree (psi : ClassFunction N))
    (hgrowth :
      2 * (degree chi).re * (degree (psi : ClassFunction N)).re <
        ∑ xi : Y0, (degree (xi : ClassFunction N)).re ^ 2) :
    exists Tnew : ClassFunction N →ₗ[Complex] ClassFunction G,
      And (isCFLinearIsometryOnSpan (insert chi Y0) Tnew)
        (And (mapsIntegerSpanToVirtualCharacters (insert chi Y0) Tnew)
          (agreesOnIntegerSpanOn (insert chi Y0) puncturedSet tau Tnew)) := by
  letI : Fintype N := Fintype.ofFinite N
  let S : Finset (ClassFunction N) := insert chi Y0
  classical
  rcases hcoherent with
    ⟨_hsource0, _hnonempty0, Told, hToldIso, hToldVirt, hToldAgree⟩
  let w : Y0 -> Nat := fun xi =>
    Classical.choose (isaacs_7_14_positive_degree_nat (hirreducible0 xi))
  have hwpos : forall xi : Y0, 0 < w xi := by
    intro xi
    exact (Classical.choose_spec
      (isaacs_7_14_positive_degree_nat (hirreducible0 xi))).1
  have hwdeg : forall xi : Y0,
      degree (xi : ClassFunction N) = (w xi : Complex) := by
    intro xi
    exact (Classical.choose_spec
      (isaacs_7_14_positive_degree_nat (hirreducible0 xi))).2
  let dchi : Nat :=
    Classical.choose (isaacs_7_14_positive_degree_nat hchi_irreducible)
  have hdchi_pos : 0 < dchi :=
    (Classical.choose_spec
      (isaacs_7_14_positive_degree_nat hchi_irreducible)).1
  have hdchi_deg : degree chi = (dchi : Complex) :=
    (Classical.choose_spec
      (isaacs_7_14_positive_degree_nat hchi_irreducible)).2
  obtain ⟨d, hddiv⟩ := hdiv
  have hdchi_eq : dchi = d * w psi := by
    have hcast : (dchi : Complex) = ((d * w psi : Nat) : Complex) := by
      rw [← hdchi_deg, hddiv, hwdeg]
      push_cast
      rfl
    exact_mod_cast hcast
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0, zero_mul] at hdchi_eq
    exact (Nat.ne_of_gt hdchi_pos) hdchi_eq
  have hgrowthNat : 2 * d * (w psi) ^ 2 < ∑ xi : Y0, (w xi) ^ 2 := by
    have h := hgrowth
    rw [hdchi_deg, hwdeg psi] at h
    simp_rw [hwdeg] at h
    have h' : (2 * dchi * w psi : Nat) < ∑ xi : Y0, (w xi) ^ 2 := by
      exact_mod_cast h
    simpa [hdchi_eq, Nat.mul_assoc, pow_two] using h'

  have hsourceSelf : forall xi : Y0,
      scalarProduct N (xi : ClassFunction N) (xi : ClassFunction N) = 1 := by
    intro xi
    exact (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (hirreducible0 xi)).2
  have hsourceCross : forall xi eta : Y0,
      xi ≠ eta ->
        scalarProduct N (xi : ClassFunction N) (eta : ClassFunction N) = 0 := by
    intro xi eta hne
    exact scalarProduct_isBookIrreducible_ne
      (xi : ClassFunction N) (eta : ClassFunction N)
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hirreducible0 xi))
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hirreducible0 eta))
      (fun h => hne (Subtype.ext h))
  have hToldGram : forall xi eta : Y0,
      scalarProduct G (Told (xi : ClassFunction N))
        (Told (eta : ClassFunction N)) = if xi = eta then 1 else 0 := by
    intro xi eta
    rw [hToldIso (xi : ClassFunction N) (eta : ClassFunction N)
      (integerSpan_of_mem Y0 xi.2) (integerSpan_of_mem Y0 eta.2)]
    by_cases hxi : xi = eta
    · subst eta
      simp [hsourceSelf]
    · simp [hxi, hsourceCross xi eta hxi]
  have hToldVirt : forall xi : Y0,
      Theory.Character.IsVirtualCharacter (Told (xi : ClassFunction N)) := by
    intro xi
    exact hToldVirt (xi : ClassFunction N) (integerSpan_of_mem Y0 xi.2)

  let alpha : ClassFunction N :=
    chi - ((d : Int) : Complex) • (psi : ClassFunction N)
  have halphaSpan : integerSpan S alpha := by
    apply integerSpan_sub
    · exact integerSpan_of_mem S (by simp [S])
    · simpa [alpha] using integerSpan_zsmul (S := S) (d : Int)
        (integerSpan_of_mem S (by simp [S, psi.2]))
  have halphaDegree : degree alpha = 0 := by
    rw [show degree alpha =
      degree chi - (d : Complex) * degree (psi : ClassFunction N) by rfl,
      hddiv]
    simp
  have halphaOn : integerSpanOn S puncturedSet alpha := by
    exact ⟨halphaSpan,
      (supportedOn_puncturedSet_iff_degree_eq_zero alpha).2 halphaDegree⟩
  have hTauAlphaVirt : Theory.Character.IsVirtualCharacter (tau alpha) :=
    (hdegreeZero alpha (by simpa [S] using halphaOn)).1
  have hTauAlphaDegree : degree (tau alpha) = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero _).1
      (hdegreeZero alpha (by simpa [S] using halphaOn)).2
  have hAlphaSelf :
      scalarProduct N alpha alpha = 1 + (d : Complex) ^ 2 := by
    have hchiSelf : scalarProduct N chi chi = 1 :=
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        hchi_irreducible).2
    have hchiPsi : scalarProduct N chi (psi : ClassFunction N) = 0 :=
      scalarProduct_isBookIrreducible_ne chi
        (psi : ClassFunction N)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          hchi_irreducible)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (hirreducible0 psi))
        (fun h => hchi_not_mem (by simp [h, psi.2]))
    have hpsiChi : scalarProduct N (psi : ClassFunction N) chi = 0 := by
      have hstar := congrArg star hchiPsi
      simpa [Section1.scalarProduct_star_swap] using hstar
    simp [alpha, Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right, hchiSelf, hsourceSelf psi,
      hchiPsi, hpsiChi]
    ring
  have hTauAlphaSelf :
      scalarProduct G (tau alpha) (tau alpha) = 1 + (d : Complex) ^ 2 := by
    rw [hisometry alpha alpha (by simpa [S] using halphaOn)
      (by simpa [S] using halphaOn), hAlphaSelf]

  let z : ClassFunction G :=
    tau alpha + ((d : Int) : Complex) • Told (psi : ClassFunction N)
  have hzVirt : Theory.Character.IsVirtualCharacter z := by
    exact Section3.isVirtualCharacter_add hTauAlphaVirt
      (by
        simpa [z] using isaacs_7_14_isVirtualCharacter_zsmul (d : Int)
          (hToldVirt psi))
  have hzCoeff : forall xi : Y0, exists n : Int,
      scalarProduct G z (Told (xi : ClassFunction N)) = (n : Complex) := by
    intro xi
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hzVirt (hToldVirt xi)
  let b : Y0 -> Int := fun xi => Classical.choose (hzCoeff xi)
  have hb : forall xi : Y0,
      scalarProduct G z (Told (xi : ClassFunction N)) = (b xi : Complex) := by
    intro xi
    exact Classical.choose_spec (hzCoeff xi)
  let P : ClassFunction G :=
    ∑ xi : Y0, (b xi : Complex) • Told (xi : ClassFunction N)
  have hPVirt : Theory.Character.IsVirtualCharacter P := by
    apply isaacs_7_14_isVirtualCharacter_finset_sum
      (Finset.univ : Finset Y0)
      (fun xi => (b xi : Complex) • Told (xi : ClassFunction N))
    intro xi _hxi
    simpa using isaacs_7_14_isVirtualCharacter_zsmul (b xi) (hToldVirt xi)
  let A : ClassFunction G := z - P
  have hAVirt : Theory.Character.IsVirtualCharacter A :=
    Section3.isVirtualCharacter_sub hzVirt hPVirt

  have hrel : forall xi : Y0,
      (w psi : Int) * b xi = (w xi : Int) * b psi := by
    intro xi
    by_cases hxi : xi = psi
    · subst xi
      rfl
    let Xi : ClassFunction N :=
      ((w psi : Int) : Complex) • (xi : ClassFunction N) -
        ((w xi : Int) : Complex) • (psi : ClassFunction N)
    have hXiSpan0 : integerSpan Y0 Xi := by
      apply integerSpan_sub
      · exact integerSpan_zsmul (w psi : Int)
          (integerSpan_of_mem Y0 xi.2)
      · exact integerSpan_zsmul (w xi : Int)
          (integerSpan_of_mem Y0 psi.2)
    have hXiDegree : degree Xi = 0 := by
      change (w psi : Complex) * degree (xi : ClassFunction N) -
        (w xi : Complex) * degree (psi : ClassFunction N) = 0
      rw [hwdeg xi, hwdeg psi]
      ring
    have hXiOn0 : integerSpanOn Y0 puncturedSet Xi :=
      ⟨hXiSpan0, (supportedOn_puncturedSet_iff_degree_eq_zero Xi).2 hXiDegree⟩
    have hXiOnS : integerSpanOn S puncturedSet Xi :=
      ⟨integerSpan_mono (by
          intro phi hphi
          simp [S, hphi]) hXiSpan0,
        hXiOn0.2⟩
    have hOldAgree : Told Xi = tau Xi := hToldAgree Xi hXiOn0
    have hIso :
        scalarProduct G (Told Xi) (tau alpha) =
          scalarProduct N Xi alpha := by
      rw [hOldAgree]
      exact hisometry Xi alpha (by simpa [S] using hXiOnS)
        (by simpa [S] using halphaOn)
    have hbRev : forall eta : Y0,
        scalarProduct G (Told (eta : ClassFunction N)) z = (b eta : Complex) := by
      intro eta
      have hstar := congrArg star (hb eta)
      simpa [Section1.scalarProduct_star_swap] using hstar
    have hxiChi :
        scalarProduct N (xi : ClassFunction N) chi = 0 := by
      exact scalarProduct_isBookIrreducible_ne
        (xi : ClassFunction N) chi
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (hirreducible0 xi))
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          hchi_irreducible)
        (fun h => hchi_not_mem (by simpa [h] using xi.2))
    have hpsiChi :
        scalarProduct N (psi : ClassFunction N) chi = 0 := by
      exact scalarProduct_isBookIrreducible_ne
        (psi : ClassFunction N) chi
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (hirreducible0 psi))
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          hchi_irreducible)
        (fun h => hchi_not_mem (by simpa [h] using psi.2))
    have hxiPsi := hsourceCross xi psi hxi
    have hOldCross : scalarProduct G
        (Told (xi : ClassFunction N)) (Told (psi : ClassFunction N)) = 0 := by
      simpa [hxi] using hToldGram xi psi
    have hOldPsiSelf : scalarProduct G
        (Told (psi : ClassFunction N)) (Told (psi : ClassFunction N)) = 1 := by
      simpa using hToldGram psi psi
    rw [show Told Xi =
        ((w psi : Int) : Complex) • Told (xi : ClassFunction N) -
          ((w xi : Int) : Complex) • Told (psi : ClassFunction N) by
          simp [Xi],
      show tau alpha =
        z - ((d : Int) : Complex) • Told (psi : ClassFunction N) by
          simp [z]] at hIso
    simp only [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right] at hIso
    rw [hbRev xi, hbRev psi, hOldCross, hOldPsiSelf] at hIso
    simp [Xi, alpha, Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right, hxiChi, hpsiChi, hxiPsi,
      hsourceSelf psi] at hIso
    exact_mod_cast (sub_eq_zero.mp hIso)
  have hnorm :
      scalarProduct G A A + ((∑ xi : Y0, (b xi) ^ 2 : Int) : Complex) =
        ((1 + 2 * (d : Int) * b psi : Int) : Complex) := by
    have hbRev : forall eta : Y0,
        scalarProduct G (Told (eta : ClassFunction N)) z = (b eta : Complex) := by
      intro eta
      have hstar := congrArg star (hb eta)
      simpa [Section1.scalarProduct_star_swap] using hstar
    have hOldPsiSelf : scalarProduct G
        (Told (psi : ClassFunction N)) (Told (psi : ClassFunction N)) = 1 := by
      simpa using hToldGram psi psi
    have hOldPsiTau :
        scalarProduct G (Told (psi : ClassFunction N)) (tau alpha) =
          (b psi : Complex) - d := by
      have h := hbRev psi
      rw [show z =
        tau alpha + ((d : Int) : Complex) • Told (psi : ClassFunction N) by rfl,
        Section5.scalarProduct_add_right,
        Section1.scalarProduct_smul_right, hOldPsiSelf] at h
      push_cast at h
      simpa using (eq_sub_of_add_eq h)
    have hTauOldPsi :
        scalarProduct G (tau alpha) (Told (psi : ClassFunction N)) =
          (b psi : Complex) - d := by
      have hstar := congrArg star hOldPsiTau
      simpa [Section1.scalarProduct_star_swap] using hstar
    have hzSelf :
        scalarProduct G z z =
          ((1 + 2 * (d : Int) * b psi : Int) : Complex) := by
      rw [show z =
        tau alpha + ((d : Int) : Complex) • Told (psi : ClassFunction N) by rfl]
      simp only [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
        Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
      rw [hTauAlphaSelf, hOldPsiTau, hTauOldPsi, hOldPsiSelf]
      push_cast
      simp
      ring
    have hPfun : P = fun g => ∑ xi : Y0,
        (((b xi : Complex) • Told (xi : ClassFunction N)) g) := by
      ext g
      simp [P]
    have hzP :
        scalarProduct G z P =
          ((∑ xi : Y0, (b xi) ^ 2 : Int) : Complex) := by
      rw [hPfun, Section1.scalarProduct_fintype_sum_right]
      simp_rw [Section1.scalarProduct_smul_right, hb]
      push_cast
      simp [pow_two]
    have hPz :
        scalarProduct G P z =
          ((∑ xi : Y0, (b xi) ^ 2 : Int) : Complex) := by
      rw [hPfun, Section1.scalarProduct_fintype_sum_left]
      simp_rw [Section1.scalarProduct_smul_left, hbRev]
      push_cast
      simp [pow_two]
    have hPP :
        scalarProduct G P P =
          ((∑ xi : Y0, (b xi) ^ 2 : Int) : Complex) := by
      rw [hPfun, Section1.scalarProduct_fintype_sum_left]
      simp_rw [Section1.scalarProduct_smul_left,
        Section1.scalarProduct_fintype_sum_right,
        Section1.scalarProduct_smul_right, hToldGram]
      push_cast
      simp [pow_two]
    rw [show scalarProduct G A A =
      scalarProduct G z z - scalarProduct G z P -
        scalarProduct G P z + scalarProduct G P P by
          simp [A, Section5.scalarProduct_sub_left,
            Section5.scalarProduct_sub_right]
          ring,
      hzSelf, hzP, hPz, hPP]
    push_cast
    ring
  let a : Complex :=
    (w psi : Complex)⁻¹ * degree (Told (psi : ClassFunction N))
  have ha : a ≠ 0 := by
    have hOldPsiSelf : scalarProduct G
        (Told (psi : ClassFunction N)) (Told (psi : ClassFunction N)) = 1 := by
      simpa using hToldGram psi psi
    have hOldPsiDegree :
        degree (Told (psi : ClassFunction N)) ≠ 0 :=
      isaacs_7_14_degree_ne_zero_of_virtual_norm_one
        (hToldVirt psi) hOldPsiSelf
    exact mul_ne_zero
      (inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt (hwpos psi))))
      hOldPsiDegree
  have hOldDegree : forall xi : Y0,
      degree (Told (xi : ClassFunction N)) = (w xi : Complex) * a := by
    intro xi
    let Xi : ClassFunction N :=
      ((w psi : Int) : Complex) • (xi : ClassFunction N) -
        ((w xi : Int) : Complex) • (psi : ClassFunction N)
    have hXiSpan0 : integerSpan Y0 Xi := by
      apply integerSpan_sub
      · exact integerSpan_zsmul (w psi : Int)
          (integerSpan_of_mem Y0 xi.2)
      · exact integerSpan_zsmul (w xi : Int)
          (integerSpan_of_mem Y0 psi.2)
    have hXiDegree : degree Xi = 0 := by
      change (w psi : Complex) * degree (xi : ClassFunction N) -
        (w xi : Complex) * degree (psi : ClassFunction N) = 0
      rw [hwdeg xi, hwdeg psi]
      ring
    have hXiOn0 : integerSpanOn Y0 puncturedSet Xi :=
      ⟨hXiSpan0,
        (supportedOn_puncturedSet_iff_degree_eq_zero Xi).2 hXiDegree⟩
    have hXiOnS : integerSpanOn S puncturedSet Xi :=
      ⟨integerSpan_mono (by
          intro phi hphi
          simp [S, hphi]) hXiSpan0,
        hXiOn0.2⟩
    have hTauXiDegree : degree (tau Xi) = 0 :=
      (supportedOn_puncturedSet_iff_degree_eq_zero _).1
        (hdegreeZero Xi (by simpa [S] using hXiOnS)).2
    have hToldXiDegree : degree (Told Xi) = 0 := by
      rw [hToldAgree Xi hXiOn0]
      exact hTauXiDegree
    have hbalance :
        (w psi : Complex) * degree (Told (xi : ClassFunction N)) =
          (w xi : Complex) * degree (Told (psi : ClassFunction N)) := by
      rw [show Told Xi =
        (w psi : Complex) • Told (xi : ClassFunction N) -
          (w xi : Complex) • Told (psi : ClassFunction N) by
            simp [Xi]] at hToldXiDegree
      change (w psi : Complex) * degree (Told (xi : ClassFunction N)) -
        (w xi : Complex) * degree (Told (psi : ClassFunction N)) = 0 at hToldXiDegree
      exact sub_eq_zero.mp hToldXiDegree
    have hwp : (w psi : Complex) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hwpos psi))
    calc
      degree (Told (xi : ClassFunction N)) =
          (w psi : Complex)⁻¹ *
            ((w psi : Complex) * degree (Told (xi : ClassFunction N))) := by
              field_simp
      _ = (w psi : Complex)⁻¹ *
          ((w xi : Complex) * degree (Told (psi : ClassFunction N))) := by
            rw [hbalance]
      _ = (w xi : Complex) * a := by
            simp [a]
            ring
  have hzDegree :
      degree z = ((d * w psi : Nat) : Complex) * a := by
    rw [show degree z =
      degree (tau alpha) + (d : Complex) *
        degree (Told (psi : ClassFunction N)) by rfl,
      hTauAlphaDegree, hOldDegree psi]
    push_cast
    ring
  have hPDegree :
      degree P =
        ((∑ xi : Y0, b xi * (w xi : Int) : Int) : Complex) * a := by
    rw [show degree P =
      ∑ xi : Y0, (b xi : Complex) *
        degree (Told (xi : ClassFunction N)) by
          simp [P, degree, smul_eq_mul]]
    simp_rw [hOldDegree]
    push_cast
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  have hdegree :
      degree A + ((∑ xi : Y0, b xi * (w xi : Int) : Int) : Complex) * a =
        ((d * w psi : Nat) : Complex) * a := by
    rw [show degree A = degree z - degree P by rfl, hzDegree, hPDegree]
    ring
  have hbpsi : b psi = 0 :=
    isaacs_7_14_distinguished_coefficient_eq_zero psi d w b A a hdpos hwpos
      hrel hnorm hdegree ha hgrowthNat
  have hbzero : forall xi : Y0, b xi = 0 := by
    intro xi
    have h := hrel xi
    rw [hbpsi, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by
      exact_mod_cast (Nat.ne_of_gt (hwpos psi)))
  have hPzero : P = 0 := by
    simp [P, hbzero]
  have hAz : A = z := by
    simp [A, hPzero]
  have hzSelf : scalarProduct G z z = 1 := by
    have h := hnorm
    simp [hbzero] at h
    simpa [hAz] using h
  have hzOld : forall xi : Y0,
      scalarProduct G z (Told (xi : ClassFunction N)) = 0 := by
    intro xi
    rw [hb xi, hbzero xi]
    norm_num
  have hOldz : forall xi : Y0,
      scalarProduct G (Told (xi : ClassFunction N)) z = 0 := by
    intro xi
    have hstar := congrArg star (hzOld xi)
    simpa [Section1.scalarProduct_star_swap] using hstar
  let img : S -> ClassFunction G := fun X =>
    if hX : (X : ClassFunction N) = chi then z
    else Told (⟨(X : ClassFunction N), by
      have hXS : (X : ClassFunction N) ∈ S := X.2
      dsimp only [S] at hXS
      exact (Finset.mem_insert.mp hXS).resolve_left hX⟩ : Y0)
  have himg_chi :
      img (⟨chi, by simp [S]⟩ : S) = z := by
    simp [img]
  have himg_old : forall xi : Y0,
      img (⟨(xi : ClassFunction N), by simp [S, xi.2]⟩ : S) =
        Told (xi : ClassFunction N) := by
    intro xi
    have hxi : (xi : ClassFunction N) ≠ chi := by
      intro h
      apply hchi_not_mem
      rw [← h]
      exact xi.2
    simp [img, hxi]
  have hsourceIrr : forall X : S,
      IsIrreducibleCharacterOnGroup (X : ClassFunction N) := by
    intro X
    by_cases hX : (X : ClassFunction N) = chi
    · simpa [hX] using hchi_irreducible
    · let X0 : Y0 := ⟨(X : ClassFunction N), by
        have hXS : (X : ClassFunction N) ∈ S := X.2
        dsimp only [S] at hXS
        exact (Finset.mem_insert.mp hXS).resolve_left hX⟩
      exact hirreducible0 X0
  have hsourceCrossS : hypothesis_5_2_c_statement S := by
    intro X Y hX hY hXY
    exact scalarProduct_isBookIrreducible_ne X Y
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hsourceIrr ⟨X, hX⟩))
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hsourceIrr ⟨Y, hY⟩)) hXY
  have hsourceSelfNe : forall X : S,
      scalarProduct N (X : ClassFunction N) (X : ClassFunction N) ≠ 0 := by
    intro X
    rw [(isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (hsourceIrr X)).2]
    norm_num
  have himgVirt : forall X : S,
      Theory.Character.IsVirtualCharacter (img X) := by
    intro X
    by_cases hX : (X : ClassFunction N) = chi
    · simpa [img, hX] using hzVirt
    · let X0 : Y0 := ⟨(X : ClassFunction N), by
        have hXS : (X : ClassFunction N) ∈ S := X.2
        dsimp only [S] at hXS
        exact (Finset.mem_insert.mp hXS).resolve_left hX⟩
      simpa [img, hX, X0] using hToldVirt X0
  have hgram : forall X Y : S,
      scalarProduct G (img X) (img Y) =
        scalarProduct N (X : ClassFunction N) (Y : ClassFunction N) := by
    intro X Y
    by_cases hX : (X : ClassFunction N) = chi
    · by_cases hY : (Y : ClassFunction N) = chi
      · have hXY : X = Y := Subtype.ext (hX.trans hY.symm)
        subst Y
        rw [show img X = z by simp [img, hX], hzSelf]
        exact (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (hsourceIrr X)).2.symm
      · let Y0' : Y0 := ⟨(Y : ClassFunction N), by
          have hYS : (Y : ClassFunction N) ∈ S := Y.2
          dsimp only [S] at hYS
          exact (Finset.mem_insert.mp hYS).resolve_left hY⟩
        rw [show img X = z by simp [img, hX],
          show img Y = Told (Y0' : ClassFunction N) by simp [img, hY, Y0'],
          hzOld Y0']
        exact (hsourceCrossS X.2 Y.2 (by
          intro h
          exact hY (h.symm.trans hX))).symm
    · by_cases hY : (Y : ClassFunction N) = chi
      · let X0 : Y0 := ⟨(X : ClassFunction N), by
          have hXS : (X : ClassFunction N) ∈ S := X.2
          dsimp only [S] at hXS
          exact (Finset.mem_insert.mp hXS).resolve_left hX⟩
        rw [show img X = Told (X0 : ClassFunction N) by simp [img, hX, X0],
          show img Y = z by simp [img, hY], hOldz X0]
        exact (hsourceCrossS X.2 Y.2 (by
          intro h
          exact hX (h.trans hY))).symm
      · let X0 : Y0 := ⟨(X : ClassFunction N), by
          have hXS : (X : ClassFunction N) ∈ S := X.2
          dsimp only [S] at hXS
          exact (Finset.mem_insert.mp hXS).resolve_left hX⟩
        let Y0' : Y0 := ⟨(Y : ClassFunction N), by
          have hYS : (Y : ClassFunction N) ∈ S := Y.2
          dsimp only [S] at hYS
          exact (Finset.mem_insert.mp hYS).resolve_left hY⟩
        rw [show img X = Told (X0 : ClassFunction N) by simp [img, hX, X0],
          show img Y = Told (Y0' : ClassFunction N) by simp [img, hY, Y0']]
        exact hToldIso (X : ClassFunction N) (Y : ClassFunction N)
          (integerSpan_of_mem Y0 X0.2) (integerSpan_of_mem Y0 Y0'.2)
  apply exists_extension_fields_of_image_family_pf57 S tau img
    hsourceCrossS hsourceSelfNe himgVirt hgram
  intro Tnew hTnew phi hphi
  rcases hphi with ⟨⟨v, hv⟩, hphiSupport⟩
  let chiS : S := ⟨chi, by simp [S]⟩
  let vOld : CoeffVector Y0 := fun xi =>
    v ⟨(xi : ClassFunction N), by simp [S, xi.2]⟩
  let m : Int := v chiS
  let oldSum : ClassFunction N :=
    Section1.evalCoeff (fun xi : Y0 => (xi : ClassFunction N)) vOld
  have hphiSplit :
      phi = oldSum + (m : Complex) • chi := by
    rw [hv]
    ext g
    simp [oldSum, vOld, m, chiS, Section1.evalCoeff, S, hchi_not_mem,
      Finset.attach_insert, smul_eq_mul]
    rw [add_comm]
    congr 1
    rw [Finset.sum_image]
    intro x _hx y _hy hxy
    have hval : (x : ClassFunction N) = (y : ClassFunction N) :=
      congrArg (fun q : S => (q : ClassFunction N)) hxy
    exact Subtype.ext hval
  let oldPart : ClassFunction N :=
    oldSum + (((d : Int) * m : Int) : Complex) • (psi : ClassFunction N)
  have hOldSumSpan : integerSpan Y0 oldSum := ⟨vOld, rfl⟩
  have hOldPartSpan : integerSpan Y0 oldPart := by
    dsimp [oldPart]
    exact integerSpan_add hOldSumSpan
      (integerSpan_zsmul ((d : Int) * m)
        (integerSpan_of_mem Y0 psi.2))
  have hphiDecomp :
      phi = oldPart + (m : Complex) • alpha := by
    rw [hphiSplit]
    ext g
    simp [oldPart, alpha, smul_eq_mul]
    ring
  have hphiDegree : degree phi = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero phi).1 hphiSupport
  have hOldPartDegree : degree oldPart = 0 := by
    have h := congrArg degree hphiDecomp
    change degree phi =
      degree oldPart + (m : Complex) * degree alpha at h
    rw [hphiDegree, halphaDegree] at h
    simpa using h.symm
  have hOldPartOn : integerSpanOn Y0 puncturedSet oldPart :=
    ⟨hOldPartSpan,
      (supportedOn_puncturedSet_iff_degree_eq_zero oldPart).2 hOldPartDegree⟩
  have hTnewOld : forall xi : Y0,
      Tnew (xi : ClassFunction N) = Told (xi : ClassFunction N) := by
    intro xi
    calc
      Tnew (xi : ClassFunction N) =
          img (⟨(xi : ClassFunction N), by simp [S, xi.2]⟩ : S) := by
        simpa using hTnew
          (⟨(xi : ClassFunction N), by simp [S, xi.2]⟩ : S)
      _ = Told (xi : ClassFunction N) := himg_old xi
  have hTnewChi : Tnew chi = z := by
    calc
      Tnew chi = img (⟨chi, by simp [S]⟩ : S) := by
        simpa using hTnew (⟨chi, by simp [S]⟩ : S)
      _ = z := himg_chi
  have hTnewAlpha : Tnew alpha = tau alpha := by
    rw [show Tnew alpha =
      Tnew chi - (d : Complex) • Tnew (psi : ClassFunction N) by
        simp [alpha],
      hTnewChi, hTnewOld psi]
    simp [z]
  have hTnewOldSum : Tnew oldSum = Told oldSum := by
    simp [oldSum, Section1.evalCoeff, hTnewOld]
  have hTnewOldPart : Tnew oldPart = Told oldPart := by
    simp [oldPart, hTnewOldSum, hTnewOld]
  have hOldPartAgree : Told oldPart = tau oldPart :=
    hToldAgree oldPart hOldPartOn
  calc
    Tnew phi =
        Tnew (oldPart + (m : Complex) • alpha) :=
      congrArg Tnew hphiDecomp
    _ = Tnew oldPart + (m : Complex) • Tnew alpha := by simp
    _ = Told oldPart + (m : Complex) • tau alpha := by
      rw [hTnewOldPart, hTnewAlpha]
    _ = tau oldPart + (m : Complex) • tau alpha := by
      rw [hOldPartAgree]
    _ = tau (oldPart + (m : Complex) • alpha) := by simp
    _ = tau phi := congrArg tau hphiDecomp.symm
/-- Isaacs, Character Theory of Finite Groups, Theorem 7.14. -/
public theorem isaacs_theorem_7_14
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G)
    (Y0 : Finset (ClassFunction N))
    (chi : ClassFunction N)
    (hchi_not_mem : chi ∉ Y0)
    (psi : Y0)
    (tau : ClassFunction N →ₗ[Complex] ClassFunction G)
    (hirreducible0 :
      forall xi : Y0, IsIrreducibleCharacterOnGroup (xi : ClassFunction N))
    (hchi_irreducible : IsIrreducibleCharacterOnGroup chi)
    (hisometry :
      isCFLinearIsometryOnSpanOn (insert chi Y0) puncturedSet tau)
    (hdegreeZero :
      forall phi : ClassFunction N,
        integerSpanOn (insert chi Y0) puncturedSet phi ->
          Theory.Character.IsVirtualCharacter (tau phi) /\
            supportedOn (tau phi) puncturedSet)
    (hcoherent : IsCoherentTriple puncturedSet Y0 tau)
    (hdiv :
      exists d : Nat,
        degree chi = (d : Complex) * degree (psi : ClassFunction N))
    (hgrowth :
      2 * (degree chi).re * (degree (psi : ClassFunction N)).re <
        ∑ xi : Y0, (degree (xi : ClassFunction N)).re ^ 2) :
    IsCoherentTriple puncturedSet (insert chi Y0) tau := by
  have hsource : sourceVirtualCharacters (insert chi Y0) := by
    intro phi hphi
    rcases Finset.mem_insert.mp hphi with rfl | hphi0
    · exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        hchi_irreducible
    · exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hirreducible0 ⟨phi, hphi0⟩)
  have hnonempty : integerSpanOnNonempty (insert chi Y0) puncturedSet := by
    rcases hcoherent.2.1 with ⟨phi, ⟨hspan, hsupported⟩, hphi⟩
    exact ⟨phi,
      ⟨integerSpan_mono (Finset.subset_insert chi Y0) hspan, hsupported⟩,
      hphi⟩
  refine ⟨hsource, hnonempty, ?_⟩
  exact isaacs_7_14_extension_fields N Y0 chi hchi_not_mem psi tau
    hirreducible0 hchi_irreducible hisometry hdegreeZero hcoherent hdiv hgrowth

end VII
end Isaacs
end External
end CFSG.BenderSuzuki
