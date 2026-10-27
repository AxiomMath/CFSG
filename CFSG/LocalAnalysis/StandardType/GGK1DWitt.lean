module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.LieType.SeitzGeneration.OrthManyPieces
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.GroupTheory.WeirSylow


section ggK1DwLift

open Matrix

private theorem ggK1Dw_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem ggK1Dw_prime_cast_ne_zero {K : Type} [Field K] [Finite K] {p nf : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := ggK1Dw_charP_two hK
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

private lemma ggK1Dw_lin_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (v : ι → K) : ggK1DLin x v = (x : Matrix ι ι K) *ᵥ v := by
  rw [ggK1DLin, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.coe_mulVecLin]

private lemma ggK1Dw_lin_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (a b : GL ι K) : ggK1DLin (a * b) = ggK1DLin a * ggK1DLin b := by
  ext v
  rw [LinearEquiv.mul_apply, ggK1Dw_lin_apply, ggK1Dw_lin_apply, ggK1Dw_lin_apply,
    Units.val_mul, Matrix.mulVec_mulVec]

private lemma ggK1Dw_lin_pow {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (n : ℕ) : ggK1DLin (x ^ n) = (ggK1DLin x) ^ n := by
  induction n with
  | zero => ext v; rw [pow_zero, pow_zero, ggK1Dw_lin_apply]; simp
  | succ n ih => rw [pow_succ, pow_succ, ggK1Dw_lin_mul, ih]

private theorem ggK1Dw_omegaLift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qPlusForm K r) p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have hxp : (x : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQPlus K r)) =>
      (y : GL (Fin r ⊕ Fin r) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dw_lin_apply, TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dw_lin_pow, hxp]
    ext v; rw [ggK1Dw_lin_apply]; simp
  · exact ggK1Dw_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qPlusForm (K := K) r).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

private theorem ggK1Dw_omegaLift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qMinusForm K (r - 1) b c) p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have hxp : (x : GL (LargeEvenMinusIdx (r - 1)) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) =>
      (y : GL (LargeEvenMinusIdx (r - 1)) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dw_lin_apply, TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dw_lin_pow, hxp]
    ext v; rw [ggK1Dw_lin_apply]; simp
  · exact ggK1Dw_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

end ggK1DwLift

private theorem ggK1Dw_even_add_mod (a s : ℕ) :
    Even (a + s) ↔ (a % 2 = 1 ↔ ¬ Even s) := by
  have ha : a % 2 = 1 ↔ ¬ Even a := by
    rw [Nat.even_iff]
    omega
  rw [Nat.even_add, ha]
  tauto

private theorem ggK1Dw_foldl_range (l : List ℕ) (f : Bool → ℕ → Bool) (e : Bool) :
    (List.range l.length).foldl (fun e k => f e (l.getD k 0)) e = l.foldl f e := by
  induction l generalizing e with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      simp only [List.getD_cons_zero]
      have h : (fun e k => f e ((a :: t).getD (k + 1) 0)) = fun e k => f e (t.getD k 0) := by
        funext e k
        rw [List.getD_cons_succ]
      rw [h, ih, List.foldl_cons]

private theorem ggK1Dw_foldl_parity (l : List ℕ) (e : Bool) :
    l.foldl (fun e a => if a % 2 = 1 then !e else e) e =
      if Even l.sum then e else !e := by
  induction l generalizing e with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, ih, List.sum_cons]
      simp only [ggK1Dw_even_add_mod a t.sum]
      by_cases ha : a % 2 = 1 <;> by_cases hs : Even t.sum <;> simp [ha, hs]

private theorem ggK1Dw_foldl_tail (m0 : ℕ) (t : List ℕ) (e : Bool) :
    ((List.range t.length).map (· + 1)).foldl
        (fun e j => if (m0 :: t).getD j 0 % 2 = 1 then !e else e) e =
      if Even t.sum then e else !e := by
  rw [List.foldl_map]
  rw [show (fun e k => (fun e j => if (m0 :: t).getD j 0 % 2 = 1 then !e else e) e (k + 1))
      = (fun e k => (fun e a => if a % 2 = 1 then !e else e) e (t.getD k 0)) from by
        funext e k
        simp only [List.getD_cons_succ]]
  exact (ggK1Dw_foldl_range t (fun e a => if a % 2 = 1 then !e else e) e).trans
    (ggK1Dw_foldl_parity t e)

private theorem ggK1Dw_eps0_one (p : ℕ) (tw : Bool) (m : List ℕ) :
    ggMultEps0 p 1 tw m = !tw := by
  simp [ggMultEps0]

private theorem ggK1Dw_eps0_two (p : ℕ) (tw : Bool) (m : List ℕ)
    (h : m.length = (p - 1) / 2 + 1) :
    ggMultEps0 p 2 tw m = if Even m.tail.sum then !tw else tw := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, m = a :: t := by
    cases m with
    | nil => simp at h
    | cons a t => exact ⟨a, t, rfl⟩
  have ht : t.length = (p - 1) / 2 := by simpa using h
  have hfold := ggK1Dw_foldl_tail a t (!tw)
  rw [ht] at hfold
  unfold ggMultEps0
  convert hfold using 2 <;> simp

private theorem ggK1Dw_eps0_two_false (p : ℕ) (m : List ℕ)
    (h : m.length = (p - 1) / 2 + 1) :
    ggMultEps0 p 2 false m = true ↔ Even m.tail.sum := by
  rw [ggK1Dw_eps0_two p false m h]
  by_cases hs : Even m.tail.sum <;> simp [hs]

private theorem ggK1Dw_eps0_two_true (p : ℕ) (m : List ℕ)
    (h : m.length = (p - 1) / 2 + 1) :
    ggMultEps0 p 2 true m = true ↔ Odd m.tail.sum := by
  rw [ggK1Dw_eps0_two p true m h]
  by_cases hs : Even m.tail.sum
  · simp [hs]
  · have ho : Odd m.tail.sum := Nat.not_even_iff_odd.mp hs
    simp [hs, ho]

private theorem ggK1Dw_ne_reciprocal_of_dvd_sub_one {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    h ≠ reciprocalPolynomial h := by
  intro hself
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvdX := hx.dvd_X_pow_sub_one hh
  have hchar : p ≠ ringChar K := by
    rw [ringChar.eq K 2]; exact hp2
  have hq1 : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    have hsplit : Nat.card K = (Nat.card K - 1) + 1 := by
      have := Nat.card_pos (α := K); omega
    rw [hsplit, Nat.cast_add, Nat.cast_one, (ZMod.natCast_eq_zero_iff (Nat.card K - 1) p).mpr hpq,
        zero_add]
  have hdeg : h.natDegree = 1 := by
    rw [CFSG.LieType.SeitzGeneration.natDegree_eq_orderOf_of_dvd hp hchar hmon hirr hdvdX hne,
      hq1, orderOf_one]
  have hc1 : h.coeff 1 = 1 := by
    rw [← hdeg]; exact hmon.leadingCoeff
  have hlin : h = X + C (h.coeff 0) := by
    have h1 := Polynomial.eq_X_add_C_of_natDegree_le_one (p := h) (by omega)
    rw [hc1, C_1, one_mul] at h1
    exact h1
  have hc0ne : h.coeff 0 ≠ 0 := by
    intro hc0
    have hX : h = X := by rw [hlin, hc0, C_0, add_zero]
    have hdvd : X ∣ (X ^ p - 1 : K[X]) := hX ▸ hdvdX
    have hcoeff : (X ^ p - 1 : K[X]).coeff 0 = 0 := Polynomial.X_dvd_iff.mp hdvd
    have hcoeff' : (X ^ p - 1 : K[X]).coeff 0 = -1 := by
      simp [coeff_X_pow, hp.ne_zero, Ne.symm hp.ne_zero]
    exact one_ne_zero (neg_eq_zero.mp (hcoeff.symm.trans hcoeff').symm)
  have hc0eq : h.coeff 0 = (h.coeff 0)⁻¹ := by
    rw [← coeff_zero_reciprocalPolynomial hmon]
    exact congrArg (fun f => f.coeff 0) hself
  have hsq : h.coeff 0 * h.coeff 0 = 1 := by
    have h1 : (h.coeff 0)⁻¹ * h.coeff 0 = 1 := inv_mul_cancel₀ hc0ne
    rwa [← hc0eq] at h1
  have hneg1 : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero 1
  have hc0one : h.coeff 0 = 1 := by
    rcases sq_eq_one_iff.mp (by rwa [pow_two] : (h.coeff 0) ^ 2 = 1) with h1 | h1
    · exact h1
    · rw [h1, hneg1]
  have heq : h = X - 1 := by
    rw [hlin, hc0one, sub_eq_add_neg, ← C_1, ← C_neg, hneg1]
  exact hne heq

open CFSG.RankThree.PartOne.K159
open CFSG.RankThree.PartOne.S15K

private theorem ggK1Dw_isPlusType_others_of_paired {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hno : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → h ≠ reciprocalPolynomial h) :
    IsPlusType (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype) := by
  classical
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨T, -, hQT, hWT, hdisj, hdim⟩ := exists_halfSpace hx hno hRep
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hTle : T ≤ R := by
    rw [hR, ← hx.suppPerp_fixedSpace]
    intro t ht
    rw [mem_suppPerp]
    intro w hw
    exact hWT w hw t ht
  let S : Submodule K R := T.comap R.subtype
  have hmapS : S.map R.subtype = T := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.mpr hTle
  have hfS : Module.finrank K S = Module.finrank K T := by
    rw [← Submodule.finrank_map_subtype_eq R S, hmapS]
  have hdimR : Module.finrank K R = 2 * Module.finrank K T := by
    have hcompl := (hx.fixed_others).1
    have hsum : Module.finrank K (fixedSpace x) + Module.finrank K R =
        Module.finrank K V := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  refine ⟨S, ?_, ?_⟩
  · rw [hfS]; omega
  · intro s hs
    rw [QuadraticMap.comp_apply]
    exact hQT (s : V) hs

private theorem ggK1Dw_isPlusType_prod_decomp {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {s k : ℕ}
    (hWdim : Module.finrank K (fixedSpace x) = 2 * s)
    (hRdim : Module.finrank K (othersSpace x.toLinearMap (X - 1)) = 2 * k) :
    IsPlusType Q ↔
      (IsPlusType (Q.comp (fixedSpace x).subtype) ↔
        IsPlusType (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype)) := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  set W := fixedSpace x with hW
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hRreg : RegOn Q R := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    have hv : v ∈ W ⊔ R := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨w, hw, r, hr, rfl⟩ := Submodule.mem_sup.mp hv
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hRnd : (QuadraticMap.polarBilin (Q.comp R.subtype)).Nondegenerate :=
    nondegenerate_of_regOn hRreg
  have eV : Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
    (isometryTop Q).trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
      (isometryEquivSup Q W R hcompl.disjoint horth))
  have hV : IsPlusType Q ↔ IsPlusType ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
    isPlusType_congr eV
  by_cases hs : s = 0
  · have hW0 : Module.finrank K W = 0 := by rw [hWdim, hs, mul_zero]
    haveI : Subsingleton ↥W := Module.finrank_zero_iff.mp hW0
    haveI : Unique ↥W := uniqueOfSubsingleton 0
    have hWplus : IsPlusType (Q.comp W.subtype) := isPlusType_of_subsingleton _
    have hprod : IsPlusType ((Q.comp W.subtype).prod (Q.comp R.subtype)) ↔
        IsPlusType (Q.comp R.subtype) :=
      isPlusType_congr (QuadraticMap.IsometryEquiv.uniqueProd _ _)
    rw [hV, hprod]
    simp [hWplus]
  · by_cases hk : k = 0
    · have hR0 : Module.finrank K R = 0 := by rw [hRdim, hk, mul_zero]
      haveI : Subsingleton ↥R := Module.finrank_zero_iff.mp hR0
      haveI : Unique ↥R := uniqueOfSubsingleton 0
      have hRplus : IsPlusType (Q.comp R.subtype) := isPlusType_of_subsingleton _
      have hprod : IsPlusType ((Q.comp W.subtype).prod (Q.comp R.subtype)) ↔
          IsPlusType (Q.comp W.subtype) :=
        isPlusType_congr ((QuadraticMap.IsometryEquiv.prodComm _ _).trans
          (QuadraticMap.IsometryEquiv.uniqueProd _ _))
      rw [hV, hprod]
      simp [hRplus]
    · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      rw [hV, isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate hRnd hs1 hk1 hWdim hRdim]

private theorem ggK1Dw_oddOrder_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1)
    (Qf : QuadraticForm K (Fin r ⊕ Fin r → K)) (hQ : LargeEvenQPlus K r = ⇑Qf) :
    OddOrderIsometry Qf p (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have heq : TableBOrth.qPlusForm K r = Qf :=
    QuadraticMap.ext fun v =>
      (congrFun (TableBOrth.coe_qPlusForm (K := K) r) v).trans (congrFun hQ v)
  exact heq ▸ ggK1Dw_omegaLift_plus hp hp2 hnf hK hx

private theorem ggK1Dw_oddOrder_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1)
    (Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K))
    (hQ : LargeEvenQMinus (r - 1) b c = ⇑Qf) :
    OddOrderIsometry Qf p (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have heq : TableBOrth.qMinusForm K (r - 1) b c = Qf :=
    QuadraticMap.ext fun v =>
      (congrFun (TableBOrth.coe_qMinusForm (K := K) (r - 1) b c) v).trans (congrFun hQ v)
  exact heq ▸ ggK1Dw_omegaLift_minus hp hp2 hnf hK hirr hx

private theorem ggK1Dw_isPlusType_qPlus {r : ℕ} {K : Type} [Field K]
    (Qf : QuadraticForm K (Fin r ⊕ Fin r → K)) (hQ : LargeEvenQPlus K r = ⇑Qf) :
    IsPlusType Qf := by
  have heq : Qf = TableBOrth.qPlusForm K r :=
    QuadraticMap.ext fun v =>
      (congrFun hQ v).symm.trans (congrFun (TableBOrth.coe_qPlusForm (K := K) r) v).symm
  rw [heq]
  exact isPlusType_quadPlus K r

private theorem ggK1Dw_not_isPlusType_qMinus {r : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K))
    (hQ : LargeEvenQMinus (r - 1) b c = ⇑Qf) :
    ¬ IsPlusType Qf := by
  have heq : Qf = TableBOrth.qMinusForm K (r - 1) b c :=
    QuadraticMap.ext fun v =>
      (congrFun hQ v).symm.trans (congrFun (TableBOrth.coe_qMinusForm (K := K) (r - 1) b c) v).symm
  rw [heq]
  intro h
  have h2 : IsPlusType (CFSG.LieType.Universal.Spin.quadMinus ((r - 1) + 1) K b c) :=
    (isPlusType_congr (TableBOrth.qMinusIsometry (r - 1) b c)).mp h
  exact not_isPlusType_quadMinus (Nat.le_add_left 1 (r - 1)) hirr h2

private theorem ggK1Dw_finrank_others_eq {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {r : ℕ} (hV : Module.finrank K V = 2 * r) {m : List ℕ}
    (hhead : m.headD 0 = Module.finrank K (fixedSpace x) / 2) (hsum : m.sum = r) :
    Module.finrank K (othersSpace x.toLinearMap (X - 1)) = 2 * m.tail.sum := by
  have hcompl := (hx.fixed_others).1
  have hdimV := Submodule.finrank_add_eq_of_isCompl hcompl
  have hW : Module.finrank K (fixedSpace x) = 2 * m.headD 0 := by
    obtain ⟨s, hs⟩ := hx.even_finrank_fixed
    have h1 : m.headD 0 = s := by rw [hhead, hs]; omega
    rw [hs, h1]
    omega
  have hsum' : m.sum = m.headD 0 + m.tail.sum := by
    cases m with
    | nil => simp
    | cons a t => simp
  omega

private noncomputable def ggK1Dw_restrictIso {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) (x : GL ι K) :
    (Q.restrict (primaryComponent (ggK1DOrthEnd x) (X - 1))).IsometryEquiv
      (Q.comp (fixedSpace (ggK1DLin x)).subtype) where
  toLinearEquiv := LinearEquiv.ofEq _ _ (fixedSpace_eq_primaryComponent (x := ggK1DLin x)).symm
  map_app' := fun _ => rfl



private theorem ggK1Dw_primaryComponent_eq_fixedSpace {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (x : GL ι K) :
    primaryComponent (ggK1DOrthEnd x) (X - 1) = fixedSpace (ggK1DLin x) :=
  fixedSpace_eq_primaryComponent.symm

private theorem ggK1Dw_head_eq {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) {m : List ℕ}
    (h : m.headD 0 = Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2) :
    m.headD 0 = Module.finrank K (fixedSpace (ggK1DLin x)) / 2 := by
  rw [← ggK1Dw_primaryComponent_eq_fixedSpace (x := x)]
  exact h

private theorem ggK1Dw_false_of_r_zero {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m)
    (hx : x ^ p = 1) (hr : r = 0) : False := by
  classical
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hxO := ggK1Dw_omegaLift_minus hp hp2 hnf hK hirr hx
  have hsum0 : m.sum = 0 := by rw [hm.sum_eq, hr]
  have hall : ∀ a ∈ m, a = 0 := List.sum_eq_zero_iff.mp hsum0
  have hhead0 : m.headD 0 = 0 := by
    cases m with
    | nil => rfl
    | cons a t => simpa using hall a (by simp)
  have hWfin : Module.finrank K
      (fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))) = 0 := by
    obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
    have h1 : m.headD 0 = s := by
      rw [ggK1Dw_head_eq (x := (x : GL (LargeEvenMinusIdx (r - 1)) K)) hm.head_eq, hs]; omega
    rw [hs, ← h1, hhead0]
  have hWbot : fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) = ⊥ :=
    Submodule.finrank_eq_zero.1 hWfin
  have hXne : (X - 1 : K[X]) ∉
      primaryFactors (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
    intro hX
    have h1 := primaryComponent_ne_bot hxO.squarefree_minpoly hX
    rw [← fixedSpace_eq_primaryComponent, hWbot] at h1
    exact h1 rfl
  have hpf : primaryFactors (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) ≠ ∅ := by
    intro h
    have h1 := prod_primaryFactors hxO.squarefree_minpoly
    simp only [ggK1DOrthEnd] at h
    rw [h, Finset.prod_empty] at h1
    exact minpoly.ne_one K (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) h1.symm
  have htail0 : m.tail.filter (fun j => decide (j ≠ 0)) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    rw [List.mem_filter] at ha
    exact (by simpa [hall a (List.mem_of_mem_tail ha.1)] using ha.2)
  rcases hm.blocks_eq with ⟨hd1, P, hP, hPeq⟩ | ⟨hd2, hPeq⟩
  · have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      by_contra h2
      have h1 : ggMultOrd p nf = 1 := hd1
      rw [ggMultOrd, if_neg h2] at h1
      split_ifs at h1 <;> exact absurd h1 (by norm_num)
    have hno : ∀ h ∈ primaryFactors (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)),
        h ≠ X - 1 → h ≠ reciprocalPolynomial h :=
      fun h hh hne => ggK1Dw_ne_reciprocal_of_dvd_sub_one hxO hp hp2 hpq hh hne
    have hP0 : P.val = 0 := by
      rw [← Multiset.map_eq_zero, ← hPeq, htail0]; rfl
    have hPempty : P = ∅ := Finset.val_eq_zero.mp hP0
    obtain ⟨h, hh⟩ := Finset.nonempty_iff_ne_empty.mpr hpf
    have hne1 : h ≠ X - 1 := fun hh1 => hXne (hh1 ▸ hh)
    rcases hP.2.1 h hh (hno h hh hne1) with hmem | hmem
    · rw [hPempty] at hmem; simpa using hmem
    · rw [hPempty] at hmem; simpa using hmem
  · have hSD0 : ggK1DSelfDualFactors (x : GL (LargeEvenMinusIdx (r - 1)) K) = ∅ := by
      have h1 : (ggK1DSelfDualFactors (x : GL (LargeEvenMinusIdx (r - 1)) K)).val.map
          (primaryMultiplicity (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K))) = 0 := by
        rw [← hPeq, htail0]; rfl
      exact Finset.val_eq_zero.mp (Multiset.map_eq_zero.mp h1)
    have hfilter : ggK1DSelfDualFactors (x : GL (LargeEvenMinusIdx (r - 1)) K) =
        primaryFactors (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
      unfold ggK1DSelfDualFactors
      exact Finset.filter_true_of_mem (fun h hh heq => hXne (heq ▸ hh))
    rw [hfilter] at hSD0
    exact hpf hSD0


theorem ggK1D_v0_witt_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m)
    (hx : x ^ p = 1)
    (Qf : QuadraticForm K (Fin r ⊕ Fin r → K)) (hQ : LargeEvenQPlus K r = ⇑Qf) :
    (CFSG.GroupTheory.WeirSylow.IsPlusType
        (Qf.restrict (primaryComponent (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) (X - 1))) ↔
      ggMultEps0 p (ggMultOrd p nf) false m = true) := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hxO := ggK1Dw_oddOrder_plus hp hp2 hnf hK hx Qf hQ
  have hhead := ggK1Dw_head_eq (x := (x : GL (Fin r ⊕ Fin r) K)) hm.head_eq
  have hVdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]; simp; omega
  have hWdim : Module.finrank K (fixedSpace (ggK1DLin (x : GL (Fin r ⊕ Fin r) K))) =
      2 * m.headD 0 := by
    obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
    have h1 : m.headD 0 = s := by rw [hhead, hs]; omega
    rw [hs, h1]; omega
  have hRdim := ggK1Dw_finrank_others_eq hxO hVdim hhead hm.sum_eq
  have hprod := ggK1Dw_isPlusType_prod_decomp hxO hWdim hRdim
  by_cases hsub : p ∣ 2 ^ nf - 1
  · have hd1 : ggMultOrd p nf = 1 := by simp [ggMultOrd, hsub]
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hsub
    have hno : ∀ h ∈ primaryFactors (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)),
        h ≠ X - 1 → h ≠ reciprocalPolynomial h :=
      fun h hh hne => ggK1Dw_ne_reciprocal_of_dvd_sub_one hxO hp hp2 hpq hh hne
    have hRplus := ggK1Dw_isPlusType_others_of_paired hxO hno
    have hQplus := ggK1Dw_isPlusType_qPlus Qf hQ
    have hWplus : IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (Fin r ⊕ Fin r) K))).subtype) :=
      (hprod.mp hQplus).mpr hRplus
    rw [isPlusType_congr (ggK1Dw_restrictIso Qf (x : GL (Fin r ⊕ Fin r) K)),
      hd1, ggK1Dw_eps0_one]
    simp [hWplus]
  · have hd2 : ggMultOrd p nf = 2 := by
      rw [ggMultOrd, if_neg hsub]
      split_ifs with h2
      · rfl
      · exact absurd (hdvd.resolve_left hsub) h2
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hdvd.resolve_left hsub
    set R := othersSpace ((ggK1DLin (x : GL (Fin r ⊕ Fin r) K)).toLinearMap) (X - 1) with hR
    have hRinv : ∀ u ∈ R, ggK1DLin (x : GL (Fin r ⊕ Fin r) K) u ∈ R := by
      intro u hu
      have hmap : R.map (ggK1DOrthEnd (x : GL (Fin r ⊕ Fin r) K)) ≤ R := by
        rw [hR]; unfold othersSpace
        rw [Submodule.map_iSup]
        refine iSup_le fun k => ?_
        rw [Submodule.map_iSup]
        refine iSup_le fun hk => ?_
        refine le_iSup₂_of_le k hk ?_
        rintro _ ⟨v, hv, rfl⟩
        exact apply_mem_primaryComponent (Commute.refl _) hv
      exact hmap ⟨u, hu, rfl⟩
    have hRfix : ∀ u ∈ R, ggK1DLin (x : GL (Fin r ⊕ Fin r) K) u = u → u = 0 := by
      intro u hu hxu
      exact (Submodule.disjoint_def.1 (hxO.fixed_others).1.disjoint) u (mem_fixedSpace.2 hxu) hu
    have hRreg : RegOn Qf R := by
      intro u hu hperp
      refine hxO.regular u fun v => ?_
      have hv : v ∈ fixedSpace (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) ⊔ R := by
        rw [hR]; exact (hxO.fixed_others).1.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨w, hw, rr, hr, rfl⟩ := Submodule.mem_sup.mp hv
      rw [QuadraticMap.polar_add_right, hperp rr hr, QuadraticMap.polar_comm Qf u w,
        (hxO.fixed_others).2 w hw u hu, add_zero]
    have hRtype := isPlusType_iff_even_of_fixedFree hxO hp hp2 hpq m.tail.sum R
      hRinv hRreg hRfix hRdim
    have hWtype : IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (Fin r ⊕ Fin r) K))).subtype) ↔
        (IsPlusType Qf ↔ Even m.tail.sum) := by
      have h1 := hprod
      rw [hRtype] at h1
      tauto
    have hWeven : IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (Fin r ⊕ Fin r) K))).subtype) ↔
        Even m.tail.sum := by
      rw [hWtype]; simp [ggK1Dw_isPlusType_qPlus Qf hQ]
    rw [isPlusType_congr (ggK1Dw_restrictIso Qf (x : GL (Fin r ⊕ Fin r) K)), hWeven,
      hd2, ggK1Dw_eps0_two_false p m hm.length_eq]

theorem ggK1D_v0_witt_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf (ggMultOrd p nf) r K
      (x : GL (LargeEvenMinusIdx (r - 1)) K) m)
    (hx : x ^ p = 1)
    (Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K))
    (hQ : LargeEvenQMinus (r - 1) b c = ⇑Qf) :
    (CFSG.GroupTheory.WeirSylow.IsPlusType
        (Qf.restrict (primaryComponent
          (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) (X - 1))) ↔
      ggMultEps0 p (ggMultOrd p nf) true m = true) := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hr0 : r ≠ 0 := fun hr => (ggK1Dw_false_of_r_zero hp hp2 hdvd hnf hK hirr hm hx hr).elim
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hxO := ggK1Dw_oddOrder_minus hp hp2 hnf hK hirr hx Qf hQ
  have hhead := ggK1Dw_head_eq (x := (x : GL (LargeEvenMinusIdx (r - 1)) K)) hm.head_eq
  have hVdim : Module.finrank K (LargeEvenMinusIdx (r - 1) → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [LargeEvenMinusIdx]; omega
  have hWdim : Module.finrank K (fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))) =
      2 * m.headD 0 := by
    obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
    have h1 : m.headD 0 = s := by rw [hhead, hs]; omega
    rw [hs, h1]; omega
  have hRdim := ggK1Dw_finrank_others_eq hxO hVdim hhead hm.sum_eq
  have hprod := ggK1Dw_isPlusType_prod_decomp hxO hWdim hRdim
  by_cases hsub : p ∣ 2 ^ nf - 1
  · have hd1 : ggMultOrd p nf = 1 := by simp [ggMultOrd, hsub]
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hsub
    have hno : ∀ h ∈ primaryFactors (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)),
        h ≠ X - 1 → h ≠ reciprocalPolynomial h :=
      fun h hh hne => ggK1Dw_ne_reciprocal_of_dvd_sub_one hxO hp hp2 hpq hh hne
    have hRplus := ggK1Dw_isPlusType_others_of_paired hxO hno
    have hQminus := ggK1Dw_not_isPlusType_qMinus hirr Qf hQ
    have hWminus : ¬ IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))).subtype) := by
      intro hW
      exact hQminus (hprod.mpr ⟨fun _ => hRplus, fun _ => hW⟩)
    rw [isPlusType_congr (ggK1Dw_restrictIso Qf (x : GL (LargeEvenMinusIdx (r - 1)) K)),
      hd1, ggK1Dw_eps0_one]
    simp [hWminus]
  · have hd2 : ggMultOrd p nf = 2 := by
      rw [ggMultOrd, if_neg hsub]
      split_ifs with h2
      · rfl
      · exact absurd (hdvd.resolve_left hsub) h2
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hdvd.resolve_left hsub
    set R := othersSpace ((ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)).toLinearMap) (X - 1)
        with hR
    have hRinv : ∀ u ∈ R, ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) u ∈ R := by
      intro u hu
      have hmap : R.map (ggK1DOrthEnd (x : GL (LargeEvenMinusIdx (r - 1)) K)) ≤ R := by
        rw [hR]; unfold othersSpace
        rw [Submodule.map_iSup]
        refine iSup_le fun k => ?_
        rw [Submodule.map_iSup]
        refine iSup_le fun hk => ?_
        refine le_iSup₂_of_le k hk ?_
        rintro _ ⟨v, hv, rfl⟩
        exact apply_mem_primaryComponent (Commute.refl _) hv
      exact hmap ⟨u, hu, rfl⟩
    have hRfix : ∀ u ∈ R, ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) u = u → u = 0 := by
      intro u hu hxu
      exact (Submodule.disjoint_def.1 (hxO.fixed_others).1.disjoint) u (mem_fixedSpace.2 hxu) hu
    have hRreg : RegOn Qf R := by
      intro u hu hperp
      refine hxO.regular u fun v => ?_
      have hv : v ∈ fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) ⊔ R := by
        rw [hR]; exact (hxO.fixed_others).1.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨w, hw, rr, hr, rfl⟩ := Submodule.mem_sup.mp hv
      rw [QuadraticMap.polar_add_right, hperp rr hr, QuadraticMap.polar_comm Qf u w,
        (hxO.fixed_others).2 w hw u hu, add_zero]
    have hRtype := isPlusType_iff_even_of_fixedFree hxO hp hp2 hpq m.tail.sum R
      hRinv hRreg hRfix hRdim
    have hWtype : IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))).subtype) ↔
        (IsPlusType Qf ↔ Even m.tail.sum) := by
      have h1 := hprod
      rw [hRtype] at h1
      tauto
    have hWodd : IsPlusType
        (Qf.comp (fixedSpace (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))).subtype) ↔
        Odd m.tail.sum := by
      rw [hWtype]; simp [ggK1Dw_not_isPlusType_qMinus hirr Qf hQ, Nat.not_even_iff_odd]
    rw [isPlusType_congr (ggK1Dw_restrictIso Qf (x : GL (LargeEvenMinusIdx (r - 1)) K)),
      hWodd, hd2, ggK1Dw_eps0_two_true p m hm.length_eq]

end CFSG.StandardType

end
