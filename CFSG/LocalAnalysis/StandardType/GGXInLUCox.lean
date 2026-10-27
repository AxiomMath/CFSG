module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
import CFSG.Assembly.GL83StatedBridge
import CFSG.RankThree.PartOne.KF.ClsSUUpper
import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
import CFSG.HardMathSupport.Foote.E27.UniMonomial
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
import CFSG.HardMathSupport.Foote.E27.NormalAbelianEquiv

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

private def suThreeFactor (i : ℕ) : ℕ := if Even i then 2 ^ i - 1 else 2 ^ i + 1

private theorem suThreeFactor_cast (i : ℕ) :
    ((suThreeFactor i : ℕ) : ℤ) = 2 ^ i - (-1) ^ i := by
  rcases Nat.even_or_odd i with hi | hi
  · simp only [suThreeFactor, if_pos hi, Nat.cast_sub (Nat.one_le_pow' i 1), Nat.cast_one,
      Nat.cast_pow, Even.neg_one_pow hi]
    ring
  · simp only [suThreeFactor, if_neg (Nat.not_even_iff_odd.mpr hi), Nat.cast_add, Nat.cast_one,
      Nat.cast_pow, Nat.cast_ofNat, Odd.neg_one_pow hi]
    ring

private theorem suThreeFactor_pos {i : ℕ} (hi : 2 ≤ i) : 0 < suThreeFactor i := by
  rw [suThreeFactor]
  split_ifs
  · have h1 : 1 < 2 ^ i := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  · positivity

private theorem suThreeFactor_factorization {i : ℕ} (hi : 2 ≤ i) :
    (suThreeFactor i).factorization 3 = 1 + i.factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three]
  rcases Nat.even_or_odd i with he | ho
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := by
      obtain ⟨j, hj⟩ := he
      exact ⟨j, by omega⟩
    have hj : j ≠ 0 := by omega
    have hE : Even (2 * j) := ⟨j, by omega⟩
    have hpow : 2 ^ (2 * j) = 4 ^ j := by
      rw [show (2 : ℕ) ^ (2 * j) = ((2 : ℕ) ^ 2) ^ j by rw [pow_mul]]
      norm_num
    have hu : suThreeFactor (2 * j) = 4 ^ j - 1 ^ j := by
      simp only [suThreeFactor, if_pos hE, hpow, one_pow]
    have hlte := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := 4) (y := 1)
      (by norm_num) (by norm_num) (by norm_num) (n := j) hj
    have h4 : padicValNat 3 (4 - 1) = 1 := by norm_num
    have h2j : padicValNat 3 (2 * j) = padicValNat 3 j := by
      rw [padicValNat.mul (by norm_num) hj,
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]
    rw [hu, hlte, h4, h2j]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := by
      obtain ⟨j, hj⟩ := ho
      exact ⟨j, by omega⟩
    have hO : Odd (2 * j + 1) := ⟨j, by omega⟩
    have hnE : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr hO
    have hu : suThreeFactor (2 * j + 1) = 2 ^ (2 * j + 1) + 1 ^ (2 * j + 1) := by
      simp only [suThreeFactor, if_neg hnE, one_pow]
    have hlte := padicValNat.pow_add_pow (p := 3) (by decide : Odd 3) (x := 2) (y := 1)
      (by norm_num) (by norm_num) (n := 2 * j + 1) hO
    have h3 : padicValNat 3 (2 + 1) = 1 := by norm_num
    rw [hu, hlte, h3]

omit [Finite K] in
theorem lup8f_factorization_three_card_SU (hK : Nat.card K = 4) (hn : 1 ≤ n) :
    (Nat.card (LargeEvenSUGroup (Fin n) K 2)).factorization 3 =
      (n - 1) + n.factorial.factorization 3 := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    USixTwo.fieldDataFour hK
  have : CharP K 2 := hU.charP
  have hraw := CFSG.RankThree.PartOne.KFU.card_statedSU_eq (f := 1) (K := K) (n := n) hU hn
  have hprod : (∏ i ∈ Finset.Icc 2 n, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i)) =
      ((∏ i ∈ Finset.Icc 2 n, suThreeFactor i : ℕ) : ℤ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((2 ^ 1 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
    exact (suThreeFactor_cast i).symm
  have hcardN : Nat.card (CFSG.Open.StatedSU n 2 K) =
      2 ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, suThreeFactor i := by
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_mul, ← hprod]
    simpa using hraw
  rw [largeEvenSUGroup_eq_statedSU, hcardN]
  have hne : ∀ i ∈ Finset.Icc 2 n, suThreeFactor i ≠ 0 :=
    fun i hi => (suThreeFactor_pos (Finset.mem_Icc.mp hi).1).ne'
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.mpr hne),
    Finsupp.add_apply, Nat.factorization_prod_apply hne]
  have hpowfac : (2 ^ (n * (n - 1) / 2)).factorization 3 = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), mul_zero]
  have hsum : ∑ i ∈ Finset.Icc 2 n, (suThreeFactor i).factorization 3 =
      (n - 1) + ∑ i ∈ Finset.Icc 2 n, i.factorization 3 := by
    rw [Finset.sum_congr rfl fun i hi => suThreeFactor_factorization (Finset.mem_Icc.mp hi).1]
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
    congr 1
  have hfac : n.factorial.factorization 3 = ∑ i ∈ Finset.Icc 2 n, i.factorization 3 := by
    have h1 : (∏ i ∈ Finset.Icc 1 n, i) = n.factorial := by
      rw [← Finset.prod_Ico_id_eq_factorial n, Finset.Ico_add_one_right_eq_Icc]
    rw [← h1, Nat.factorization_prod_apply (fun i hi => by
      have := (Finset.mem_Icc.mp hi).1
      omega)]
    conv_lhs => rw [← Finset.insert_Icc_add_one_left_eq_Icc (a := 1) hn]
    rw [Finset.sum_insert (by simp), Nat.factorization_one, Finsupp.zero_apply, zero_add]
    norm_num
  rw [hpowfac, zero_add, hsum, hfac]

omit [Finite K] in
private theorem lup8f_cox_unit_cube (hK : Nat.card K = 4) (t : Kˣ) : t ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have := pow_card_eq_one' (G := Kˣ) (x := t)
  rwa [h3] at this

omit [Finite K] in
private theorem lup8f_cox_diagGL_eq :
    lup8f_diagGL n K = TauCeti.diagGL (k := K) (ι := Fin n) :=
  MonoidHom.ext fun t => Units.ext (by rw [TauCeti.diagGL_coe]; rfl)

omit [Finite K] in
private theorem lup8f_cox_diagGL_mem_SU (hK : Nat.card K = 4) (t : Fin n → Kˣ)
    (ht : ∏ i, t i = 1) : lup8f_diagGL n K t ∈ LargeEvenSUGroup (Fin n) K 2 := by
  have hval : ((lup8f_diagGL n K t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (t i : K)) := rfl
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hval, Matrix.det_diagonal, ← Units.coe_prod, ht, Units.val_one]
  · rw [hval, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, lup8f_cox_unit_cube hK (t i), Units.val_one]

omit [Finite K] in
private theorem lup8f_cox_permutationGL_mem_SU (hK : Nat.card K = 4) (π : Equiv.Perm (Fin n)) :
    TauCeti.permutationGL (k := K) π ∈ LargeEvenSUGroup (Fin n) K 2 := by
  have hC : CharP K 2 := (USixTwo.fieldDataFour hK).charP
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [TauCeti.permutationGL_coe, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h <;> rw [h] <;>
      simp [CharTwo.neg_eq]
  · rw [TauCeti.permutationGL_coe]
    have hmap : ((π⁻¹).permMatrix K).map (· ^ 2) = (π⁻¹).permMatrix K := by
      ext i j
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_inv, inv_mul_cancel,
      Matrix.permMatrix_one]

private theorem lup8f_cox_conj_mem_SU (hK : Nat.card K = 4) {P : GL (Fin n) K}
    (hP : P ∈ LargeEvenGUSet (Fin n) K 2) {y : GL (Fin n) K}
    (hy : y ∈ LargeEvenSUGroup (Fin n) K 2) :
    P * y * P⁻¹ ∈ LargeEvenSUGroup (Fin n) K 2 := by
  have hC : CharP K 2 := (USixTwo.fieldDataFour hK).charP
  exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su (d := n) (j := 1) hP hy

private def lup8f_coxDg (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  TauCeti.diagonalTorus K n

private def lup8f_coxW (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.normalizer (lup8f_coxDg n K : Set (GL (Fin n) K))

private def lup8f_coxMon (n : ℕ) (K : Type) [Field K] (P : GL (Fin n) K) :
    Subgroup (GL (Fin n) K) :=
  (lup8f_coxW n K).map (MulAut.conj P).toMonoidHom

private def lup8f_coxM0 (n : ℕ) (K : Type) [Field K] (P : GL (Fin n) K) :
    Subgroup ↥(LargeEvenSUGroup (Fin n) K 2) :=
  (lup8f_coxMon n K P).subgroupOf (LargeEvenSUGroup (Fin n) K 2)

omit [Finite K] in
private theorem lup8f_cox_mem_M0 {P : GL (Fin n) K}
    {x : ↥(LargeEvenSUGroup (Fin n) K 2)} :
    x ∈ lup8f_coxM0 n K P ↔ (x : GL (Fin n) K) ∈ lup8f_coxMon n K P := by
  rw [lup8f_coxM0, Subgroup.mem_subgroupOf]

omit [Finite K] in
private theorem lup8f_cox_frameTorusGL_le_Mon (P : GL (Fin n) K) :
    lup8f_frameTorusGL n K P ≤ lup8f_coxMon n K P := by
  have h1 : Subgroup.map (lup8f_diagGL n K) (lup8f_prodOne n K) ≤ lup8f_coxDg n K := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hx
    rw [lup8f_coxDg]
    exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, by rw [lup8f_cox_diagGL_eq]⟩
  have h2 : lup8f_coxDg n K ≤ lup8f_coxW n K := by
    rw [lup8f_coxW]
    exact Subgroup.le_normalizer
  intro x hx
  rw [lup8f_frameTorusGL] at hx
  rw [lup8f_coxMon]
  exact Subgroup.map_mono h2 (Subgroup.map_mono h1 hx)

private theorem lup8f_cox_frameTorusGL_le_SU (hK : Nat.card K = 4) (P : GL (Fin n) K)
    (hP : P ∈ LargeEvenGUSet (Fin n) K 2) :
    lup8f_frameTorusGL n K P ≤ LargeEvenSUGroup (Fin n) K 2 := by
  intro g hg
  rw [lup8f_frameTorusGL, Subgroup.mem_map] at hg
  obtain ⟨d, hd, rfl⟩ := hg
  rw [Subgroup.mem_map] at hd
  obtain ⟨t, ht, rfl⟩ := hd
  show P * lup8f_diagGL n K t * P⁻¹ ∈ LargeEvenSUGroup (Fin n) K 2
  exact lup8f_cox_conj_mem_SU hK hP (lup8f_cox_diagGL_mem_SU hK t ht)

private theorem lup8f_cox_frameTorus_iff (hK : Nat.card K = 4) {P g : GL (Fin n) K}
    (hg : g ∈ LargeEvenSUGroup (Fin n) K 2) :
    P⁻¹ * g * P ∈ TauCeti.diagonalTorus K n ↔ g ∈ lup8f_frameTorusGL n K P := by
  have hC : CharP K 2 := (USixTwo.fieldDataFour hK).charP
  constructor
  · intro h
    obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp h
    have ht' : (lup8f_diagGL n K t : GL (Fin n) K) = P⁻¹ * g * P := by
      rw [lup8f_cox_diagGL_eq]
      exact ht
    have hg1 : g ∈ LargeEvenSUGroup (Fin n) K (2 ^ 1) := hg
    have hdet : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
      ((CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff (d := n) (g := 1) g).mp hg1).1
    have hPP : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hdetR : (((P⁻¹ * g * P : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
        ← Matrix.det_mul, hPP, Matrix.det_one]
    have h1 : (∏ i, (t i : K)) = 1 := by
      have h := congrArg (fun x : GL (Fin n) K => ((x : Matrix (Fin n) (Fin n) K)).det) ht'
      rw [show ((lup8f_diagGL n K t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.diagonal (fun i => (t i : K)) from rfl, Matrix.det_diagonal] at h
      rwa [hdetR] at h
    have hprod : ∏ i, t i = 1 := by
      apply Units.ext
      simpa using h1
    rw [lup8f_frameTorusGL, Subgroup.mem_map]
    exact ⟨lup8f_diagGL n K t, Subgroup.mem_map_of_mem _ hprod, by
      show P * lup8f_diagGL n K t * P⁻¹ = g
      rw [ht']
      group⟩
  · intro hg'
    rw [lup8f_frameTorusGL, Subgroup.mem_map] at hg'
    obtain ⟨d, hd, rfl⟩ := hg'
    rw [Subgroup.mem_map] at hd
    obtain ⟨t, -, rfl⟩ := hd
    show P⁻¹ * (P * lup8f_diagGL n K t * P⁻¹) * P ∈ TauCeti.diagonalTorus K n
    rw [show P⁻¹ * (P * lup8f_diagGL n K t * P⁻¹) * P = lup8f_diagGL n K t by group]
    rw [lup8f_cox_diagGL_eq]
    exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩

omit [Finite K] in
private theorem lup8f_cox_card_frameTorusGL (hK : Nat.card K = 4) (P : GL (Fin n) K)
    (hn : 1 ≤ n) : Nat.card (lup8f_frameTorusGL n K P) = 3 ^ (n - 1) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K := USixTwo.fieldDataFour hK
  have hEq : lup8f_prodOne n K = CFSG.HardMathSupport.Foote.E27.Uni.prodKer n K := by
    ext t
    simp [lup8f_prodOne, CFSG.HardMathSupport.Foote.E27.Uni.prodKer,
      CFSG.HardMathSupport.Foote.E27.Uni.prodHom, MonoidHom.mem_ker]
  have hinj : Function.Injective (lup8f_diagGL n K) := by
    intro a b hab
    exact TauCeti.diagGL_injective (by rwa [lup8f_cox_diagGL_eq] at hab)
  have h1 : Nat.card (lup8f_frameTorusGL n K P) =
      Nat.card (Subgroup.map (lup8f_diagGL n K) (lup8f_prodOne n K)) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj P).toMonoidHom) (MulAut.conj P).injective
  have h2 : Nat.card (Subgroup.map (lup8f_diagGL n K) (lup8f_prodOne n K)) =
      Nat.card (lup8f_prodOne n K) :=
    Subgroup.card_map_of_injective (f := lup8f_diagGL n K) hinj
  rw [h1, h2, hEq, CFSG.HardMathSupport.Foote.E27.Uni.card_prodKer (E := K) hU hn]

theorem lup8f_frame_coxeter (_hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame3 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hT : lup8f_TorusData ((lup8f_HT L Bs) ⧸ C.N)
      ((lup8f_E' L Bs).map (QuotientGroup.mk' C.N))
      ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) (lup8f_frameT F)
      (QuotientGroup.mk' C.N ⟨x, Subgroup.mem_sup_left hxL⟩))
    (_hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    ∃ Nsub : Subgroup ((lup8f_HT L Bs) ⧸ C.N),
      lup8f_CoxeterData ((lup8f_HT L Bs) ⧸ C.N)
        ((lup8f_E' L Bs).map (QuotientGroup.mk' C.N))
        ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) (lup8f_frameT F) Nsub := by
  classical
  have hnt : Nontrivial Kˣ := by
    rcases subsingleton_or_nontrivial Kˣ with h | h
    · exfalso
      have h1 : Nat.card Kˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h, inferInstance⟩
      rw [Nat.card_units, M.card_K] at h1
      norm_num at h1
    · exact h
  let L0 : Subgroup ((lup8f_HT L Bs) ⧸ C.N) := (lup8f_L' L Bs).map (QuotientGroup.mk' C.N)
  let E0 : Subgroup ((lup8f_HT L Bs) ⧸ C.N) := (lup8f_E' L Bs).map (QuotientGroup.mk' C.N)
  let T : Subgroup ((lup8f_HT L Bs) ⧸ C.N) := lup8f_frameT F
  let Nsub : Subgroup ((lup8f_HT L Bs) ⧸ C.N) :=
    ((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom).map L0.subtype
  have hNsubDef : Nsub =
      ((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom).map L0.subtype := rfl
  have hTdef : T = lup8f_frameT F := rfl
  have hE0def : E0 = (lup8f_E' L Bs).map (QuotientGroup.mk' C.N) := rfl
  have htoW_mem : ∀ y : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom),
      F.P⁻¹ * (F.eps (y : ↥L0) : GL (Fin n) K) * F.P ∈ lup8f_coxW n K := by
    intro y
    have hy : (F.eps (y : ↥L0) : GL (Fin n) K) ∈ lup8f_coxMon n K F.P :=
      (lup8f_cox_mem_M0 (n := n) (K := K) (P := F.P)).mp (Subgroup.mem_comap.mp y.2)
    rw [lup8f_coxMon] at hy
    obtain ⟨w, hwW, hw⟩ := Subgroup.mem_map.mp hy
    have hEq : F.P⁻¹ * (F.eps (y : ↥L0) : GL (Fin n) K) * F.P = (w : GL (Fin n) K) := by
      rw [← hw]
      show F.P⁻¹ * (F.P * (w : GL (Fin n) K) * F.P⁻¹) * F.P = (w : GL (Fin n) K)
      group
    rw [hEq]
    exact hwW
  let toW : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom) →* ↥(lup8f_coxW n K) :=
    { toFun := fun y => ⟨F.P⁻¹ * (F.eps (y : ↥L0) : GL (Fin n) K) * F.P, htoW_mem y⟩
      map_one' := by
        apply Subtype.ext
        show F.P⁻¹ * (F.eps ((1 : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom)) :
          ↥L0) : GL (Fin n) K) * F.P = 1
        rw [show ((1 : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom)) : ↥L0) = 1 from rfl,
          map_one, Subgroup.coe_one]
        group
      map_mul' := by
        intro y z
        apply Subtype.ext
        show F.P⁻¹ * (F.eps ((y * z : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom)) :
          ↥L0) : GL (Fin n) K) * F.P =
          (F.P⁻¹ * (F.eps (y : ↥L0) : GL (Fin n) K) * F.P) *
            (F.P⁻¹ * (F.eps (z : ↥L0) : GL (Fin n) K) * F.P)
        rw [show ((y * z : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom)) : ↥L0) =
          (y : ↥L0) * (z : ↥L0) from rfl, map_mul, Subgroup.coe_mul]
        group }
  have hNsub_le_l0' : Nsub ≤ L0 := Subgroup.map_subtype_le _
  have hsub : Nsub.subgroupOf L0 = (lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom := by
    rw [hNsubDef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      Subtype.val_injective]
  let he : ↥Nsub ≃* ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hNsub_le_l0').symm.trans (MulEquiv.subgroupCongr hsub)
  have he_coe : ∀ ν : ↥Nsub,
      ((he ν : ↥L0) : (lup8f_HT L Bs) ⧸ C.N) = (ν : (lup8f_HT L Bs) ⧸ C.N) := by
    intro ν
    exact Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe hNsub_le_l0' ν
  let ψ : ↥Nsub →* Equiv.Perm (Fin n) :=
    (TauCeti.diagonalNormalizerPerm (k := K) (n := n)).comp (toW.comp he.toMonoidHom)
  have hψ_apply : ∀ ν : ↥Nsub, ψ ν = TauCeti.diagonalNormalizerPerm (k := K) (n := n)
      ⟨F.P⁻¹ * (F.eps (he ν : ↥L0) : GL (Fin n) K) * F.P, htoW_mem (he ν)⟩ := fun ν => rfl
  have hψ_surj : Function.Surjective ψ := by
    intro π
    have hSU : (TauCeti.permutationGL (k := K) π : GL (Fin n) K) ∈
        LargeEvenSUGroup (Fin n) K 2 := lup8f_cox_permutationGL_mem_SU M.card_K π
    have hconjSU : (F.P * (TauCeti.permutationGL (k := K) π : GL (Fin n) K) * F.P⁻¹) ∈
        LargeEvenSUGroup (Fin n) K 2 := lup8f_cox_conj_mem_SU M.card_K F.P_mem hSU
    have hmon : (F.P * (TauCeti.permutationGL (k := K) π : GL (Fin n) K) * F.P⁻¹) ∈
        lup8f_coxMon n K F.P := by
      rw [lup8f_coxMon]
      exact Subgroup.mem_map.mpr ⟨TauCeti.permutationGL (k := K) π,
        TauCeti.permutationGL_mem_normalizer π, rfl⟩
    let g0 : ↥(LargeEvenSUGroup (Fin n) K 2) :=
      ⟨F.P * (TauCeti.permutationGL (k := K) π : GL (Fin n) K) * F.P⁻¹, hconjSU⟩
    have hy0 : F.eps.symm g0 ∈
        (lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom := by
      rw [Subgroup.mem_comap, show F.eps.toMonoidHom (F.eps.symm g0) = g0 from
        MulEquiv.apply_symm_apply F.eps g0, lup8f_cox_mem_M0]
      exact hmon
    let y0 : ↥((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom) := ⟨F.eps.symm g0, hy0⟩
    refine ⟨⟨L0.subtype y0, Subgroup.mem_map_of_mem _ y0.2⟩, ?_⟩
    have hhe : he ⟨L0.subtype y0, Subgroup.mem_map_of_mem _ y0.2⟩ = y0 :=
      Subtype.ext (Subtype.ext (by
        rw [he_coe ⟨L0.subtype y0, Subgroup.mem_map_of_mem _ y0.2⟩]
        rfl))
    refine TauCeti.diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ 1 π ?_
    show F.P⁻¹ * (F.eps (he ⟨L0.subtype y0, Subgroup.mem_map_of_mem _ y0.2⟩ : ↥L0) :
      GL (Fin n) K) * F.P = TauCeti.diagGL (1 : Fin n → Kˣ) * TauCeti.permutationGL (k := K) π
    rw [hhe]
    have hy0eps : F.eps (y0 : ↥L0) = g0 := MulEquiv.apply_symm_apply F.eps g0
    rw [hy0eps]
    show F.P⁻¹ * (F.P * (TauCeti.permutationGL (k := K) π : GL (Fin n) K) * F.P⁻¹) *
      F.P = TauCeti.diagGL (1 : Fin n → Kˣ) * TauCeti.permutationGL (k := K) π
    rw [map_one, one_mul]
    group
  have hψ_ker : ψ.ker = T.subgroupOf Nsub := by
    ext ν
    rw [MonoidHom.mem_ker, hψ_apply ν, TauCeti.diagonalNormalizerPerm_eq_one_iff,
      Subgroup.mem_subgroupOf]
    have hTmem : (ν : (lup8f_HT L Bs) ⧸ C.N) ∈ T ↔
        (F.eps (he ν : ↥L0) : GL (Fin n) K) ∈ lup8f_frameTorusGL n K F.P := by
      rw [hTdef, lup8f_frameT, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyeq⟩
        have hyeq' : ((y : ↥L0) : (lup8f_HT L Bs) ⧸ C.N) =
            (ν : (lup8f_HT L Bs) ⧸ C.N) := hyeq
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hy
        have h1 : (y : ↥L0) = (he ν : ↥L0) := Subtype.ext (by
          show ((y : ↥L0) : (lup8f_HT L Bs) ⧸ C.N) =
            (((he ν : ↥L0) : (lup8f_HT L Bs) ⧸ C.N))
          rw [hyeq', ← he_coe ν])
        have hyy : y = (he ν : ↥L0) := Subtype.val_injective (by
          show ((y : (lup8f_HT L Bs) ⧸ C.N)) =
            (((he ν : ↥L0) : (lup8f_HT L Bs) ⧸ C.N))
          rw [hyeq', ← he_coe ν])
        rwa [hyy] at hy
      · intro h
        exact ⟨he ν, Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr h), he_coe ν⟩
    rw [hTmem]
    exact lup8f_cox_frameTorus_iff M.card_K (F.eps (he ν : ↥L0)).2
  have hT_normal : (T.subgroupOf Nsub).Normal := hψ_ker ▸ MonoidHom.normal_ker ψ
  have hT_le_nsub : T ≤ Nsub := by
    intro t ht
    rw [hTdef, lup8f_frameT, Subgroup.mem_map] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hy
    rw [hNsubDef, Subgroup.mem_map]
    exact ⟨y, Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr
      (lup8f_cox_frameTorusGL_le_Mon F.P hy)), rfl⟩
  have hNsub_le_l0 : Nsub ≤ L0 := hNsub_le_l0'
  have hNsub_le_norm : Nsub ≤ Subgroup.normalizer (E0 : Set ((lup8f_HT L Bs) ⧸ C.N)) := by
    have hclaim : ∀ ν ∈ Nsub, ∀ e ∈ E0, ν * e * ν⁻¹ ∈ E0 := by
      intro ν hν e he
      rw [hNsubDef, Subgroup.mem_map] at hν
      obtain ⟨u, hu, rfl⟩ := hν
      rw [hE0def, Subgroup.mem_map] at he
      obtain ⟨b, hb, hbe⟩ := he
      rw [← hbe]
      let b' : ↥(lup8f_E' L Bs) := ⟨b, hb⟩
      obtain ⟨l0, hl0mem, hl0⟩ := Subgroup.mem_map.mp u.2
      let l0' : ↥(lup8f_L' L Bs) := ⟨l0, hl0mem⟩
      have huMon : (F.eps u : GL (Fin n) K) ∈ lup8f_coxMon n K F.P :=
        (lup8f_cox_mem_M0 (n := n) (K := K) (P := F.P)).mp (Subgroup.mem_comap.mp hu)
      rw [lup8f_coxMon] at huMon
      obtain ⟨w, hwW, hw⟩ := Subgroup.mem_map.mp huMon
      rw [lup8f_coxW, lup8f_coxDg] at hwW
      obtain ⟨σ, hσ⟩ := F.diag b'
      have hdiag : (F.P⁻¹ : GL (Fin n) K) * F.mat b' * F.P = lup8f_diagGL n K σ := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact hσ
      have hDw : (F.mat b' : GL (Fin n) K) = F.P * lup8f_diagGL n K σ * F.P⁻¹ := by
        rw [← hdiag]
        group
      have hw' : (F.eps u : GL (Fin n) K) = F.P * (w : GL (Fin n) K) * F.P⁻¹ := by
        rw [← hw]
        rfl
      have hu' : (⟨QuotientGroup.mk' C.N ((l0'⁻¹ : ↥(lup8f_L' L Bs)) : lup8f_HT L Bs),
          Subgroup.mem_map_of_mem _ (l0'⁻¹).2⟩ : ↥L0) = u⁻¹ := by
        apply Subtype.ext
        show QuotientGroup.mk' C.N ((l0'⁻¹ : ↥(lup8f_L' L Bs)) : lup8f_HT L Bs) =
          (u : (lup8f_HT L Bs) ⧸ C.N)⁻¹
        rw [Subgroup.coe_inv (x := l0'), map_inv, hl0]
      have hepsinv : (F.eps (⟨QuotientGroup.mk' C.N ((l0'⁻¹ : ↥(lup8f_L' L Bs)) :
          lup8f_HT L Bs), Subgroup.mem_map_of_mem _ (l0'⁻¹).2⟩ : ↥L0) : GL (Fin n) K) =
          (F.eps u)⁻¹ := by
        rw [hu', map_inv]
      have hmat := F.mat_ind b' (l0'⁻¹)
      have hconjL : (F.eps (lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs) F.E'_le_norm b'
          l0'⁻¹) : GL (Fin n) K) = F.mat b' * (F.eps u)⁻¹ * (F.mat b')⁻¹ := by
        rw [hmat, MulAut.conj_apply, hepsinv]
      have hcalc : (F.eps (u * lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs)
          F.E'_le_norm b' l0'⁻¹) : GL (Fin n) K) =
          F.P * ((w : GL (Fin n) K) * lup8f_diagGL n K σ * (w : GL (Fin n) K)⁻¹ *
            (lup8f_diagGL n K σ)⁻¹) * F.P⁻¹ := by
        have hwinv : ((F.eps u : GL (Fin n) K))⁻¹ =
            (F.P * (w : GL (Fin n) K) * F.P⁻¹)⁻¹ := by rw [hw']
        rw [map_mul, Subgroup.coe_mul, hw', hconjL, hDw, Subgroup.coe_inv, hwinv]
        group
      have hframe : F.eps (u * lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs)
          F.E'_le_norm b' l0'⁻¹) ∈
          (lup8f_frameTorusGL n K F.P).subgroupOf (LargeEvenSUGroup (Fin n) K 2) := by
        rw [Subgroup.mem_subgroupOf]
        let g1 : ↥(LargeEvenSUGroup (Fin n) K 2) :=
          F.eps (u * lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs) F.E'_le_norm b' l0'⁻¹)
        have hg1 : (g1 : GL (Fin n) K) ∈ LargeEvenSUGroup (Fin n) K 2 := g1.2
        refine (lup8f_cox_frameTorus_iff M.card_K (P := F.P) (g := (g1 : GL (Fin n) K))
          hg1).mp ?_
        have hcancel : F.P⁻¹ * (F.P * ((w : GL (Fin n) K) * lup8f_diagGL n K σ *
            (w : GL (Fin n) K)⁻¹ * (lup8f_diagGL n K σ)⁻¹) * F.P⁻¹) * F.P =
            (w : GL (Fin n) K) * lup8f_diagGL n K σ * (w : GL (Fin n) K)⁻¹ *
              (lup8f_diagGL n K σ)⁻¹ := by group
        rw [hcalc, hcancel]
        have hD : lup8f_diagGL n K σ ∈ TauCeti.diagonalTorus K n :=
          TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨σ, by rw [lup8f_cox_diagGL_eq]⟩
        have hwD : (w : GL (Fin n) K) * lup8f_diagGL n K σ * (w : GL (Fin n) K)⁻¹ ∈
            TauCeti.diagonalTorus K n :=
          (Subgroup.mem_normalizer_iff.mp hwW (lup8f_diagGL n K σ)).mp hD
        exact Subgroup.mul_mem _ hwD (Subgroup.inv_mem _ hD)
      have hmem : u * lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs)
          F.E'_le_norm b' l0'⁻¹ ∈
          ((lup8f_frameTorusGL n K F.P).subgroupOf (LargeEvenSUGroup (Fin n) K 2)).comap
            F.eps.toMonoidHom :=
        Subgroup.mem_comap.mpr hframe
      have hTmem2 : (L0.subtype (u * lup8f_conjLQ C.N (lup8f_L' L Bs)
          (lup8f_E' L Bs) F.E'_le_norm b' l0'⁻¹) :
          (lup8f_HT L Bs) ⧸ C.N) ∈ T := by
        rw [hTdef, lup8f_frameT]
        exact Subgroup.mem_map_of_mem _ hmem
      have hE0mem : (L0.subtype (u * lup8f_conjLQ C.N (lup8f_L' L Bs)
          (lup8f_E' L Bs) F.E'_le_norm b' l0'⁻¹) :
          (lup8f_HT L Bs) ⧸ C.N) ∈ E0 := hT.T_le_E0 hTmem2
      have hprod : L0.subtype u *
          (QuotientGroup.mk' C.N (b : lup8f_HT L Bs)) *
          (L0.subtype u)⁻¹ =
          (L0.subtype (u * lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs)
            F.E'_le_norm b' l0'⁻¹) : (lup8f_HT L Bs) ⧸ C.N) *
          (QuotientGroup.mk' C.N (b : lup8f_HT L Bs)) := by
        have hcj : ∀ x : lup8f_HT L Bs,
            QuotientGroup.mk' C.N (b * x * b⁻¹) =
              QuotientGroup.mk' C.N b * QuotientGroup.mk' C.N x *
                (QuotientGroup.mk' C.N b)⁻¹ := by
          intro x
          rw [map_mul, map_mul, map_inv]
        show L0.subtype u * QuotientGroup.mk' C.N b *
            (L0.subtype u)⁻¹ =
          (L0.subtype u * QuotientGroup.mk' C.N
            (b * ((l0'⁻¹ : ↥(lup8f_L' L Bs)) : lup8f_HT L Bs) * b⁻¹)) *
          QuotientGroup.mk' C.N b
        rw [Subgroup.coe_inv (x := l0'), hcj, map_inv, hl0]
        rw [show L0.subtype u = ((u : ↥L0) : (lup8f_HT L Bs) ⧸ C.N) from rfl]
        group
      rw [hprod]
      exact Subgroup.mul_mem _ hE0mem (Subgroup.mem_map_of_mem _ hb)
    intro ν hν
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact hclaim ν hν e
    · intro he
      have h1 := hclaim ν⁻¹ (Subgroup.inv_mem _ hν) (ν * e * ν⁻¹) he
      have h2 : ν⁻¹ * (ν * e * ν⁻¹) * (ν⁻¹)⁻¹ = e := by group
      rwa [h2] at h1
  have hTnorm : (T.subgroupOf Nsub).Normal := hT_normal
  have he1 : ↥Nsub ⧸ T.subgroupOf Nsub ≃* Equiv.Perm (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hψ_ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj)
  have hcoxeter : ∃ (ι : Type) (M : CoxeterMatrix ι),
      Nonempty (CoxeterSystem M (Nsub ⧸ T.subgroupOf Nsub)) := by
    obtain ⟨e2, -⟩ := CFSG.StandardType.ggCoxeterA_mulEquivPerm (n - 1)
    have hfin : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    exact ⟨Fin (n - 1), CoxeterMatrix.A (n - 1),
      ⟨CoxeterSystem.mk (he1.trans ((Equiv.permCongrHom (finCongr hfin)).symm.trans e2.symm))⟩⟩
  have hcardT : Nat.card T = 3 ^ (n - 1) := by
    have h1 : Nat.card T = Nat.card
        (((lup8f_frameTorusGL n K F.P).subgroupOf
          (LargeEvenSUGroup (Fin n) K 2)).comap F.eps.toMonoidHom) := by
      rw [hTdef, lup8f_frameT]
      exact Subgroup.card_map_of_injective (f := L0.subtype) Subtype.val_injective
    have h2 : Nat.card (((lup8f_frameTorusGL n K F.P).subgroupOf
          (LargeEvenSUGroup (Fin n) K 2)).comap F.eps.toMonoidHom) =
        Nat.card ((lup8f_frameTorusGL n K F.P).subgroupOf
          (LargeEvenSUGroup (Fin n) K 2)) := by
      rw [← Subgroup.card_map_of_injective (f := F.eps.toMonoidHom)
        (show Function.Injective F.eps.toMonoidHom from F.eps.injective),
        Subgroup.map_comap_eq_self_of_surjective F.eps.surjective]
    have h3 : Nat.card ((lup8f_frameTorusGL n K F.P).subgroupOf
        (LargeEvenSUGroup (Fin n) K 2)) = Nat.card (lup8f_frameTorusGL n K F.P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (lup8f_cox_frameTorusGL_le_SU M.card_K F.P F.P_mem)).toEquiv
    rw [h1, h2, h3, lup8f_cox_card_frameTorusGL M.card_K F.P (by omega)]
  have hcardNsub : Nat.card Nsub = n.factorial * 3 ^ (n - 1) := by
    have hq : Nat.card (Nsub ⧸ T.subgroupOf Nsub) = n.factorial := by
      rw [Nat.card_congr he1.toEquiv, Nat.card_perm, Nat.card_fin]
    have hTsub : Nat.card (T.subgroupOf Nsub) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_nsub).toEquiv
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf Nsub)
    rw [hq, hTsub, hcardT] at h
    exact h
  have hcardM0 : Nat.card (lup8f_coxM0 n K F.P) = Nat.card Nsub := by
    have h1 : Nat.card Nsub =
        Nat.card ((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom) := by
      rw [hNsubDef]
      exact Subgroup.card_map_of_injective (f := L0.subtype) Subtype.val_injective
    have h2 : Nat.card ((lup8f_coxM0 n K F.P).comap F.eps.toMonoidHom) =
        Nat.card (lup8f_coxM0 n K F.P) := by
      rw [← Subgroup.card_map_of_injective (f := F.eps.toMonoidHom)
        (show Function.Injective F.eps.toMonoidHom from F.eps.injective),
        Subgroup.map_comap_eq_self_of_surjective F.eps.surjective]
    rw [h1, h2]
  have hcardSU : Nat.card (LargeEvenSUGroup (Fin n) K 2) =
      n.factorial * 3 ^ (n - 1) * (Nsub.subgroupOf L0).index := by
    have h1 : Nat.card (LargeEvenSUGroup (Fin n) K 2) =
        Nat.card (lup8f_coxM0 n K F.P) * (lup8f_coxM0 n K F.P).index :=
      (Subgroup.card_mul_index (lup8f_coxM0 n K F.P)).symm
    rw [hcardM0, hcardNsub] at h1
    have h2 : (lup8f_coxM0 n K F.P).index = (Nsub.subgroupOf L0).index := by
      rw [hsub]
      exact (Subgroup.index_comap_of_surjective (f := F.eps.toMonoidHom)
        (H := lup8f_coxM0 n K F.P) F.eps.surjective).symm
    rw [h2] at h1
    exact h1
  have hidx : ¬ 3 ∣ Nsub.relIndex L0 := by
    have hrel : Nsub.relIndex L0 = (Nsub.subgroupOf L0).index := rfl
    rw [hrel]
    have hne : (Nsub.subgroupOf L0).index ≠ 0 := by
      intro h0
      have hpos : 0 < Nat.card (LargeEvenSUGroup (Fin n) K 2) := Nat.card_pos
      rw [hcardSU, h0, mul_zero] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    have hfac := lup8f_factorization_three_card_SU (n := n) (K := K) M.card_K
      (by omega : 1 ≤ n)
    have hmul : (Nat.card (LargeEvenSUGroup (Fin n) K 2)).factorization 3 =
        n.factorial.factorization 3 + (n - 1) +
          (Nsub.subgroupOf L0).index.factorization 3 := by
      rw [hcardSU, Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
        Nat.factorization_mul (Nat.factorial_ne_zero n) (by positivity), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization_self Nat.prime_three, mul_one]
    have hzero : (Nsub.subgroupOf L0).index.factorization 3 = 0 := by omega
    intro h3
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hne).1 h3
    omega
  refine ⟨Nsub, ?_⟩
  exact ⟨hT_le_nsub, hNsub_le_l0, hNsub_le_norm, hT_normal, hcoxeter, hidx⟩


end CFSG.StandardType.GGXInL

end
