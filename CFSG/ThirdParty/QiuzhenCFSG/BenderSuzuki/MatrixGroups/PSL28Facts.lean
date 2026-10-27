module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.IntegralDomain
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# PSL(2,8) small-group interfaces

This file records statement-only external theorem interfaces for the
`PSL(2,8)` small-group facts used in Peterfalvi, Part II, Chapter II.

Source guide: `docs/PFpart2/ref/PFpart2_external_formalization_guides.md`,
item `NearFieldHallWielandtPackage`; the Chapter II Claim (13) application
uses the prime divisors and strong-real element analysis in the `PSL(2,8)`
standard model.
-/

namespace CFSG.BenderSuzuki
namespace MatrixGroups

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open MatrixGroups
open scoped LinearAlgebra.Projectivization Matrix

universe u

noncomputable section


private theorem psl28_det_range_top (F : Type*) [Field F] :
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    let diagonalGL : GL (Fin 2) F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(u : F), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two])
    refine ⟨diagonalGL, ?_⟩
    ext
    simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem psl28_sl2_binary3_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3)) = 504 := by
  classical
  have hGL : Nat.card (GL (Fin 2) (BinaryGaloisField 3)) = 3528 := by
    letI : Fintype (BinaryGaloisField 3) := Fintype.ofFinite _
    rw [Matrix.card_GL_field]
    have hF : Fintype.card (BinaryGaloisField 3) = 8 := by
      rw [← Nat.card_eq_fintype_card]
      simpa [BinaryGaloisField] using (GaloisField.card 2 3 (by norm_num))
    rw [hF]
    norm_num [Fin.prod_univ_two]
  have hRange :
      Nat.card
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := BinaryGaloisField 3)).range = 7 := by
    rw [psl28_det_range_top]
    simp [Nat.card_units, BinaryGaloisField, GaloisField.card 2 3 (by norm_num)]
  let detHom := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := BinaryGaloisField 3)
  have hmul :
      Nat.card detHom.range * Nat.card detHom.ker =
        Nat.card (GL (Fin 2) (BinaryGaloisField 3)) := by
    rw [← Subgroup.index_ker detHom]
    exact detHom.ker.index_mul_card
  have hker : Nat.card detHom.ker = 504 := by
    rw [hRange, hGL] at hmul
    omega
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3)) =
        Nat.card detHom.ker := by
      let slEquivDetKer : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3) ≃
          (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := BinaryGaloisField 3)).ker := by
        refine Equiv.ofBijective
          (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
            exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
        constructor
        · intro A B h
          apply Matrix.SpecialLinearGroup.toGL_injective
          exact congrArg Subtype.val h
        · intro A
          refine ⟨⟨(A : GL (Fin 2) (BinaryGaloisField 3)), ?_⟩, ?_⟩
          · have hmem := A.property
            change Matrix.GeneralLinearGroup.det (A : GL (Fin 2) (BinaryGaloisField 3)) = 1 at hmem
            exact Units.ext_iff.mp hmem
          · apply Subtype.ext
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            rfl
      exact Nat.card_congr slEquivDetKer
    _ = 504 := hker

private theorem psl28_sl2_binary3_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3)) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  rcases (Matrix.SpecialLinearGroup.mem_center_iff.mp hA) with ⟨r, hr, hscalar⟩
  have hr1 : r = 1 := by
    rcases (sq_eq_one_iff.mp hr) with hr' | hr'
    · exact hr'
    · simpa [CharTwo.neg_eq] using hr'
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hmat :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) (BinaryGaloisField 3) => M i j) hscalar
  simpa [hr1] using hmat.symm

private theorem psl28_binary3_card :
    Nat.card (PSL2BinaryMatrixGroup 3) = 504 := by
  classical
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3)) :=
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3))
  have hCcard : Nat.card C = 1 := by
    dsimp [C]
    rw [psl28_sl2_binary3_center_eq_bot]
    simp
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  dsimp [PSL2BinaryMatrixGroup, PSL2MatrixGroup, Matrix.ProjectiveSpecialLinearGroup] at hmul ⊢
  rw [psl28_sl2_binary3_card, hCcard, Nat.mul_one] at hmul
  exact hmul.symm


private theorem psl28_prime_dvd_504_ne_two {r : ℕ}
    (hr : Nat.Prime r) (hr_dvd : r ∣ 504) (hr_ne_two : r ≠ 2) :
    r = 3 ∨ r = 7 := by
  have hfac : 504 = 8 * 9 * 7 := by norm_num
  rw [hfac] at hr_dvd
  have hcases1 : r ∣ 8 * 9 ∨ r ∣ 7 := (Nat.Prime.dvd_mul hr).mp hr_dvd
  rcases hcases1 with h89 | h7
  · have hcases2 : r ∣ 8 ∨ r ∣ 9 := (Nat.Prime.dvd_mul hr).mp h89
    rcases hcases2 with h8 | h9
    · have h2 : r = 2 := by
        have h8' : r ∣ 2 ^ 3 := by simpa using h8
        have hp2 : Nat.Prime 2 := by decide
        exact Nat.prime_eq_prime_of_dvd_pow hr hp2 h8'
      exact (hr_ne_two h2).elim
    · have h3 : r = 3 := by
        have h9' : r ∣ 3 ^ 2 := by simpa using h9
        have hp3 : Nat.Prime 3 := by decide
        exact Nat.prime_eq_prime_of_dvd_pow hr hp3 h9'
      exact Or.inl h3
  · have h7eq : r = 7 := by
      have h7' : r ∣ 7 ^ 1 := by simpa using h7
      have hp7 : Nat.Prime 7 := by decide
      exact Nat.prime_eq_prime_of_dvd_pow hr hp7 h7'
    exact Or.inr h7eq

private instance psl28SLDistribMulAction (F : Type*) [Field F] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) (Fin 2 → F) :=
  DistribMulAction.compHom (Fin 2 → F) (Matrix.SpecialLinearGroup.toLin' :
    Matrix.SpecialLinearGroup (Fin 2) F →* (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))

private instance psl28SLSMulCommClass (F : Type*) [Field F] :
    SMulCommClass (Matrix.SpecialLinearGroup (Fin 2) F) F (Fin 2 → F) where
  smul_comm A c v := by
    change (Matrix.SpecialLinearGroup.toLin' A) (c • v) =
      c • (Matrix.SpecialLinearGroup.toLin' A) v
    exact (Matrix.SpecialLinearGroup.toLin' A).map_smul c v

private theorem psl28Line0_ne_zero (F : Type*) [Zero F] [One F] [NeZero (1 : F)] :
    (![1, 0] : Fin 2 → F) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

private theorem psl28Line1_ne_zero (F : Type*) [Zero F] [One F] [NeZero (1 : F)] :
    (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 1)

private theorem psl28Line01_ne_zero (F : Type*) [Zero F] [One F] [NeZero (1 : F)] :
    (![1, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

private theorem psl28_sl_center_mem_projective_perm_ker (F : Type*) [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    A ∈ (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) F)
      (ℙ F (Fin 2 → F))).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
      obtain ⟨r, _hrpow, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      rw [Equiv.Perm.coe_one, id_eq]
      change A • Projectivization.mk F v hv = Projectivization.mk F v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨r, ?_⟩
      change r • v = (Matrix.SpecialLinearGroup.toLin' A) v
      rw [Matrix.SpecialLinearGroup.toLin'_apply]
      funext i
      rw [← hscalar]
      simp [Matrix.toLin'_apply]

private theorem psl28_sl_mem_center_of_projective_trivial (F : Type*) [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hfix : ∀ x : ℙ F (Fin 2 → F), A • x = x) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hline0 := hfix (Projectivization.mk F ((![1, 0] : Fin 2 → F)) (psl28Line0_ne_zero F))
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hline0
  rcases hline0 with ⟨c0, hc0⟩
  have h10 : A 1 0 = 0 := by
    have h := congrFun hc0 1
    change (c0 • (![1, 0] : Fin 2 → F)) 1 =
      ((Matrix.SpecialLinearGroup.toLin' A) ((![1, 0] : Fin 2 → F))) 1 at h
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm
  have hline1 := hfix (Projectivization.mk F ((![0, 1] : Fin 2 → F)) (psl28Line1_ne_zero F))
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hline1
  rcases hline1 with ⟨c1, hc1⟩
  have h01 : A 0 1 = 0 := by
    have h := congrFun hc1 0
    change (c1 • (![0, 1] : Fin 2 → F)) 0 =
      ((Matrix.SpecialLinearGroup.toLin' A) ((![0, 1] : Fin 2 → F))) 0 at h
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm
  have hline01 := hfix (Projectivization.mk F ((![1, 1] : Fin 2 → F)) (psl28Line01_ne_zero F))
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hline01
  rcases hline01 with ⟨c01, hc01⟩
  have hc01_0 : c01 = A 0 0 := by
    have h := congrFun hc01 0
    change (c01 • (![1, 1] : Fin 2 → F)) 0 =
      ((Matrix.SpecialLinearGroup.toLin' A) ((![1, 1] : Fin 2 → F))) 0 at h
    simpa [h10, h01, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hc01_1 : c01 = A 1 1 := by
    have h := congrFun hc01 1
    change (c01 • (![1, 1] : Fin 2 → F)) 1 =
      ((Matrix.SpecialLinearGroup.toLin' A) ((![1, 1] : Fin 2 → F))) 1 at h
    simpa [h10, h01, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hdiag : A 0 0 = A 1 1 := hc01_0.symm.trans hc01_1
  have hscalar : Matrix.scalar (Fin 2) (A 0 0) =
      (A : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.scalar_apply]
    · simpa [Matrix.scalar_apply] using h01.symm
    · simpa [Matrix.scalar_apply] using h10.symm
    · simp [Matrix.scalar_apply, hdiag]
  rw [Subgroup.mem_center_iff]
  intro B
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hcomm := Matrix.scalar_commute (n := Fin 2) (A 0 0) (Commute.all (A 0 0))
    (B : Matrix (Fin 2) (Fin 2) F)
  have hmat :
      (B : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hscalar, ← hscalar]
    exact hcomm.symm.eq
  simpa [Matrix.SpecialLinearGroup.coe_mul] using congrFun (congrFun hmat i) j

private theorem psl28_projectiveLine_natCard :
    Nat.card (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)) = 9 := by
  classical
  have hfinrank :
      Module.finrank (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3) = 2 := by
    simp
  rw [Projectivization.card_of_finrank_two
    (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3) hfinrank]
  simp [BinaryGaloisField, GaloisField.card 2 3 (by norm_num)]

private theorem psl28_exists_mem_dvd_of_prime_dvd_multiset_lcm {p : ℕ}
    (hp : Nat.Prime p) {s : Multiset ℕ} (h : p ∣ s.lcm) :
    ∃ n ∈ s, p ∣ n := by
  induction s using Multiset.induction_on with
  | empty =>
      have h' : p ∣ 1 := by simpa [Multiset.lcm_zero] using h
      exact (hp.not_dvd_one h').elim
  | cons a s ih =>
      rw [Multiset.lcm_cons] at h
      rw [lcm_eq_nat_lcm] at h
      have hprod : p ∣ a * s.lcm := h.trans (Nat.lcm_dvd_mul a s.lcm)
      have hcases : p ∣ a ∨ p ∣ s.lcm := (Nat.Prime.dvd_mul hp).mp hprod
      rcases hcases with ha | hs
      · exact ⟨a, by simp, ha⟩
      · rcases ih hs with ⟨n, hn, hpn⟩
        exact ⟨n, by simp [hn], hpn⟩

private theorem psl28_ten_le_sum_cycleType_of_orderOf_eq_21
    {α : Type*} [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hσ : orderOf σ = 21) :
    10 ≤ σ.cycleType.sum := by
  have hlcm : σ.cycleType.lcm = 21 := by
    simpa [Equiv.Perm.lcm_cycleType] using hσ
  have h7dvd : 7 ∣ σ.cycleType.lcm := by rw [hlcm]; norm_num
  have h3dvd : 3 ∣ σ.cycleType.lcm := by rw [hlcm]; norm_num
  rcases psl28_exists_mem_dvd_of_prime_dvd_multiset_lcm
      (by decide : Nat.Prime 7) h7dvd with ⟨a, ha, h7a⟩
  rcases psl28_exists_mem_dvd_of_prime_dvd_multiset_lcm
      (by decide : Nat.Prime 3) h3dvd with ⟨b, hb, h3b⟩
  have hadvd : a ∣ 21 := by
    have := Equiv.Perm.dvd_of_mem_cycleType (σ := σ) ha
    simpa [hσ] using this
  have hbdvd : b ∣ 21 := by
    have := Equiv.Perm.dvd_of_mem_cycleType (σ := σ) hb
    simpa [hσ] using this
  have ha_cases : a = 7 ∨ a = 21 := by
    have ha_le : a ≤ 21 := Nat.le_of_dvd (by norm_num) hadvd
    have ha2 : 2 ≤ a := Equiv.Perm.two_le_of_mem_cycleType ha
    interval_cases a <;> simp at h7a hadvd ⊢
  have hb_cases : b = 3 ∨ b = 21 := by
    have hb_le : b ≤ 21 := Nat.le_of_dvd (by norm_num) hbdvd
    have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hb
    interval_cases b <;> simp at h3b hbdvd ⊢
  rcases ha_cases with rfl | rfl
  · rcases hb_cases with rfl | rfl
    · have h3erase : 3 ∈ σ.cycleType.erase 7 := by
        exact (Multiset.mem_erase_of_ne (by norm_num : 3 ≠ 7)).2 hb
      have hsum : 7 + (σ.cycleType.erase 7).sum = σ.cycleType.sum := by
        simpa using Multiset.sum_erase ha
      have h3le : 3 ≤ (σ.cycleType.erase 7).sum := Multiset.le_sum_of_mem h3erase
      omega
    · have h21le : 21 ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hb
      omega
  · have h21le : 21 ≤ σ.cycleType.sum := Multiset.le_sum_of_mem ha
    omega

private theorem psl28_no_orderOf_21_perm_of_card_eq_9
    {α : Type*} [DecidableEq α] [Fintype α]
    (hcard : Fintype.card α = 9) (σ : Equiv.Perm α) :
    orderOf σ ≠ 21 := by
  intro hσ
  have hsum10 : 10 ≤ σ.cycleType.sum :=
    psl28_ten_le_sum_cycleType_of_orderOf_eq_21 hσ
  have hsumle : σ.cycleType.sum ≤ 9 := by
    simpa [hcard] using Equiv.Perm.sum_cycleType_le σ
  omega

private theorem psl28_binary3_no_orderOf_21 (x : PSL2BinaryMatrixGroup 3) :
    orderOf x ≠ 21 := by
  classical
  letI : Fintype (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)) :=
    Fintype.ofFinite _
  let φ : PSL2BinaryMatrixGroup 3 →* Equiv.Perm (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)) :=
    QuotientGroup.lift _
      (MulAction.toPermHom
        (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3))
        (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)))
      (by
        intro A hA
        exact psl28_sl_center_mem_projective_perm_ker (BinaryGaloisField 3) A hA)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    constructor
    · intro hx
      rcases QuotientGroup.mk'_surjective
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3))) x with ⟨A, rfl⟩
      rw [MonoidHom.mem_ker] at hx
      have hperm :
          (MulAction.toPermHom
            (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3))
            (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3))) A = 1 := by
        simpa [φ] using hx
      have hfix : ∀ line : ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3), A • line = line := by
        intro line
        have hline := congrArg
          (fun f : Equiv.Perm (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)) => f line)
          hperm
        simpa using hline
      have hcenter := psl28_sl_mem_center_of_projective_trivial (BinaryGaloisField 3) A hfix
      rw [Subgroup.mem_bot]
      simpa [PSL2MatrixGroup, Matrix.ProjectiveSpecialLinearGroup] using
        (QuotientGroup.eq_one_iff A).mpr hcenter
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      simp
  have hcard :
      Fintype.card (ℙ (BinaryGaloisField 3) (Fin 2 → BinaryGaloisField 3)) = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact psl28_projectiveLine_natCard
  intro hx
  have hperm : orderOf (φ x) = 21 := by
    simpa [hx] using orderOf_injective φ hφinj x
  exact psl28_no_orderOf_21_perm_of_card_eq_9 hcard (φ x) hperm

private theorem psl28_binary3_orderSeven_centralizer_no_order_three
    {y : PSL2BinaryMatrixGroup 3} (hy : orderOf y = 7) :
    ¬ ∃ z : PSL2BinaryMatrixGroup 3,
      z ∈ Subgroup.centralizer ({y} : Set (PSL2BinaryMatrixGroup 3)) ∧
        orderOf z = 3 := by
  rintro ⟨z, hzcent, hzOrder⟩
  have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hzcent
  have hyzComm : Commute y z := hzy.symm
  have hcop : (orderOf y).Coprime (orderOf z) := by
    rw [hy, hzOrder]
    decide
  have hyzOrder : orderOf (y * z) = 21 := by
    rw [hyzComm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hy, hzOrder]
  exact psl28_binary3_no_orderOf_21 (y * z) hyzOrder


private theorem sl2_orderThree_no_eigenvector
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hFcard : Nat.card F = 8)
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hAorder : orderOf A = 3) :
    ∀ (lambda : F) (v : Fin 2 -> F), v ≠ 0 ->
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ lambda • v := by
  intro lambda v hv hAv
  have hA3sub : A ^ 3 = 1 := by
    rw [← hAorder]
    exact pow_orderOf_eq_one A
  have hA3 : (A : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 :=
    congrArg Subtype.val hA3sub
  have hA2v : ((A : Matrix (Fin 2) (Fin 2) F) ^ 2) *ᵥ v = lambda ^ 2 • v := by
    calc
      ((A : Matrix (Fin 2) (Fin 2) F) ^ 2) *ᵥ v =
          (A : Matrix (Fin 2) (Fin 2) F) *ᵥ
            ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
              rw [pow_two, Matrix.mulVec_mulVec]
      _ = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (lambda • v) := by rw [hAv]
      _ = lambda • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
        rw [Matrix.mulVec_smul]
      _ = lambda • (lambda • v) := by rw [hAv]
      _ = lambda ^ 2 • v := by simp [pow_two, smul_smul]
  have hA3v : ((A : Matrix (Fin 2) (Fin 2) F) ^ 3) *ᵥ v = lambda ^ 3 • v := by
    calc
      ((A : Matrix (Fin 2) (Fin 2) F) ^ 3) *ᵥ v =
          (A : Matrix (Fin 2) (Fin 2) F) *ᵥ
            (((A : Matrix (Fin 2) (Fin 2) F) ^ 2) *ᵥ v) := by
              rw [show (A : Matrix (Fin 2) (Fin 2) F) ^ 3 =
                (A : Matrix (Fin 2) (Fin 2) F) *
                  (A : Matrix (Fin 2) (Fin 2) F) ^ 2 by
                    rw [pow_succ']]
              rw [Matrix.mulVec_mulVec]
      _ = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (lambda ^ 2 • v) := by rw [hA2v]
      _ = lambda ^ 2 • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
        rw [Matrix.mulVec_smul]
      _ = lambda ^ 2 • (lambda • v) := by rw [hAv]
      _ = lambda ^ 3 • v := by simp [pow_succ, smul_smul]
  have hlambda3 : lambda ^ 3 = 1 := by
    apply smul_left_injective F hv
    calc
      lambda ^ 3 • v = ((A : Matrix (Fin 2) (Fin 2) F) ^ 3) *ᵥ v := hA3v.symm
      _ = (1 : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by rw [hA3]
      _ = (1 : F) • v := by simp
  have hlambda0 : lambda ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hlambda3
    exact zero_ne_one hlambda3
  let u : Fˣ := Units.mk0 lambda hlambda0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    exact hlambda3
  have hord3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hUcard : Nat.card Fˣ = 7 := by
    rw [Nat.card_units, hFcard]
  have hord7 : orderOf u ∣ 7 := by
    rw [← hUcard]
    exact orderOf_dvd_natCard u
  have hord1 : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 7) hord3 hord7
  have hu1 : u = 1 := orderOf_eq_one_iff.mp hord1
  have hlambda1 : lambda = 1 := congrArg Units.val hu1
  rw [hlambda1] at hAv
  let M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) - 1
  have hMv : M *ᵥ v = 0 := by
    simp [M, Matrix.sub_mulVec, hAv]
  have hker : ∃ w ≠ 0, M *ᵥ w = 0 := ⟨v, hv, hMv⟩
  have hMdet : M.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp hker
  have htrace : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = 0 := by
    dsimp [M] at hMdet
    rw [Matrix.det_fin_two] at hMdet
    simp [Matrix.sub_apply] at hMdet
    have hdetA : Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 := A.property
    rw [Matrix.det_fin_two] at hdetA
    change
      (((A : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) *
          ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) -
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
          (A : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 at hMdet
    change
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
          (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
          (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 at hdetA
    rw [Matrix.trace_fin_two]
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hsum :
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
          (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 := by
      linear_combination hdetA - hMdet
    simpa [htwo] using hsum
  have hA2 : (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1 := by
    have hdetA : Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 := A.property
    have hCH := Matrix.aeval_self_charpoly (A : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.charpoly_fin_two] at hCH
    simp [htrace, hdetA] at hCH
    have hneg_one_scalar : -(1 : F) = 1 := by
      apply neg_eq_iff_add_eq_zero.mpr
      calc
        (1 : F) + 1 = 2 := by norm_num
        _ = 0 := CharP.cast_eq_zero F 2
    have hneg_one_matrix :
        -(1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
      classical
      ext i j
      change -((1 : Matrix (Fin 2) (Fin 2) F) i j) =
        (1 : Matrix (Fin 2) (Fin 2) F) i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hneg_one_scalar]
    calc
      (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1 :=
        eq_neg_of_add_eq_zero_left hCH
      _ = 1 := hneg_one_matrix
  have hdvd2 : orderOf A ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    exact hA2
  rw [hAorder] at hdvd2
  norm_num at hdvd2


private theorem sl2_commuting_matrix_eq_linear
    {F : Type*} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hnoeig : ∀ (lambda : F) (v : Fin 2 -> F), v ≠ 0 ->
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ lambda • v)
    (B : Matrix (Fin 2) (Fin 2) F)
    (hcomm : Commute (A : Matrix (Fin 2) (Fin 2) F) B) :
    ∃ r u : F, B =
      r • (1 : Matrix (Fin 2) (Fin 2) F) +
        u • (A : Matrix (Fin 2) (Fin 2) F) := by
  have hbc :
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∨
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hnoeig ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ![1, 0] (by
      intro hv
      exact one_ne_zero (congrFun hv 0))
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h.1, h.2]
  have h00 := congrFun (congrFun hcomm.eq 0) 0
  have h01 := congrFun (congrFun hcomm.eq 0) 1
  have h10 := congrFun (congrFun hcomm.eq 1) 0
  have h11 := congrFun (congrFun hcomm.eq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rcases hbc with hb | hc
  · refine
      ⟨B 0 0 - (B 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 0 1) *
          (A : Matrix (Fin 2) (Fin 2) F) 0 0,
        B 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp [hb]
    · simp
      field_simp [hb]
      linear_combination h00
    · simp
      field_simp [hb]
      linear_combination h01
  · refine
      ⟨B 0 0 - (B 1 0 / (A : Matrix (Fin 2) (Fin 2) F) 1 0) *
          (A : Matrix (Fin 2) (Fin 2) F) 0 0,
        B 1 0 / (A : Matrix (Fin 2) (Fin 2) F) 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
      field_simp [hc]
      linear_combination h11
    · simp [hc]
    · simp
      field_simp [hc]
      linear_combination -h10

private theorem sl2_matrix_centralizer_mul_comm
    {F : Type*} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hnoeig : ∀ (lambda : F) (v : Fin 2 -> F), v ≠ 0 ->
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ lambda • v)
    (B C : Subring.centralizer
      ({(A : Matrix (Fin 2) (Fin 2) F)} : Set
        (Matrix (Fin 2) (Fin 2) F))) :
    B * C = C * B := by
  have hBcomm :
      Commute (A : Matrix (Fin 2) (Fin 2) F)
        (B : Matrix (Fin 2) (Fin 2) F) :=
    B.property (A : Matrix (Fin 2) (Fin 2) F) (by simp)
  have hCcomm :
      Commute (A : Matrix (Fin 2) (Fin 2) F)
        (C : Matrix (Fin 2) (Fin 2) F) :=
    C.property (A : Matrix (Fin 2) (Fin 2) F) (by simp)
  rcases sl2_commuting_matrix_eq_linear A hnoeig B hBcomm with ⟨r, u, hB⟩
  rcases sl2_commuting_matrix_eq_linear A hnoeig C hCcomm with ⟨q, v, hC⟩
  apply Subtype.ext
  change
    (B : Matrix (Fin 2) (Fin 2) F) *
        (C : Matrix (Fin 2) (Fin 2) F) =
      (C : Matrix (Fin 2) (Fin 2) F) *
        (B : Matrix (Fin 2) (Fin 2) F)
  rw [hB, hC]
  have hrq :
      Commute
        (r • (1 : Matrix (Fin 2) (Fin 2) F))
        (q • (1 : Matrix (Fin 2) (Fin 2) F)) :=
    (Commute.one_left (1 : Matrix (Fin 2) (Fin 2) F)).smul_left r |>.smul_right q
  have hrv :
      Commute
        (r • (1 : Matrix (Fin 2) (Fin 2) F))
        (v • (A : Matrix (Fin 2) (Fin 2) F)) :=
    (Commute.one_left (A : Matrix (Fin 2) (Fin 2) F)).smul_left r |>.smul_right v
  have huq :
      Commute
        (u • (A : Matrix (Fin 2) (Fin 2) F))
        (q • (1 : Matrix (Fin 2) (Fin 2) F)) :=
    (Commute.one_right (A : Matrix (Fin 2) (Fin 2) F)).smul_left u |>.smul_right q
  have huv :
      Commute
        (u • (A : Matrix (Fin 2) (Fin 2) F))
        (v • (A : Matrix (Fin 2) (Fin 2) F)) :=
    (Commute.refl (A : Matrix (Fin 2) (Fin 2) F)).smul_left u |>.smul_right v
  exact ((hrq.add_right hrv).add_left (huq.add_right huv)).eq

private theorem sl2_matrix_centralizer_eq_zero_or_eq_zero_of_mul_eq_zero
    {F : Type*} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hnoeig : ∀ (lambda : F) (v : Fin 2 -> F), v ≠ 0 ->
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ lambda • v)
    (B C : Subring.centralizer
      ({(A : Matrix (Fin 2) (Fin 2) F)} : Set
        (Matrix (Fin 2) (Fin 2) F)))
    (hBC : B * C = 0) :
    B = 0 ∨ C = 0 := by
  by_cases hBzero : B = 0
  · exact Or.inl hBzero
  right
  apply Subtype.ext
  change (C : Matrix (Fin 2) (Fin 2) F) = 0
  have hBne :
      (B : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h
    apply hBzero
    apply Subtype.ext
    exact h
  have hBcomm :
      Commute (A : Matrix (Fin 2) (Fin 2) F)
        (B : Matrix (Fin 2) (Fin 2) F) :=
    B.property (A : Matrix (Fin 2) (Fin 2) F) (by simp)
  rcases sl2_commuting_matrix_eq_linear A hnoeig B hBcomm with
    ⟨r, u, hBshape⟩
  have hdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro hdet
    have hker :
        ∃ v ≠ 0, (B : Matrix (Fin 2) (Fin 2) F) *ᵥ v = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rcases hker with ⟨v, hv, hBv⟩
    have hlin :
        r • v + u •
          ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = 0 := by
      simpa [hBshape, Matrix.add_mulVec, Matrix.smul_mulVec] using hBv
    by_cases hu : u = 0
    · have hrv : r • v = 0 := by simpa [hu] using hlin
      have hr : r = 0 := (smul_eq_zero.mp hrv).resolve_right hv
      apply hBne
      rw [hBshape, hu, hr]
      simp
    · apply hnoeig (-r / u) v hv
      have huAv :
          u • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = -(r • v) :=
        eq_neg_of_add_eq_zero_right hlin
      calc
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
            u⁻¹ • (u • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by
              simp [smul_smul, hu]
        _ = u⁻¹ • (-(r • v)) := by rw [huAv]
        _ = (-r / u) • v := by
          module
  have hunit : IsUnit (Matrix.det (B : Matrix (Fin 2) (Fin 2) F)) :=
    (isUnit_iff_ne_zero).2 hdet
  have hBCmat :
      (B : Matrix (Fin 2) (Fin 2) F) *
          (C : Matrix (Fin 2) (Fin 2) F) = 0 :=
    congrArg Subtype.val hBC
  calc
    (C : Matrix (Fin 2) (Fin 2) F) =
        (B : Matrix (Fin 2) (Fin 2) F)⁻¹ *
          ((B : Matrix (Fin 2) (Fin 2) F) *
            (C : Matrix (Fin 2) (Fin 2) F)) :=
      (Matrix.nonsing_inv_mul_cancel_left
        (B : Matrix (Fin 2) (Fin 2) F)
        (C : Matrix (Fin 2) (Fin 2) F) hunit).symm
    _ = 0 := by rw [hBCmat]; simp

private theorem sl2_orderThree_centralizer_isCyclic
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hFcard : Nat.card F = 8)
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hAorder : orderOf A = 3) :
    IsCyclic (Subgroup.centralizer
      ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  let C : Subring (Matrix (Fin 2) (Fin 2) F) :=
    Subring.centralizer
      ({(A : Matrix (Fin 2) (Fin 2) F)} : Set
        (Matrix (Fin 2) (Fin 2) F))
  have hnoeig := sl2_orderThree_no_eigenvector hFcard A hAorder
  letI : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun B D =>
        sl2_matrix_centralizer_mul_comm A hnoeig B D }
  letI : IsDomain C := {
    toIsCancelMulZero := by
      refine isCancelMulZero_iff_noZeroDivisors.mpr ?_
      rw [noZeroDivisors_iff]
      intro B D hBD
      exact
        sl2_matrix_centralizer_eq_zero_or_eq_zero_of_mul_eq_zero
          A hnoeig B D hBD
    toNontrivial := by infer_instance
  }
  let f :
      Subgroup.centralizer
          ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) →* C :=
    { toFun := fun B => ⟨(B.1 : Matrix (Fin 2) (Fin 2) F), by
        intro X hX
        have hXA : X = (A : Matrix (Fin 2) (Fin 2) F) := by simpa using hX
        subst X
        have hcomm :=
          congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp B.property).symm
        simpa using hcomm⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro B D
        apply Subtype.ext
        simp }
  apply isCyclic_of_injective_ringHom f
  intro B D h
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun (congrArg Subtype.val h) i) j


private noncomputable def psl28_binary3_equiv_sl2 :
    PSL2BinaryMatrixGroup 3 ≃*
      Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3) := by
  dsimp [PSL2BinaryMatrixGroup, PSL2MatrixGroup,
    Matrix.ProjectiveSpecialLinearGroup]
  exact
    (QuotientGroup.quotientMulEquivOfEq
      psl28_sl2_binary3_center_eq_bot).trans
      (QuotientGroup.quotientBot
      (G := Matrix.SpecialLinearGroup
          (Fin 2) (BinaryGaloisField 3)))

/-- The projective special linear group `PSL(2,8)` has trivial center. -/
public theorem psl28_binary3_center_eq_bot :
    Subgroup.center (PSL2BinaryMatrixGroup 3) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  calc
    Nat.card (Subgroup.center (PSL2BinaryMatrixGroup 3)) =
        Nat.card (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3))) :=
      Nat.card_congr
        (Subgroup.centerCongr psl28_binary3_equiv_sl2).toEquiv
    _ = 1 := by rw [psl28_sl2_binary3_center_eq_bot]; simp


private def centralizerSingletonMulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃*
      Subgroup.centralizer ({e x} : Set H) where
  toFun y := ⟨e y.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy :=
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp y.property)
    simpa using hy⟩
  invFun z := ⟨e.symm z.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz :=
      congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp z.property)
    simpa using hz⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  map_mul' y z := by
    apply Subtype.ext
    simp

private theorem sl2_orderThree_centralizer_order_ne_two
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hFcard : Nat.card F = 8)
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hAorder : orderOf A = 3)
    (B : Subgroup.centralizer
      ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    orderOf B ≠ 2 := by
  intro hBorder
  have hB2sub : B ^ 2 = 1 := by
    simpa only [hBorder] using pow_orderOf_eq_one B
  have hB2 :
      (B.1 : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1 :=
    congrArg Subtype.val (congrArg Subtype.val hB2sub)
  have hnoeig := sl2_orderThree_no_eigenvector hFcard A hAorder
  let C : Subring (Matrix (Fin 2) (Fin 2) F) :=
    Subring.centralizer
      ({(A : Matrix (Fin 2) (Fin 2) F)} : Set
        (Matrix (Fin 2) (Fin 2) F))
  have hAB :
      Commute (A : Matrix (Fin 2) (Fin 2) F)
        (B.1 : Matrix (Fin 2) (Fin 2) F) := by
    have h :=
      congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp B.property).symm
    rw [commute_iff_eq]
    exact h
  let X : C :=
    ⟨(B.1 : Matrix (Fin 2) (Fin 2) F) - 1, by
      intro Y hY
      have hYA : Y = (A : Matrix (Fin 2) (Fin 2) F) := by simpa using hY
      subst Y
      exact
        (hAB.sub_right (Commute.one_right
          (A : Matrix (Fin 2) (Fin 2) F))).eq⟩
  have hXX : X * X = 0 := by
    apply Subtype.ext
    change
      ((B.1 : Matrix (Fin 2) (Fin 2) F) - 1) *
          ((B.1 : Matrix (Fin 2) (Fin 2) F) - 1) = 0
    rw [sub_mul, mul_sub, mul_one, one_mul]
    change
      (B.1 : Matrix (Fin 2) (Fin 2) F) *
          (B.1 : Matrix (Fin 2) (Fin 2) F) -
        (B.1 : Matrix (Fin 2) (Fin 2) F) -
        ((B.1 : Matrix (Fin 2) (Fin 2) F) - 1) = 0
    rw [show
      (B.1 : Matrix (Fin 2) (Fin 2) F) *
          (B.1 : Matrix (Fin 2) (Fin 2) F) =
        (B.1 : Matrix (Fin 2) (Fin 2) F) ^ 2 by rw [pow_two], hB2]
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    ext i j
    simp only [Matrix.sub_apply, Matrix.zero_apply]
    rw [show
      (1 : Matrix (Fin 2) (Fin 2) F) i j -
          (B.1 : Matrix (Fin 2) (Fin 2) F) i j -
          ((B.1 : Matrix (Fin 2) (Fin 2) F) i j -
            (1 : Matrix (Fin 2) (Fin 2) F) i j) =
        (2 : F) *
          ((1 : Matrix (Fin 2) (Fin 2) F) i j -
            (B.1 : Matrix (Fin 2) (Fin 2) F) i j) by ring,
      htwo, zero_mul]
  have hXzero : X = 0 := by
    rcases
        sl2_matrix_centralizer_eq_zero_or_eq_zero_of_mul_eq_zero
          A hnoeig X X hXX with h | h
    · exact h
    · exact h
  have hBmat :
      (B.1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h := congrArg Subtype.val hXzero
    change (B.1 : Matrix (Fin 2) (Fin 2) F) - 1 = 0 at h
    exact sub_eq_zero.mp h
  have hBone : B = 1 := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun hBmat i) j
  rw [hBone] at hBorder
  norm_num at hBorder

private theorem psl28_binary3_orderThree_centralizer_isCyclic
    (x : PSL2BinaryMatrixGroup 3) (hx : orderOf x = 3) :
    IsCyclic (Subgroup.centralizer
      ({x} : Set (PSL2BinaryMatrixGroup 3))) := by
  let e := psl28_binary3_equiv_sl2
  let ce := centralizerSingletonMulEquiv e x
  apply ce.isCyclic.mpr
  apply sl2_orderThree_centralizer_isCyclic
    (F := BinaryGaloisField 3)
  · simpa [BinaryGaloisField] using
      (GaloisField.card 2 3 (by norm_num))
  · simpa [e] using hx

private theorem psl28_binary3_orderThree_centralizer_card
    (x : PSL2BinaryMatrixGroup 3) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer
      ({x} : Set (PSL2BinaryMatrixGroup 3))) = 9 := by
  let C : Subgroup (PSL2BinaryMatrixGroup 3) :=
    Subgroup.centralizer ({x} : Set (PSL2BinaryMatrixGroup 3))
  have hCcyc : IsCyclic C :=
    psl28_binary3_orderThree_centralizer_isCyclic x hx
  letI : IsCyclic C := hCcyc
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨P, hXP⟩ := hX3.exists_le_sylow
  have hfac : Nat.factorization 504 3 = 2 := by
    rw [Nat.factorization_def 504 Nat.prime_three]
    rw [show 504 = 3 ^ 2 * 56 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hPcard : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity, psl28_binary3_card, hfac]
    norm_num

  have hxP : x ∈ (P : Subgroup (PSL2BinaryMatrixGroup 3)) :=
    hXP (Subgroup.mem_zpowers x)
  have hP_le_C : (P : Subgroup (PSL2BinaryMatrixGroup 3)) ≤ C := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm :=
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq
        (p := 3) (G := P) (by simpa [pow_two] using hPcard)).is_comm.comm
        ⟨y, hy⟩ ⟨x, hxP⟩
    exact congrArg Subtype.val hcomm
  have h9dvd : 9 ∣ Nat.card C := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hP_le_C
  have hCdvd : Nat.card C ∣ 504 := by
    simpa [psl28_binary3_card] using C.card_subgroup_dvd_card
  have hnot2 : ¬ 2 ∣ Nat.card C := by
    intro h2
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card' (G := C) 2 h2
    let e := psl28_binary3_equiv_sl2
    let ce := centralizerSingletonMulEquiv e x
    have hmaporder : orderOf (ce y) = 2 := by simpa using hy
    exact
      sl2_orderThree_centralizer_order_ne_two
        (F := BinaryGaloisField 3)
        (by
          simpa [BinaryGaloisField] using
            (GaloisField.card 2 3 (by norm_num)))
        (e x) (by simpa [e] using hx) (ce y) hmaporder
  have hnot7 : ¬ 7 ∣ Nat.card C := by
    letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    intro h7
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card' (G := C) 7 h7
    apply
      psl28_binary3_orderSeven_centralizer_no_order_three
        (y := (y : PSL2BinaryMatrixGroup 3)) (by simpa using hy)
    refine ⟨x, ?_, hx⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp y.property).symm
  have hprime :
      ∀ {r : ℕ}, Nat.Prime r → r ∣ Nat.card C → r = 3 := by
    intro r hr hrd
    have hr504 : r ∣ 504 := hrd.trans hCdvd
    have hrne2 : r ≠ 2 := by
      intro hre
      apply hnot2
      simpa [hre] using hrd
    rcases psl28_prime_dvd_504_ne_two hr hr504 hrne2 with hr3 | hr7
    · exact hr3
    · exfalso
      apply hnot7
      simpa [hr7] using hrd
  have hCpow :
      Nat.card C = 3 ^ (Nat.card C).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime
  let k := (Nat.card C).primeFactorsList.length
  have hk_le : k ≤ 2 := by
    have hf3 :
        Nat.factorization (Nat.card C) 3 ≤ Nat.factorization 504 3 :=
      Nat.factorization_le_factorization_of_dvd_right
        (a := 3) hCdvd Nat.card_pos.ne' (by norm_num : (504 : ℕ) ≠ 0)
    rw [hCpow] at hf3
    simpa [Nat.Prime.factorization Nat.prime_three, hfac, k] using hf3
  have hk_ge : 2 ≤ k := by
    have hfac9 : Nat.factorization 9 3 = 2 := by
      rw [show 9 = 3 ^ 2 by norm_num,
        Nat.Prime.factorization_pow Nat.prime_three]
      simp
    have hf3 : Nat.factorization 9 3 ≤ Nat.factorization (Nat.card C) 3 :=
      Nat.factorization_le_factorization_of_dvd_right
        (a := 3) h9dvd (by norm_num : (9 : ℕ) ≠ 0) Nat.card_pos.ne'
    rw [hCpow] at hf3
    simpa [Nat.Prime.factorization Nat.prime_three, hfac9, k] using hf3
  have hk : k = 2 := by omega
  rw [hCpow]
  simp [k, hk]


/-- In `PSL(2,8)`, the centralizer of an element of order three is the
nonsplit cyclic torus of order nine. -/
public theorem psl28_orderThree_centralizer_cyclic_order_nine
    (x : PSL2BinaryMatrixGroup 3) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer
      ({x} : Set (PSL2BinaryMatrixGroup 3))) = 9 ∧
      IsCyclic (Subgroup.centralizer
        ({x} : Set (PSL2BinaryMatrixGroup 3))) :=
  ⟨psl28_binary3_orderThree_centralizer_card x hx,
    psl28_binary3_orderThree_centralizer_isCyclic x hx⟩

end

end MatrixGroups
end CFSG.BenderSuzuki
