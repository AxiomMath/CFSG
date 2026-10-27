module

public import CFSG.RankThree.PartTwo.Census.Exceptional.ReeCarrier
public import CFSG.Adapters.SpecialLinearPerfect
import all TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open TauCeti TauCeti.G2ShortRoot CFSG.RankThree.CentralCover
open scoped MatrixGroups commutatorElement

section Ree

theorem endPow_succ_apply {M : Type*} [Monoid M] (f : Monoid.End M) (n : ℕ) (x : M) :
    (f ^ (n + 1)) x = f ((f ^ n) x) := by
  rw [pow_succ']
  rfl

variable (d : ReeG2LieIndex)

noncomputable abbrev reeTau : Monoid.End d.AmbientGroup := d.halfFrobenius

noncomputable abbrev reeFr : SL(2, d.1.Closure) →* SL(2, d.1.Closure) :=
  Matrix.SpecialLinearGroup.map (frobenius d.1.Closure 3)

theorem halfFrobenius_reePhi1 (A : SL(2, d.1.Closure)) :
    reeTau d (reePhi1 d.1.Closure A) = reePhi2 d.1.Closure (reeFr d A) := by
  change PrimeField.specialIsogeny d.1.Closure
      (reeNb d.1.Closure * phia d.1.Closure A * (reeNb d.1.Closure)⁻¹) =
    reeNa d.1.Closure * phib d.1.Closure (reeFr d A) * (reeNa d.1.Closure)⁻¹
  rw [map_mul, map_mul, map_inv, specialIsogeny_phia, reeNb, specialIsogeny_phib, reeNa]

theorem halfFrobenius_reePhi2 (A : SL(2, d.1.Closure)) :
    reeTau d (reePhi2 d.1.Closure A) = reePhi1 d.1.Closure A := by
  change PrimeField.specialIsogeny d.1.Closure
      (reeNa d.1.Closure * phib d.1.Closure A * (reeNa d.1.Closure)⁻¹) =
    reeNb d.1.Closure * phia d.1.Closure A * (reeNb d.1.Closure)⁻¹
  rw [map_mul, map_mul, map_inv, specialIsogeny_phib, reeNa, specialIsogeny_phia,
    map_frobenius_sl2Weyl, reeNb]

theorem halfFrobenius_pow_even (k : ℕ) (A : SL(2, d.1.Closure)) :
    (reeTau d ^ (2 * k)) (reePhi1 d.1.Closure A) =
        reePhi1 d.1.Closure ((reeFr d)^[k] A) ∧
      (reeTau d ^ (2 * k)) (reePhi2 d.1.Closure A) =
        reePhi2 d.1.Closure ((reeFr d)^[k] A) := by
  induction k generalizing A with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, endPow_succ_apply, endPow_succ_apply,
      endPow_succ_apply, endPow_succ_apply, (ih A).1, (ih A).2, halfFrobenius_reePhi1,
      halfFrobenius_reePhi2, halfFrobenius_reePhi2, halfFrobenius_reePhi1,
      Function.iterate_succ_apply']
    exact ⟨rfl, rfl⟩

variable {d} {m : ℕ} (hd : d.1.fieldExponent = 2 * m + 1)
include hd

theorem steinberg_reePhi1 (A : SL(2, d.1.Closure)) :
    d.steinberg (reePhi1 d.1.Closure A) = reePhi2 d.1.Closure ((reeFr d)^[m + 1] A) := by
  change (reeTau d ^ d.1.fieldExponent) (reePhi1 d.1.Closure A) = _
  rw [hd, endPow_succ_apply, (halfFrobenius_pow_even d m A).1,
    halfFrobenius_reePhi1, Function.iterate_succ_apply']

theorem steinberg_reePhi2 (A : SL(2, d.1.Closure)) :
    d.steinberg (reePhi2 d.1.Closure A) = reePhi1 d.1.Closure ((reeFr d)^[m] A) := by
  change (reeTau d ^ d.1.fieldExponent) (reePhi2 d.1.Closure A) = _
  rw [hd, endPow_succ_apply, (halfFrobenius_pow_even d m A).2,
    halfFrobenius_reePhi2]

omit hd in
theorem steinberg_of_halfFrobenius {g : d.AmbientGroup} (hg : reeTau d g = g) :
    d.steinberg g = g := by
  change (reeTau d ^ d.1.fieldExponent) g = g
  induction d.1.fieldExponent with
  | zero => rfl
  | succ n ih => rw [endPow_succ_apply, ih, hg]

end Ree

section ReeWitness

variable (d : ReeG2LieIndex)

theorem reeFr_iterate_apply (n : ℕ) (B : SL(2, d.1.Closure)) (i j : Fin 2) :
    (((reeFr d)^[n] B : SL(2, d.1.Closure)) : Matrix (Fin 2) (Fin 2) d.1.Closure) i j =
      (B : Matrix (Fin 2) (Fin 2) d.1.Closure) i j ^ 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, ih, frobenius_def, ← pow_mul, pow_succ]

noncomputable abbrev reeIncl : SL(2, d.1.fixedField) →* SL(2, d.1.Closure) :=
  Matrix.SpecialLinearGroup.map d.1.fixedField.subtype

variable {d} {m : ℕ} (hd : d.1.fieldExponent = 2 * m + 1)

include hd in
theorem reeFr_iterate_incl (A : SL(2, d.1.fixedField)) :
    (reeFr d)^[2 * m + 1] (reeIncl d A) = reeIncl d A := by
  ext i j
  rw [reeFr_iterate_apply, ← hd]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have h := ValidLieTypeIndex.mem_fixedField.1
    ((A : Matrix (Fin 2) (Fin 2) d.1.fixedField) i j).2
  rwa [ReeG2LieIndex.fieldOrder_eq_three_pow] at h

variable (d m)

@[expose] noncomputable def reePsi : SL(2, d.1.fixedField) →* d.AmbientGroup where
  toFun A := reePhi1 d.1.Closure (reeIncl d A) *
    reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A))
  map_one' := by simp [iterate_map_one]
  map_mul' A B := by
    simp only [map_mul, iterate_map_mul]
    have h := reePhi_commute d.1.Closure (reeIncl d B) ((reeFr d)^[m + 1] (reeIncl d A))
    calc reePhi1 d.1.Closure (reeIncl d A) * reePhi1 d.1.Closure (reeIncl d B) *
          (reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A)) *
            reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d B)))
        = reePhi1 d.1.Closure (reeIncl d A) *
            (reePhi1 d.1.Closure (reeIncl d B) *
              reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A))) *
            reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d B)) := by
          simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc]

variable {d m}

include hd in
theorem steinberg_reePsi (A : SL(2, d.1.fixedField)) :
    d.steinberg (reePsi d m A) = reePsi d m A := by
  change d.steinberg (reePhi1 d.1.Closure (reeIncl d A) *
    reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A))) = _
  rw [map_mul, steinberg_reePhi1 hd, steinberg_reePhi2 hd, ← Function.iterate_add_apply,
    show m + (m + 1) = 2 * m + 1 by ring, reeFr_iterate_incl hd]
  exact (reePhi_commute _ _ _).symm

include hd in
theorem steinberg_reeT : d.steinberg (reeT d.1.Closure) = reeT d.1.Closure := by
  have h0 : reeFr d (-1) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.map_apply_coe]
  have h1 : ∀ n, (reeFr d)^[n] (-1) = -1 := fun n => Function.iterate_fixed h0 n
  rw [reeT, steinberg_reePhi1 hd, h1, reePhi1_neg_one]

omit hd in
theorem steinberg_reeU : d.steinberg (reeU d.1.Closure) = reeU d.1.Closure :=
  steinberg_of_halfFrobenius (specialIsogeny_reeU d.1.Closure)

omit hd in
theorem steinberg_reeV : d.steinberg (reeV d.1.Closure) = reeV d.1.Closure :=
  steinberg_of_halfFrobenius (specialIsogeny_reeV d.1.Closure)

end ReeWitness

section ReeRank

theorem reeMap_injective {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro A B h
  ext a b
  have := congrArg (fun M : SL(2, K') => (M : Matrix (Fin 2) (Fin 2) K') a b) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact f.injective this

open CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {d : ReeG2LieIndex} {m : ℕ}

theorem mem_center_of_reePsi_eq_one {A : SL(2, d.1.fixedField)} (hA : reePsi d m A = 1) :
    A ∈ Subgroup.center (SL(2, d.1.fixedField)) := by
  set B := reeIncl d A
  set B' := (reeFr d)^[m + 1] B
  have h1 : reePhi1 d.1.Closure B = (reePhi2 d.1.Closure B')⁻¹ := eq_inv_of_mul_eq_one_left hA
  have hB : ∀ C : SL(2, d.1.Closure), C * B = B * C := by
    intro C
    apply reePhi1_injective d.1.Closure
    rw [map_mul, map_mul, h1]
    exact ((Commute.inv_right (reePhi_commute d.1.Closure C B'))).eq
  rw [Subgroup.mem_center_iff]
  intro A'
  apply reeMap_injective d.1.fixedField.subtype
  rw [map_mul, map_mul]
  exact hB _

theorem eq_zero_of_reePsi_commute (c : d.1.fixedField)
    (h : reePsi d m (sl2Upper c) * reePsi d m (CFSG.LocalAnalysis.ComponentInitial.sl2Lower _ 1) =
      reePsi d m (CFSG.LocalAnalysis.ComponentInitial.sl2Lower _ 1) * reePsi d m (sl2Upper c)) :
    c = 0 := by
  set U := sl2Upper c
  set V := CFSG.LocalAnalysis.ComponentInitial.sl2Lower d.1.fixedField 1
  have h1 : reePsi d m (U * V * U⁻¹ * V⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    (mem_center_of_reePsi_eq_one h1)
  have h10 := congrFun (congrFun hr 1) 0
  simp [U, V, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, coe_sl2Upper] at h10
  exact h10.symm

variable (d) in
@[expose] noncomputable def reeUH : ↥(fixedSubgroup d.steinberg) :=
  ⟨reeU d.1.Closure, steinberg_reeU⟩

variable (d) in
@[expose] noncomputable def reeVH : ↥(fixedSubgroup d.steinberg) :=
  ⟨reeV d.1.Closure, steinberg_reeV⟩

variable (hd : d.1.fieldExponent = 2 * m + 1)
include hd

@[expose] noncomputable def reePsiH : SL(2, d.1.fixedField) →* ↥(fixedSubgroup d.steinberg) :=
  (reePsi d m).codRestrict _ fun A => steinberg_reePsi hd A

@[expose] noncomputable def reeTH : ↥(fixedSubgroup d.steinberg) :=
  ⟨reeT d.1.Closure, steinberg_reeT hd⟩

theorem reeTH_eq_commutator :
    reeTH hd = ⁅reeUH d * reeVH d * reeUH d ^ 2 * reeVH d,
      reeUH d * reeVH d ^ 2 * reeUH d * reeVH d⁆ := by
  refine Subtype.ext ?_
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  rw [← commutatorElement_def]
  exact (ree_commutator d.1.Closure).symm

theorem reeTH_mem : reeTH hd ∈ commutator ↥(fixedSubgroup d.steinberg) := by
  rw [reeTH_eq_commutator hd, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

@[expose] noncomputable def reeTbar : FixedPointCandidate d.steinberg :=
  QuotientGroup.mk ⟨reeTH hd, reeTH_mem hd⟩

theorem orderOf_reeTbar : orderOf (reeTbar hd) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · have h : (⟨reeTH hd, reeTH_mem hd⟩ : ↥(commutator ↥(fixedSubgroup d.steinberg))) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext (by
        change reePhi1 d.1.Closure (-1) ^ 2 = 1
        rw [← map_pow, neg_one_sq, map_one]))
    rw [reeTbar, ← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
  · intro h
    have hc := (QuotientGroup.eq_one_iff _).1 h
    have hy : reeUH d * reeTH hd * (reeUH d)⁻¹ ∈ commutator ↥(fixedSubgroup d.steinberg) :=
      (inferInstance : (commutator ↥(fixedSubgroup d.steinberg)).Normal).conj_mem _
        (reeTH_mem hd) (reeUH d)
    have := congrArg (fun z : ↥(commutator ↥(fixedSubgroup d.steinberg)) =>
      ((z : ↥(fixedSubgroup d.steinberg)) : d.AmbientGroup))
      (Subgroup.mem_center_iff.1 hc ⟨_, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    have hinv : (reeU d.1.Closure)⁻¹ = reeU d.1.Closure ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ', reeU_pow_three])
    change reeU d.1.Closure * reeT d.1.Closure * (reeU d.1.Closure)⁻¹ * reeT d.1.Closure =
      reeT d.1.Closure * (reeU d.1.Closure * reeT d.1.Closure * (reeU d.1.Closure)⁻¹) at this
    rw [hinv] at this
    exact ree_t_not_commute d.1.Closure this.symm

omit hd in
theorem reePsi_commute_reeT (A : SL(2, d.1.fixedField)) :
    reePsi d m A * reeT d.1.Closure = reeT d.1.Closure * reePsi d m A := by
  change reePhi1 d.1.Closure (reeIncl d A) *
      reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A)) * reePhi1 d.1.Closure (-1) =
    reePhi1 d.1.Closure (-1) * (reePhi1 d.1.Closure (reeIncl d A) *
      reePhi2 d.1.Closure ((reeFr d)^[m + 1] (reeIncl d A)))
  rw [mul_assoc, ← reePhi_commute d.1.Closure (-1) _, ← mul_assoc, ← map_mul,
    (Commute.neg_one_right (reeIncl d A)).eq, map_mul, mul_assoc]

theorem toQuot_reePsiH_commute (hC : commutator (SL(2, d.1.fixedField)) = ⊤)
    (A : SL(2, d.1.fixedField)) :
    toQuot (reePsiH hd) hC A * reeTbar hd = reeTbar hd * toQuot (reePsiH hd) hC A := by
  have h : (⟨reePsiH hd A, map_mem_commutator _ hC A⟩ :
      ↥(commutator ↥(fixedSubgroup d.steinberg))) * ⟨reeTH hd, reeTH_mem hd⟩ =
      ⟨reeTH hd, reeTH_mem hd⟩ * ⟨reePsiH hd A, map_mem_commutator _ hC A⟩ :=
    Subtype.ext (Subtype.ext (reePsi_commute_reeT (m := m) A))
  have e : toQuot (reePsiH hd) hC A =
      QuotientGroup.mk ⟨reePsiH hd A, map_mem_commutator _ hC A⟩ := rfl
  rw [e, reeTbar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem toQuot_reePsiH_upper_injective (hC : commutator (SL(2, d.1.fixedField)) = ⊤) :
    Function.Injective ((toQuot (reePsiH hd) hC).comp (sl2UpperHom d.1.fixedField)) := by
  refine (injective_iff_map_eq_one _).2 fun c hc => ?_
  have h := (toQuot_eq_one_iff (reePsiH hd) hC _).1 hc _ (map_mem_commutator (reePsiH hd) hC
    (CFSG.LocalAnalysis.ComponentInitial.sl2Lower d.1.fixedField 1))
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  exact Multiplicative.toAdd.injective (eq_zero_of_reePsi_commute (m := m) _ h')

theorem le_localRank_reeG2 (hm : 1 ≤ m) [Finite (FixedPointCandidate d.steinberg)] :
    2 * m + 1 ≤ localRank 3 (FixedPointCandidate d.steinberg) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card d.1.fixedField = 3 ^ (2 * m + 1) := by
    rw [ValidLieTypeIndex.card_fixedField, ReeG2LieIndex.fieldOrder_eq_three_pow, hd]
  have hF4 : 4 ≤ Nat.card d.1.fixedField := by
    rw [hF]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC : commutator (SL(2, d.1.fixedField)) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF4).commutator_eq_top
  have hinj := toQuot_reePsiH_upper_injective hd hC
  have hE : IsElemAbelian 3 ((toQuot (reePsiH hd) hC).comp (sl2UpperHom d.1.fixedField)).range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha⟩ := a.2
      obtain ⟨b', hb⟩ := b.2
      change (a : FixedPointCandidate d.steinberg) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := by
        change Multiplicative.ofAdd (3 • Multiplicative.toAdd a) = Multiplicative.ofAdd 0
        congr 1
        refine Subtype.ext ?_
        have h3 : (3 : d.1.Closure) = 0 := by exact_mod_cast CharP.cast_eq_zero d.1.Closure 3
        rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat, h3, zero_mul,
          ZeroMemClass.coe_zero]
      rw [this, map_one]
  have hcard :
      Nat.card ((toQuot (reePsiH hd) hC).comp (sl2UpperHom d.1.fixedField)).range =
        3 ^ (2 * m + 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hF
  refine le_localRank_of_commute_involution Nat.prime_three (orderOf_reeTbar hd) hE hcard ?_
  rintro _ ⟨c, rfl⟩
  exact toQuot_reePsiH_commute hd hC _

end ReeRank

end CFSG.RankThree.PartTwo.Census.Exceptional
