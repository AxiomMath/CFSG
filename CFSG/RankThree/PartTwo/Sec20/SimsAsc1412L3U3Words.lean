module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Group
import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Classical

variable {K : Type} [Field K]

private theorem unitaryScalars_eq_bot_of_mod_three {p : ℕ} (h : UnitaryFieldData p 1 K)
    (hp3 : p % 3 = 1) : unitaryScalars h 3 = ⊥ := by
  rw [← Subgroup.card_eq_one, card_unitaryScalars h (by norm_num), pow_one]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem unitaryProj_injective_of_mod_three1412 {p : ℕ} (h : UnitaryFieldData p 1 K)
    (hp3 : p % 3 = 1) : Function.Injective (unitaryProj h 3) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, unitaryScalars_eq_bot_of_mod_three h hp3]

theorem center_unitaryPSU_of_mod_three1412 {p : ℕ} (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) :
    Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have hq : 2 < p ^ 1 := by
    have := h.prime.two_le
    rw [pow_one]
    omega
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  have hg : g ∈ Subgroup.center (unitarySU p 1 K 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.mp hx (unitaryProj h 3 y)
    rw [← map_mul, ← map_mul] at this
    exact unitaryProj_injective_of_mod_three1412 h hp3 this
  rw [center_unitarySU_three (h := h) hq, unitaryScalars_eq_bot_of_mod_three h hp3,
    Subgroup.mem_bot] at hg
  rw [hg, map_one]
  exact Subgroup.one_mem _

private theorem exists_dvd_orderOf_mul_inv_of_conj {G : Type*} [Group G] {α α₀ β : MulAut G}
    (hα : α = β * α₀ * β⁻¹) {n : ℕ} {y : G} (hy : n ∣ orderOf (α₀ y * y⁻¹)) :
    ∃ x : G, n ∣ orderOf (α x * x⁻¹) := by
  refine ⟨β y, ?_⟩
  have e : α (β y) * (β y)⁻¹ = β (α₀ y * y⁻¹) := by
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  rw [e, MulEquiv.orderOf_eq]
  exact hy

private theorem one_add_pow_prime_eq_one {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hp : 3 ≤ p) {N : R} (hN : N ^ 3 = 0) : (1 + N) ^ p = 1 := by
  rw [add_pow_char_of_commute p (Commute.one_left N), one_pow, pow_eq_zero_of_le hp hN, add_zero]

private theorem exists_mul_bar_eq_neg_one {p f : ℕ} (h : UnitaryFieldData p f K) :
    ∃ c : K, c * h.bar c = -1 := by
  have hm : (-1 : K) ∈ h.fixedField := by rw [h.mem_fixedField, map_neg, map_one]
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨-1, hm⟩
  exact ⟨c, congrArg Subtype.val hc⟩

private theorem exists_bar_eq_neg_of_unitary {p f : ℕ} (h : UnitaryFieldData p f K) :
    ∃ t : K, t ≠ 0 ∧ h.bar t = -t := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact ⟨c - h.bar c, sub_ne_zero.mpr (Ne.symm hc), by rw [map_sub, h.bar_bar, neg_sub]⟩

private theorem orderOf_eq_two_of_mul_self_of_ne_one {G : Type*} [Group G] {g : G} (hg : g * g = 1)
    (h1 : g ≠ 1) : orderOf g = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hg) h1

section Reflections

variable {c d : K}

private def u3Refl (c d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 2 * d, 2; 2 * c, -3, 2 * c; 2, 2 * d, 1]

private def u3Nil (c d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2, -2 * d, -2; -2 * c, 2, -2 * c; 2, 2 * d, 0]

private theorem u3Refl_mul_self (hcd : c * d = -1) : u3Refl c d * u3Refl c d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Refl, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem det_u3Refl (hcd : c * d = -1) : (u3Refl c d).det = 1 := by
  simp [u3Refl, Matrix.det_fin_three]
  grind

private theorem map_transpose_u3Refl (σ : K →+* K) (hc : σ c = d) (hd : σ d = c) :
    ((u3Refl c d).map σ)ᵀ = u3Refl c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Refl, hc, hd, map_ofNat]

private theorem negNegOneDiag_mul_u3Refl : negNegOneDiag K * u3Refl c d = 1 + u3Nil c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negNegOneDiag, u3Refl, u3Nil, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] <;> ring

private theorem u3Nil_pow_three (hcd : c * d = -1) : u3Nil c d ^ 3 = 0 := by
  rw [pow_succ, sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Nil, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

end Reflections

private theorem exists_orderOf_two_orderOf_mul_unitaryInvT {p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p 1 K) (hp3 : 3 ≤ p) (hp2 : p ≠ 2) :
    ∃ s : unitarySU p 1 K 3, orderOf s = 2 ∧ orderOf (unitaryInvT h * s) = p := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨c, hc⟩ := exists_mul_bar_eq_neg_one h
  obtain ⟨d, hd⟩ : ∃ d, d = h.bar c := ⟨_, rfl⟩
  have hcd : c * d = -1 := by rw [hd]; exact hc
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcd
    exact zero_ne_one (α := K) (by linear_combination -hcd)
  have hbd : h.bar d = c := by rw [hd, h.bar_bar]
  set S : GL (Fin 3) K := ⟨u3Refl c d, u3Refl c d, u3Refl_mul_self hcd, u3Refl_mul_self hcd⟩
  have hS : S ∈ unitarySU p 1 K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨det_u3Refl hcd, ?_⟩
    change ((u3Refl c d).map h.bar)ᵀ * u3Refl c d = 1
    rw [map_transpose_u3Refl h.bar hd.symm hbd, u3Refl_mul_self hcd]
  refine ⟨⟨S, hS⟩, ?_, ?_⟩
  · refine orderOf_eq_two_of_mul_self_of_ne_one
      (Subtype.ext (Units.ext (u3Refl_mul_self hcd))) fun h1 => ?_
    have e := congrArg (fun g : unitarySU p 1 K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) h1
    simp [S, u3Refl] at e
    exact h2 (e.resolve_right hd0)
  · refine orderOf_eq_prime ?_ fun h1 => ?_
    · apply Subtype.ext
      apply Units.ext
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul,
        coe_unitaryInvT]
      change (negNegOneDiag K * u3Refl c d) ^ p = _
      rw [negNegOneDiag_mul_u3Refl]
      exact one_add_pow_prime_eq_one hp3 (u3Nil_pow_three hcd)
    · have e := congrArg (fun g : unitarySU p 1 K 3 =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) h1
      simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryInvT, OneMemClass.coe_one,
        Units.val_one] at e
      change (negNegOneDiag K * u3Refl c d) 0 1 = _ at e
      rw [negNegOneDiag_mul_u3Refl] at e
      simp [u3Nil] at e
      exact h2 (e.resolve_right hd0)

private theorem exists_dvd_orderOf_conj_unitaryInvT_of_mod_three {p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) :
    ∃ x : unitaryPSU h 3,
      p ∣ orderOf (MulAut.conj (unitaryProj h 3 (unitaryInvT h)) x * x⁻¹) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hp3' : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨s, hs2, hsp⟩ := exists_orderOf_two_orderOf_mul_unitaryInvT h hp3' hp2
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 hs2)
  refine ⟨unitaryProj h 3 g, dvd_of_eq ?_⟩
  have htt : unitaryProj h 3 (unitaryInvT h) * unitaryProj h 3 (unitaryInvT h) = 1 := by
    rw [← map_mul, ← sq, unitaryInvT_sq, map_one]
  have e : MulAut.conj (unitaryProj h 3 (unitaryInvT h)) (unitaryProj h 3 g) *
      (unitaryProj h 3 g)⁻¹ = unitaryProj h 3 (unitaryInvT h * s) := by
    rw [← hg, MulAut.conj_apply, inv_eq_of_mul_eq_one_right htt]
    simp only [map_mul, map_inv, mul_assoc]
  rw [e, orderOf_injective (unitaryProj h 3) (unitaryProj_injective_of_mod_three1412 h hp3), hsp]

section Unipotent

variable {i : K} {v : Fin 3 → K}

private def u3Rank (i : K) (v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun r s => i * v r * v s

private theorem u3Rank_mul_self (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 0) :
    u3Rank i v * u3Rank i v = 0 := by
  ext r s
  simp only [u3Rank, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.zero_apply]
  linear_combination (i ^ 2 * v r * v s) * hv

private theorem transpose_u3Rank : (u3Rank i v)ᵀ = u3Rank i v := by
  ext r s
  simp only [u3Rank, Matrix.transpose_apply, Matrix.of_apply]
  ring

private theorem map_u3Rank (σ : K →+* K) (hi : σ i = -i) (hv : ∀ j, σ (v j) = v j) :
    (u3Rank i v).map σ = -u3Rank i v := by
  ext r s
  simp only [u3Rank, Matrix.map_apply, Matrix.of_apply, Matrix.neg_apply, map_mul, hi, hv]
  ring

private theorem det_one_add_u3Rank (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 0) :
    (1 + u3Rank i v).det = 1 := by
  simp only [Matrix.det_fin_three, u3Rank, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  simp
  linear_combination i * hv

private theorem u3Rank_ne_zero (hi : i ≠ 0) (hv : v 2 ≠ 0) : u3Rank i v ≠ 0 := fun h0 => by
  have := congrFun (congrFun h0 2) 2
  simp only [u3Rank, Matrix.of_apply, Matrix.zero_apply] at this
  exact mul_ne_zero (mul_ne_zero hi hv) hv this

end Unipotent

private theorem exists_symm_unipotent_bar_inv {p : ℕ} [Fact p.Prime] (h : UnitaryFieldData p 1 K)
    (hp3 : 3 ≤ p) :
    ∃ y : GL (Fin 3) K,
      ((y : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (y : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (y : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      (y : Matrix (Fin 3) (Fin 3) K).map h.bar = ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      y ^ p = 1 ∧ y ≠ 1 := by
  have : CharP K p := h.charP
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq K p (-1)
  obtain ⟨i, hi0, hi⟩ := exists_bar_eq_neg_of_unitary h
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, v = ![(a : K), (b : K), 1] := ⟨_, rfl⟩
  have hv0 : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 0 := by
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_pow]
    push_cast at hab
    linear_combination hab
  have hbv : ∀ j, h.bar (v j) = v j := by
    intro j
    fin_cases j <;> simp [hv]
  have hv2 : v 2 ≠ 0 := by simp [hv]
  have hNN : u3Rank i v * u3Rank i v = 0 := u3Rank_mul_self hv0
  have hy1 : (1 + u3Rank i v) * (1 - u3Rank i v) = 1 := by
    have e : (1 + u3Rank i v) * (1 - u3Rank i v) = 1 - u3Rank i v * u3Rank i v := by noncomm_ring
    rw [e, hNN, sub_zero]
  have hy2 : (1 - u3Rank i v) * (1 + u3Rank i v) = 1 := by
    have e : (1 - u3Rank i v) * (1 + u3Rank i v) = 1 - u3Rank i v * u3Rank i v := by noncomm_ring
    rw [e, hNN, sub_zero]
  have hbar : (1 + u3Rank i v).map h.bar = 1 - u3Rank i v := by
    rw [← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply,
      map_u3Rank h.bar hi hbv, sub_eq_add_neg]
  refine ⟨⟨1 + u3Rank i v, 1 - u3Rank i v, hy1, hy2⟩, ?_, det_one_add_u3Rank hv0, hbar, ?_, ?_⟩
  · change ((1 + u3Rank i v).map h.bar)ᵀ * (1 + u3Rank i v) = 1
    rw [hbar, Matrix.transpose_sub, Matrix.transpose_one, transpose_u3Rank, hy2]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change (1 + u3Rank i v) ^ p = 1
    refine one_add_pow_prime_eq_one hp3 ?_
    rw [pow_succ, sq, hNN, Matrix.zero_mul]
  · intro h1
    have e := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_one] at e
    exact u3Rank_ne_zero hi0 hv2 (by simpa using e)

theorem exists_dvd_orderOf_conj_of_orderOf_eq_two1412 {p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) {s : unitaryPSU h 3} (hs : orderOf s = 2) :
    ∃ x : unitaryPSU h 3, p ∣ orderOf (MulAut.conj s x * x⁻¹) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_unitaryProj_unitaryInvT h hp2 hs)
  obtain ⟨y, hy⟩ := exists_dvd_orderOf_conj_unitaryInvT_of_mod_three h hp3
  have hβ : MulAut.conj s = MulAut.conj g⁻¹ * MulAut.conj (unitaryProj h 3 (unitaryInvT h)) *
      (MulAut.conj g⁻¹)⁻¹ := by
    rw [← hg]
    simp only [map_mul, map_inv]
    group
  exact exists_dvd_orderOf_mul_inv_of_conj hβ hy

private theorem exists_dvd_orderOf_mul_inv_of_bar {p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) {A : unitaryIsom3 h} {σ : K ≃+* K}
    (hσbar : ∀ c, σ c = h.bar c) {c : Kˣ} (hcN : h.norm (c : K) = 1)
    (hcA : (A : GL (Fin 3) K) * glAut σ A = GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ x : unitaryPSU h 3, p ∣ orderOf ((psuConj h A * psuField h σ) x * x⁻¹) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hp3' : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hσmat : ∀ M : Matrix (Fin 3) (Fin 3) K, M.map σ = M.map h.bar := fun M => by
    ext i j
    exact hσbar _
  have hAA : (A : GL (Fin 3) K) * glAut σ A = 1 := by
    have hc1 : c = 1 := by
      have hmat := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).det) hcA
      simp only [Units.val_mul, coe_glAut, det_mul, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hmat
      have hσdet : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).det =
          h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
        rw [hσmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have hN := norm_det_of_mem_unitaryIsom3 A.2
      rw [UnitaryFieldData.norm] at hN
      have hc3 : (c : K) ^ 3 = 1 := by rw [← hmat, hσdet, hN]
      obtain ⟨m, hm⟩ : ∃ m, p + 1 = 3 * m + 2 := ⟨(p + 1) / 3, by omega⟩
      have hc2 : (c : K) ^ 2 = 1 := by
        rw [UnitaryFieldData.norm, h.bar_apply, pow_one, ← pow_succ'] at hcN
        rwa [hm, pow_add, pow_mul, hc3, one_pow, one_mul] at hcN
      apply Units.ext
      rw [Units.val_one]
      calc (c : K) = (c : K) * (c : K) ^ 2 := by rw [hc2, mul_one]
        _ = (c : K) ^ 3 := by ring
        _ = 1 := hc3
    rw [hcA, hc1, map_one]
  have hAAm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 := by
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hAA
    simpa [coe_glAut, hσmat] using this
  obtain ⟨C, d, hAC, hCC⟩ := exists_antiunitary_normalForm_unitary3 h hp2 A.2 hAAm
  obtain ⟨y, hy1, hydet, hybar, hyp, hyne⟩ := exists_symm_unipotent_bar_inv h hp3'
  have hyS : y ∈ gramSU h (d • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    refine mem_gramSU.mpr ⟨?_, hydet⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hy1]
  have hxS : C * y * C⁻¹ ∈ unitarySU p 1 K 3 := by
    rw [unitarySU_eq_gramSU h 3]
    exact conj_mem_gramSU_of_gram h hCC hyS
  set x : unitarySU p 1 K 3 := ⟨C * y * C⁻¹, hxS⟩
  have hyσ : glAut σ y = y⁻¹ := by
    apply Units.ext
    rw [coe_glAut, hσmat]
    exact hybar
  have hCσ : glAut σ C = (A : GL (Fin 3) K)⁻¹ * C := by
    rw [eq_inv_mul_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, coe_glAut, hσmat]
    exact hAC
  have hαx : (psuConj h A * psuField h σ) (unitaryProj h 3 x) = (unitaryProj h 3 x)⁻¹ := by
    rw [MulAut.mul_apply, ← map_inv]
    change psuConj h A (psuField h σ (x : unitaryPSU h 3)) = ((x⁻¹ : unitarySU p 1 K 3) :
      unitaryPSU h 3)
    rw [psuField_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suConj, coe_suField, Subgroup.coe_inv]
    change (A : GL (Fin 3) K) * glAut σ (C * y * C⁻¹) * (A : GL (Fin 3) K)⁻¹ = (C * y * C⁻¹)⁻¹
    rw [map_mul, map_mul, map_inv, hyσ, hCσ]
    group
  have hxp : orderOf (unitaryProj h 3 x) = p := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · have : x ^ p = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        change (C * y * C⁻¹) ^ p = 1
        rw [conj_pow, hyp, mul_one, mul_inv_cancel]
      rw [← map_pow, this, map_one]
    · have hx1 : x = 1 :=
        unitaryProj_injective_of_mod_three1412 h hp3 (h1.trans (map_one _).symm)
      have hy1' : y = 1 := by
        have e : C * y * C⁻¹ = 1 := congrArg Subtype.val hx1
        calc y = C⁻¹ * (C * y * C⁻¹) * C := by group
          _ = 1 := by rw [e, mul_one, inv_mul_cancel]
      exact hyne hy1'
  refine ⟨unitaryProj h 3 x, dvd_of_eq ?_⟩
  have hw : (psuConj h A * psuField h σ) (unitaryProj h 3 x) * (unitaryProj h 3 x)⁻¹ =
      ((unitaryProj h 3 x) ^ 2)⁻¹ := by
    rw [hαx]
    group
  rw [hw, orderOf_inv, Nat.Coprime.orderOf_pow
    (by rw [hxp]; exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2), hxp]

theorem exists_dvd_orderOf_mul_inv_unitaryPSU3 {p : ℕ} [Fact p.Prime] (h : UnitaryFieldData p 1 K)
    (hp3 : p % 3 = 1) (α : MulAut (unitaryPSU h 3)) (hα : orderOf α = 2) :
    ∃ x : unitaryPSU h 3, p ∣ orderOf (α x * x⁻¹) := by
  have hp : p ≠ 2 := by
    rintro rfl
    omega
  have hq : 2 < p ^ 1 := by
    have := (Fact.out : p.Prime).two_le
    rw [pow_one]
    omega
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  have key :
      psuConj h (A * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩) * psuField h (σ * σ) = 1 := by
    rw [map_mul, map_mul, ← psuField_mul_psuConj_mul_inv σ A, ← hα2, sq]
    simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨hσσ, c, hcN, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ key
  rcases ringEquiv_eq_refl_or_bar h hσσ with rfl | hσbar
  ·
    have hα' : psuConj h A * psuField h (RingEquiv.refl K) = psuConj h A := by
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    rw [hα'] at hα hα2 ⊢
    obtain ⟨s, hs⟩ := mem_range_conj_of_mem_psuConj_range_of_coprime ⟨A, rfl⟩
      (m := 2) (by norm_num) hα2
    have hZ := center_unitaryPSU_of_mod_three1412 h hp3
    have hs2 : orderOf s = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have hc : MulAut.conj (s ^ 2) = 1 := by rw [map_pow, hs, hα2]
        have : s ^ 2 ∈ Subgroup.center (unitaryPSU h 3) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have e := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ y) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at e
          calc y * s ^ 2 = s ^ 2 * y * (s ^ 2)⁻¹ * s ^ 2 := by rw [e]
            _ = s ^ 2 * y := by group
        rw [hZ, Subgroup.mem_bot] at this
        exact this
      · rw [h1, map_one] at hs
        rw [← hs, orderOf_one] at hα
        exact absurd hα (by norm_num)
    rw [← hs]
    exact exists_dvd_orderOf_conj_of_orderOf_eq_two1412 h hp3 hs2
  ·
    exact exists_dvd_orderOf_mul_inv_of_bar h hp3 hσbar hcN hcA

end CFSG.RankThree.PartTwo.Sec20
