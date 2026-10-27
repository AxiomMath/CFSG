module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {f : ℕ} {K : Type} [Field K]

theorem isPG1 {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) :=
  ⟨by simp, fun i j => by
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subfield.one_mem _
    · exact Subfield.zero_mem _⟩

abbrev P4 (h : UnitaryFieldData 2 f K) : Type :=
  primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

noncomputable abbrev InnAut (T : Type) [Group T] : Subgroup (MulAut T) := inner T

theorem hq4 (f : ℕ) : ¬ (4 = 3 ∧ 2 ^ f = 2) := fun ⟨h, _⟩ => by omega

@[expose] noncomputable def fld (h : UnitaryFieldData 2 f K) (σ : K ≃+* K) : MulAut (P4 h) :=
  primeFormFieldHom h (isPG1 (n := 4)) σ

@[expose] noncomputable def FF (h : UnitaryFieldData 2 f K) : MulAut (P4 h) →* (K ≃+* K) :=
  primeFormFieldFactor h (isPG1 (n := 4)) (by norm_num) (hq4 f)

variable (h : UnitaryFieldData 2 f K)

theorem inner_le_D :
    inner (P4 h) ≤ primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ α).mp hα
  exact ⟨_, rfl⟩

theorem D_le_inner (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1) :
    primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≤ inner (P4 h) := by
  intro α hα
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (n := 4) (by norm_num) (hq4 f)
  rw [hgcd] at hcard
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  have h1 : (QuotientGroup.mk (⟨α, hα⟩ : primeFormD h ((1 : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) : primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ⧸
        (inner (P4 h)).subgroupOf (primeFormD h ((1 : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K))) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem ker_FF : (FF h).ker = primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  ker_primeFormFieldFactor h (isPG1 (n := 4)) (by norm_num) (hq4 f)

theorem FF_apply (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (σ : K ≃+* K) : FF h (primeFormConjHom h _ A * fld h σ) = σ :=
  primeFormFieldFactor_apply h (isPG1 (n := 4)) (by norm_num) (hq4 f) A σ

theorem FF_fld (σ : K ≃+* K) : FF h (fld h σ) = σ := by
  have := FF_apply h 1 σ
  rwa [map_one, one_mul] at this

theorem fld_eq_one {σ : K ≃+* K} (hσ : fld h σ = 1) : σ = 1 := by
  have := FF_fld h σ
  rw [hσ, map_one] at this
  exact this.symm

theorem fld_one : fld h 1 = 1 := (primeFormFieldHom h (isPG1 (n := 4))).map_one

theorem fld_pow (σ : K ≃+* K) (k : ℕ) : fld h σ ^ k = fld h (σ ^ k) :=
  ((primeFormFieldHom h (isPG1 (n := 4))).map_pow σ k).symm

theorem exists_fieldFactor_of_pPow (hgcd : Nat.gcd 4 (2 ^ f + 1) = 1) [Finite K] {p : ℕ}
    (hp : p.Prime) {α : MulAut (P4 h)} (hα : α ∉ inner (P4 h)) {m : ℕ} (hm : orderOf α = p ^ m) :
    ∃ (j : ℕ) (σ : K ≃+* K) (s : MulAut (P4 h)), orderOf σ = p ∧ s ∈ inner (P4 h) ∧
      α ^ (p ^ j) = s * fld h σ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hex : ∃ j, α ^ (p ^ j) ∈ inner (P4 h) :=
    ⟨m, by rw [← hm, pow_orderOf_eq_one]; exact one_mem _⟩
  set j₁ := Nat.find hex with hj₁
  have hj₁mem : α ^ (p ^ j₁) ∈ inner (P4 h) := Nat.find_spec hex
  have hj₁pos : j₁ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hj₁mem
    exact hα hj₁mem
  obtain ⟨j, hj⟩ : ∃ j, j₁ = j + 1 := ⟨j₁ - 1, by omega⟩
  have hjnot : α ^ (p ^ j) ∉ inner (P4 h) := Nat.find_min hex (by omega)
  set α' := α ^ (p ^ j) with hα'
  have hα'p : α' ^ p ∈ inner (P4 h) := by
    rw [hα', ← pow_mul, ← pow_succ, ← hj]
    exact hj₁mem
  obtain ⟨σ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h (isPG1 (n := 4)) (by norm_num)
    (hq4 f) α'
  have hFF : FF h α' = σ := by rw [hA]; exact FF_apply h A σ
  have hσp : σ ^ p = 1 := by
    rw [← hFF, ← map_pow]
    have : α' ^ p ∈ (FF h).ker := by
      rw [ker_FF]
      exact inner_le_D h hα'p
    exact this
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hjnot
    refine D_le_inner h hgcd ?_
    rw [hA, h1, map_one, mul_one]
    exact ⟨A, rfl⟩
  have hcA : primeFormConjHom h _ A ∈ inner (P4 h) :=
    D_le_inner h hgcd ⟨A, rfl⟩
  exact ⟨j, σ, primeFormConjHom h _ A, orderOf_eq_prime hσp hσ1, hcA, hA⟩

theorem ringEquiv_fixes_rootsOfUnity {p : ℕ} (hp : p.Prime) {σ : K ≃+* K} (hσ : σ ^ p = 1)
    {c : K} (hc : c ^ p = 1) : σ c = c := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hc1 : c = 1
  · rw [hc1]
    exact map_one σ
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  have hord : orderOf c = p := orderOf_eq_prime hc hc1
  have hprim : IsPrimitiveRoot c p := hord ▸ IsPrimitiveRoot.orderOf c
  have hσc : (σ c) ^ p = 1 := by rw [← map_pow, hc, map_one]
  obtain ⟨r, -, hr⟩ := hprim.eq_pow_of_pow_eq_one hσc
  have hiter : ∀ i : ℕ, (σ ^ i) c = c ^ (r ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hr, ← pow_mul, ← pow_succ']
  have h1 : c ^ (r ^ p) = c := by
    have := hiter p
    rw [hσ] at this
    exact this.symm
  have hr0 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0, zero_pow hp.ne_zero, pow_zero] at h1
      exact hc1 h1.symm
    · exact h0
  have hrp1 : 1 ≤ r ^ p := Nat.one_le_pow _ _ hr0
  have hcpow : c ^ (r ^ p - 1) = 1 := by
    have : c ^ (r ^ p - 1) * c = 1 * c := by
      rw [← pow_succ, Nat.sub_add_cancel hrp1, h1, one_mul]
    exact mul_right_cancel₀ hc0 this
  have h2 : p ∣ r ^ p - 1 := by
    have := orderOf_dvd_of_pow_eq_one hcpow
    rwa [hord] at this
  have h3 : p ∣ r - 1 := by
    have h4 : ((r : ZMod p)) ^ p = (r : ZMod p) := ZMod.pow_card _
    have h5 : ((r ^ p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.modEq_iff_dvd' hrp1).mpr h2).symm
    push_cast at h5
    rw [h4] at h5
    have h6 : ((r : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h5
    exact (Nat.modEq_iff_dvd' hr0).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp h6).symm
  rw [← hr]
  have : c ^ (r - 1) = 1 := by
    have h3' : orderOf c ∣ r - 1 := by rw [hord]; exact h3
    exact orderOf_dvd_iff_pow_eq_one.mp h3'
  calc c ^ r = c ^ (r - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hr0]
    _ = c := by rw [this, one_mul]

end CFSG.RankThree.PartOne.Q1327R
