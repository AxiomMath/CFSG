module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniScalar
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers

variable {d m : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem q1CentUni_heldGU_subset_guSet (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
    (hτQ : ∀ x, τ x = x ^ 2 ^ m) :
    (Held.heldGU d K τ hτ : Set (GL (Fin d) K)) ⊆ LargeEvenGUSet (Fin d) K (2 ^ m) := by
  intro A hA
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul]
  have hmap : (A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ m) =
      (A : Matrix (Fin d) (Fin d) K).map τ := by
    ext i j
    exact (hτQ _).symm
  rw [hmap]
  exact Held.mem_heldGU.mp hA

theorem q1CentUni_pow_mem_scalars (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ m) ≠ (3, 2)) {p : ℕ} {s : GL (Fin d) K}
    (hsN : s ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)))
    (hsp : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ ^ p = 1) :
    s ^ p ∈ LargeEvenScalars (Fin d) K := by
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    unitaryFieldData_of_card hm hK
  obtain ⟨p', hp', hp'dvd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m + 1)
    (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) (Nat.add_le_add_right Nat.one_le_two_pow 1)).ne'
  have hM : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) (⟨s, hsN⟩ ^ p) = 1 := by
    rw [map_pow, hsp]
  have h := TableBUE.mem_scalars_of_projConj_eq_one hF hK hd hdq hp' hp'dvd hM
  simpa using h

omit [Finite K] in
theorem q1CentUni_odd_orderOf (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m) {p : ℕ} (hp : Odd p)
    {s : GL (Fin d) K} (hs : s ^ p ∈ LargeEvenScalars (Fin d) K) : Odd (orderOf s) := by
  obtain ⟨c, hc⟩ := hs
  have hcard : Nat.card Kˣ = (2 ^ m) ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  have hc1 : c ^ ((2 ^ m) ^ 2 - 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hs1 : s ^ (p * ((2 ^ m) ^ 2 - 1)) = 1 := by
    rw [pow_mul, ← hc, ← map_pow, hc1, map_one]
  have hev : Even ((2 ^ m) ^ 2) := by
    rw [← pow_mul]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hodd : Odd ((2 ^ m) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow 2 (2 ^ m) Nat.one_le_two_pow) hev odd_one
  exact Odd.of_dvd_nat (hp.mul hodd) (orderOf_dvd_of_pow_eq_one hs1)

omit [Finite K] in
theorem q1CentUni_commute (hd : 1 ≤ d) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
    (hτQ : ∀ x, τ x = x ^ 2 ^ m) {p : ℕ} (hp : p.Prime) (hcop : ¬ p ∣ Nat.gcd d (2 ^ m + 1))
    {s t : GL (Fin d) K} (hs : s ∈ Held.heldGU d K τ hτ) (ht : t ∈ Held.heldGU d K τ hτ)
    (hsp : s ^ p ∈ LargeEvenScalars (Fin d) K)
    (hst : (s * t)⁻¹ * (t * s) ∈ LargeEvenScalars (Fin d) K) :
    t * s = s * t := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨z, hz⟩ := hst
  have hzp : (z : K) ^ p = 1 := by
    refine pow_eq_one_of_commutator_eq_scalar (s := t) (t := s) (a := (z : K)) ?_ ?_
    · rw [← hz, Matrix.GeneralLinearGroup.coe_scalar]
    · obtain ⟨c, hc⟩ := hsp
      exact ⟨(c : K), by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]⟩
  have hzd : (z : K) ^ d = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det ((s * t)⁻¹ * (t * s)) = z ^ d := by
      rw [← hz, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    have hone : Matrix.GeneralLinearGroup.det ((s * t)⁻¹ * (t * s)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul]
      simp [mul_comm, mul_assoc]
    have hu : z ^ d = 1 := by rw [← hdet, hone]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hcomm_mem : (s * t)⁻¹ * (t * s) ∈ Held.heldGU d K τ hτ :=
    mul_mem (inv_mem (mul_mem hs ht)) (mul_mem ht hs)
  have hmat := Held.mem_heldGU.mp hcomm_mem
  rw [← hz] at hmat
  have hzz : τ (z : K) * (z : K) = 1 := by
    have hmat' : Matrix.scalar (Fin d) (τ (z : K) * (z : K)) = 1 := by
      simpa only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal] using hmat
    have h00 := congrFun (congrFun hmat' (⟨0, by omega⟩ : Fin d)) (⟨0, by omega⟩ : Fin d)
    simpa [Matrix.scalar_apply] using h00
  have hzq : (z : K) ^ (2 ^ m + 1) = 1 := by
    rw [pow_succ, ← hτQ]
    exact hzz
  have hzp' : z ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzp, Units.val_one]
  have hzd' : z ^ d = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzd, Units.val_one]
  have hzq' : z ^ (2 ^ m + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzq, Units.val_one]
  have hzorder : orderOf z ∣ Nat.gcd p (Nat.gcd d (2 ^ m + 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp')
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzd') (orderOf_dvd_of_pow_eq_one hzq'))
  have hz1 : z = 1 := by
    have h : orderOf z = 1 := by
      have hdvd := hzorder
      rw [(hp.coprime_iff_not_dvd.mpr hcop).gcd_eq_one] at hdvd
      exact Nat.dvd_one.mp hdvd
    exact orderOf_eq_one_iff.mp h
  have hcomm1 : (s * t)⁻¹ * (t * s) = 1 := by
    rw [← hz, hz1, map_one]
  exact (inv_mul_eq_one.mp hcomm1).symm

theorem q1CentUni_commute_of_projConj (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ m) ≠ (3, 2)) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
    (hτQ : ∀ x, τ x = x ^ 2 ^ m) {p : ℕ} (hp : p.Prime) (hcop : ¬ p ∣ Nat.gcd d (2 ^ m + 1))
    {s t : GL (Fin d) K} (hs : s ∈ Held.heldGU d K τ hτ) (ht : t ∈ Held.heldGU d K τ hτ)
    (hsN : s ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)))
    (htN : t ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)))
    (hsp : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ ^ p = 1)
    (hcomm : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ *
        TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ *
        TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩) :
    t * s = s * t := by
  have hscalar : s ^ p ∈ LargeEvenScalars (Fin d) K :=
    q1CentUni_pow_mem_scalars hK hm hd hdq hsN hsp
  let X : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    (⟨s, hsN⟩ * ⟨t, htN⟩)⁻¹ * (⟨t, htN⟩ * ⟨s, hsN⟩)
  have hX : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) X = 1 := by
    dsimp only [X]
    simp only [map_mul, map_inv, hcomm, inv_mul_cancel]
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    unitaryFieldData_of_card hm hK
  obtain ⟨p', hp', hp'dvd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m + 1)
    (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) (Nat.add_le_add_right Nat.one_le_two_pow 1)).ne'
  have hXscalar : (X : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    TableBUE.mem_scalars_of_projConj_eq_one hF hK hd hdq hp' hp'dvd hX
  have hXval : (X : GL (Fin d) K) = (s * t)⁻¹ * (t * s) := rfl
  refine q1CentUni_commute (by omega : 1 ≤ d) τ hτ hτQ hp hcop hs ht hscalar ?_
  rw [← hXval]
  exact hXscalar

section Lift

theorem q1CentUni_exists_lift (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    {u : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))}
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (LargeEvenGUSet (Fin d) K (2 ^ m))) :
    ∃ (s : GL (Fin d) K) (hsN : s ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))),
      s ∈ Held.heldGU d K τ hτ ∧
        u = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ := by
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    unitaryFieldData_of_card hm hK
  obtain ⟨M, hM, rfl⟩ :=
    TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer (d := d) hF) hu
  obtain ⟨c, hc⟩ := exists_heldGU_scalar_mul (d := d) hK hm τ hτ hτQ hM
  have hz : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ LargeEvenScalars (Fin d) K := ⟨c, rfl⟩
  have hzN : (Matrix.GeneralLinearGroup.scalar (Fin d) c) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    TableB.scalar_mem_normalizer _ hz
  have hMN : (M : GL (Fin d) K) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    TableBUE.gu_subset_normalizer (d := d) hF hM
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c * (M : GL (Fin d) K),
    mul_mem hzN hMN, hc, ?_⟩
  have hmul : (⟨Matrix.GeneralLinearGroup.scalar (Fin d) c * (M : GL (Fin d) K),
      mul_mem hzN hMN⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))) =
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c, hzN⟩ * ⟨M, hMN⟩ := rfl
  rw [hmul, map_mul, TableB.projConj_of_scalar _ hz, one_mul]

end Lift

end CFSG.StandardType
