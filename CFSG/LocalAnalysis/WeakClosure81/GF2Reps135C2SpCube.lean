module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpFourWeight
public import CFSG.Quasithin.Background.SmithCurtisMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpGaussLong
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisInterp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis

private theorem spCU_odd_card_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card K - 1) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have hc : Nat.card K - 1 = 2 ^ (n : ℕ) - 1 := by
    rw [Nat.card_eq_fintype_card, hcard]
  rw [← Nat.not_even_iff_odd, hc, Nat.even_sub (Nat.one_le_two_pow)]
  have h2n : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.pos.ne').mpr even_two
  simp [h2n]

private theorem spCU_natCard_sub_one_cast_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] :
    ((Nat.card K - 1 : ℕ) : K) = 1 :=
  natCast_eq_one_of_odd_of_two_eq_zero (spCU_odd_card_sub_one) (CharP.cast_eq_zero K 2)

private def spCU_e {n : ℕ} (hn : 3 ≤ n) : Fin n → ℤ :=
  ((0 : Fin n → ℤ) + (1 : ℤ) • stdVec (.negativeLong (⟨1, by omega⟩ : Fin n))) +
    (1 : ℤ) • stdVec (.negativeLong (⟨0, by omega⟩ : Fin n))

private noncomputable def spCU_X {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) : StatedSp n K :=
  elt (.positiveLong (⟨0, by omega⟩ : Fin n)) 1 * elt (.positiveLong (⟨1, by omega⟩ : Fin n)) 1

private noncomputable def spCU_z {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (ι : K →+* k) (ρ : Representation k (StatedSp n K) V) (y : V) : V :=
  ∑ v : K, ι v ^ (Nat.card K - 1 - 1) •
    ρ (elt (.negativeLong (⟨1, by omega⟩ : Fin n)) v) y
private noncomputable def spCU_w {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (ι : K →+* k) (ρ : Representation k (StatedSp n K) V) (y : V) : V :=
  ∑ t : K, ι t ^ (Nat.card K - 1 - 1) •
    ρ (elt (.negativeLong (⟨0, by omega⟩ : Fin n)) t) (spCU_z hn ι ρ y)

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence in
private theorem spCU_weight {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (hK : 4 ≤ Nat.card K) {k : Type} [Field k] (ι : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1) :
    spCU_w hn ι ρ y₀ ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι (spCU_e hn)) := by
  have h0 : y₀ ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι (0 : Fin n → ℤ)) := by
    refine mem_weightSpace_of_isCurtisType (D := spCurtisDatum n K) ht (diagHom n K) ?_
      (spTorusChar ι (0 : Fin n → ℤ)) ?_
    · intro e
      exact diagHom_mem_spCurtisDatum_H e
    · intro e
      rw [spTorusChar_apply, hχ _ (diagHom_mem_spCurtisDatum_H e)]
      simp
  have hz : spCU_z hn ι ρ y₀ ∈ weightSpace (ρ.comp (diagHom n K))
      (spTorusChar ι ((0 : Fin n → ℤ) +
        (1 : ℤ) • stdVec (.negativeLong (⟨1, by omega⟩ : Fin n)))) := by
    rw [spCU_z]
    exact sum_pow_smul_mem_weightSpace (K := K) (j := 1) ι ρ
      (.negativeLong (⟨1, by omega⟩ : Fin n)) h0 (show 1 < Nat.card K by omega)
  have hw : spCU_w hn ι ρ y₀ ∈ weightSpace (ρ.comp (diagHom n K))
      (spTorusChar ι (spCU_e hn)) := by
    rw [spCU_w]
    simpa only [spCU_e, Nat.cast_one] using
      sum_pow_smul_mem_weightSpace (K := K) (j := 1) ι ρ
        (.negativeLong (⟨0, by omega⟩ : Fin n)) hz (show 1 < Nat.card K by omega)
  exact hw

private theorem spCU_f_sum_factor {G : Type*} [Group G] {K : Type*} [Field K] [Fintype K]
    {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (X : G) (Y0 Y1 : K → G) (y Z : V) (f : Module.Dual k V)
    (a b A B : K → k) (hZ : Z = ∑ v : K, b v • ρ (Y1 v) y)
    (hiff : ∀ t v : K, f (ρ ((X * Y0 t) * Y1 v) y) = A t * B v) :
    f (ρ X (∑ t : K, a t • ρ (Y0 t) Z)) =
      (∑ t : K, a t * A t) * (∑ v : K, b v * B v) := by
  rw [hZ]
  have h1 : f (ρ X (∑ t : K, a t • ρ (Y0 t) (∑ v : K, b v • ρ (Y1 v) y))) =
      ∑ t : K, a t * f (ρ (X * Y0 t) (∑ v : K, b v • ρ (Y1 v) y)) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp
  have h2 : ∀ t : K, f (ρ (X * Y0 t) (∑ v : K, b v • ρ (Y1 v) y)) =
      ∑ v : K, b v * f (ρ ((X * Y0 t) * Y1 v) y) := by
    intro t
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp
  have h3 : f (ρ X (∑ t : K, a t • ρ (Y0 t) (∑ v : K, b v • ρ (Y1 v) y))) =
      ∑ t : K, ∑ v : K, (a t * b v) * f (ρ ((X * Y0 t) * Y1 v) y) := by
    rw [h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h2 t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have h4 : f (ρ X (∑ t : K, a t • ρ (Y0 t) (∑ v : K, b v • ρ (Y1 v) y))) =
      ∑ t : K, ∑ v : K, (a t * A t) * (b v * B v) := by
    rw [h3]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hiff t v]
    ring
  rw [h4, Finset.sum_mul_sum]

private theorem spCU_f_w_eq_one {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (hK : 4 ≤ Nat.card K) {k : Type} [Field k] [CharP k 2] (ι : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1)
    (hμ : μ ⟨n - 1, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨n - 1, by omega⟩ : Fin n)) :
    f (ρ (spCU_X hn) (spCU_w hn ι ρ y₀)) = 1 := by
  have hZ : spCU_z hn ι ρ y₀ = ∑ v : K, ι v ^ (Nat.card K - 1 - 1) •
      ρ (elt (.negativeLong (⟨1, by omega⟩ : Fin n)) v) y₀ := rfl
  have hiff : ∀ t v : K, f (ρ ((spCU_X hn * elt (.negativeLong (⟨0, by omega⟩ : Fin n)) t) *
        elt (.negativeLong (⟨1, by omega⟩ : Fin n)) v) y₀) =
      (1 + ι t) ^ (Nat.card K - 1) * (1 + ι v) ^ (Nat.card K - 1) := by
    intro t v
    simpa only [spCU_X, mul_assoc] using
      form_long_mul_long (n := n) (by omega) ι ht hf hfy hχ hμ t v
  have hmain := spCU_f_sum_factor ρ (spCU_X hn)
    (fun t : K => elt (.negativeLong (⟨0, by omega⟩ : Fin n)) t)
    (fun v : K => elt (.negativeLong (⟨1, by omega⟩ : Fin n)) v) y₀ (spCU_z hn ι ρ y₀) f
    (fun t : K => ι t ^ (Nat.card K - 1 - 1)) (fun v : K => ι v ^ (Nat.card K - 1 - 1))
    (fun t : K => (1 + ι t) ^ (Nat.card K - 1)) (fun v : K => (1 + ι v) ^ (Nat.card K - 1))
    hZ hiff
  have hS : (∑ t : K, ι t ^ (Nat.card K - 1 - 1) * (1 + ι t) ^ (Nat.card K - 1)) = 1 := by
    have hKsum : (∑ t : K, t ^ (Nat.card K - 1 - 1) * (1 + t) ^ (Nat.card K - 1)) = 1 := by
      rw [sum_pow_mul_one_add_pow (K := K) (j := 1) (c := Nat.card K - 1) le_rfl
        (show 1 + 1 < Nat.card K by omega) (show Nat.card K - 1 < Nat.card K by omega)]
      rw [Nat.choose_one_right, spCU_natCard_sub_one_cast_eq_one]
      exact CharTwo.neg_eq 1
    calc (∑ t : K, ι t ^ (Nat.card K - 1 - 1) * (1 + ι t) ^ (Nat.card K - 1))
        = ι (∑ t : K, t ^ (Nat.card K - 1 - 1) * (1 + t) ^ (Nat.card K - 1)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [map_mul, map_pow, map_add, map_one]
      _ = 1 := by rw [hKsum, map_one]
  rw [spCU_w, hmain, hS]
  simp

private theorem spCU_ne_zero {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (hK : 4 ≤ Nat.card K) {k : Type} [Field k] [CharP k 2] (ι : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) {y₀ : V}
    {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1)
    (hμ : μ ⟨n - 1, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨n - 1, by omega⟩ : Fin n)) :
    spCU_w hn ι ρ y₀ ≠ 0 := by
  obtain ⟨f, hf, hfy⟩ := (spCurtisDatum n K).exists_form hρ ht.1 ht.2.1
  have hone := spCU_f_w_eq_one hn hK ι ht hf hfy hχ hμ
  intro h0
  simp only [h0, map_zero] at hone
  exact zero_ne_one hone

private theorem spCU_e_zero {n : ℕ} (hn : 3 ≤ n) :
    ∀ a : Fin n, 2 ≤ a.val → spCU_e hn a = 0 := by
  intro a ha
  have h1 : a ≠ (⟨1, by omega⟩ : Fin n) := by
    intro h
    rw [h] at ha
    simp at ha
  have h0 : a ≠ (⟨0, by omega⟩ : Fin n) := by
    intro h
    rw [h] at ha
    simp at ha
  simp [spCU_e, stdVec_apply_negativeLong, h1, h0]

private theorem spCU_e_coord_zero {n : ℕ} (hn : 3 ≤ n) :
    spCU_e hn (⟨0, by omega⟩ : Fin n) = -2 := by
  simp [spCU_e, stdVec_apply_negativeLong]

private theorem spCU_e_coord_one {n : ℕ} (hn : 3 ≤ n) :
    spCU_e hn (⟨1, by omega⟩ : Fin n) = -2 := by
  simp [spCU_e, stdVec_apply_negativeLong]

private theorem spCU_not_dvd_neg_two {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) : ¬ ((Nat.card K : ℤ) - 1) ∣ (-2 : ℤ) := by
  intro h
  have h3 : (3 : ℤ) ≤ (Nat.card K : ℤ) - 1 := by
    have : (4 : ℤ) ≤ Nat.card K := by exact_mod_cast hK
    omega
  have hb : (Nat.card K : ℤ) - 1 ≤ 2 := by
    have := Int.le_abs_of_dvd (a := (Nat.card K : ℤ) - 1) (b := -2) (by norm_num) h
    simpa using this
  omega

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence in
theorem four_le_finrank_of_chi_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (hK : 4 ≤ Nat.card K) {k : Type} [Field k] [CharP k 2] (ι : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) {y₀ : V}
    {χ : StatedSp n K → k} {μ : Fin n → k} (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1)
    (hμ : μ ⟨n - 1, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨n - 1, by omega⟩ : Fin n))
    {y : StatedSp n K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hWne : spCU_w hn ι ρ y₀ ≠ 0 := spCU_ne_zero hn hK ι hρ ht hχ hμ
  have hW : spCU_w hn ι ρ y₀ ∈ weightSpace (ρ.comp (diagHom n K))
      (spTorusChar ι (spCU_e hn)) := spCU_weight hn hK ι ht hχ
  refine four_le_finrank_range_sub_one_of_weight (e := spCU_e hn) hn ι ρ
    (spCU_e_zero hn)
    (by
      rw [spCU_e_coord_zero hn]
      exact spCU_not_dvd_neg_two (K := K) hK)
    (by
      rw [spCU_e_coord_one hn]
      exact spCU_not_dvd_neg_two (K := K) hK)
    hWne hW hy hy1

end CFSG.LocalAnalysis.WeakClosure81
