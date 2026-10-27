module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.RankTwoClassical
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

private theorem s16g_commutator_sl2 (hK : 4 ≤ Nat.card K) : commutator SL(2, K) = ⊤ := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset K).card by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact (CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩).commutator_eq_top

theorem s16g_rhoTwo_mul_rhoOne_eq_one [CharP K 2] {A B : SL(2, K)}
    (h : rhoTwoMat A * rhoOneMat B = 1) : A = 1 ∧ B = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdetA := A.2
  rw [det_fin_two] at hdetA
  have e : ∀ i j, (rhoTwoMat A * rhoOneMat B) i j =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j := fun i j => by rw [h]
  have E1 := e (.inl 0) (.inl 0)
  have E2 := e (.inl 0) (.inl 1)
  have E3 := e (.inl 1) (.inl 0)
  have E4 := e (.inl 1) (.inl 1)
  have E5 := e (.inl 0) (.inr 1)
  have E6 := e (.inr 0) (.inl 1)
  have E7 := e (.inr 1) (.inr 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, rhoTwoMat_apply, rhoOneMat_apply,
    adjugate_fin_two, swapM, Matrix.one_apply] at E1 E2 E3 E4 E5 E6 E7
  have hb0 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun hb => by
    rw [hb, mul_zero] at E1
    exact zero_ne_one E1
  have ha01 := E2.resolve_right hb0
  have ha10 := E3.resolve_right hb0
  have haa : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (A : Matrix (Fin 2) (Fin 2) K) 1 1 :=
    mul_right_cancel₀ hb0 (E1.trans E4.symm)
  have hsq : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination hdetA + (A : Matrix (Fin 2) (Fin 2) K) 0 0 * haa +
      (A : Matrix (Fin 2) (Fin 2) K) 1 0 * ha01
  have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h3 : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hsq + (1 - (A : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
  have ha0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by rw [ha]; exact one_ne_zero
  have hb00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [ha, one_mul] at E1
    exact E1
  have hb01 := E5.resolve_left ha0
  have hb10 := E6.resolve_left (by rw [← haa]; exact ha0)
  have hb11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [ha, one_mul] at E7
    exact E7
  constructor
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    revert i j
    simp only [Fin.forall_fin_two]
    simp [ha, ha01, ha10, ← haa]
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    revert i j
    simp only [Fin.forall_fin_two]
    simp [hb00, hb01, hb10, hb11]

theorem s16g_rhoTwo_mul_rhoOne_fix [CharP K 2] (A : SL(2, K)) :
    (rhoTwoMat A * rhoOneMat (Matrix.SpecialLinearGroup.transpose A⁻¹)) *ᵥ
        (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) =
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
  have hdet := A.2
  rw [det_fin_two] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [← Matrix.mulVec_mulVec]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, rhoTwoMat_apply,
      rhoOneMat_apply, Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
      adjugate_fin_two, swapM]
  · linear_combination hdet
  · ring
  · linear_combination hdet +
      ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1) * h2
  · linear_combination
      (-((A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 0 0)) * h2

private theorem s16g_transpose_inv_pow {A : SL(2, K)} {n : ℕ} (h : A ^ n = 1) :
    (Matrix.SpecialLinearGroup.transpose A⁻¹) ^ n = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_transpose,
    ← Matrix.transpose_pow, ← Matrix.SpecialLinearGroup.coe_pow, inv_pow, h, inv_one]
  simp

theorem s16g_omega_blocks [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
    [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ x y : Matrix.GeneralLinearGroup ι K, x ∈ StatedOmega Q ∧ y ∈ StatedOmega Q ∧
      Commute x y ∧ orderOf x = p ∧ orderOf y = p ∧ y ∉ Subgroup.zpowers x ∧
      ∀ v : ι → K, (∀ b, v (oe (.inr b)) = 0) →
        (x : Matrix ι ι K) *ᵥ v = v ∧ (y : Matrix ι ι K) *ᵥ v = v := by
  have hSL := s16g_commutator_sl2 hK
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  refine ⟨(oRhoTwo oe hQ hSL g : GL ι K), (oRhoOne oe hQ hSL g : GL ι K),
    (oRhoTwo oe hQ hSL g).2, (oRhoOne oe hQ hSL g).2,
    congrArg Subtype.val (oRhoOne_commute_oRhoTwo (hQ := hQ) (hSL := hSL) g g).symm, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_injective _ oRhoTwo_injective g, hg]
  · rw [Subgroup.orderOf_coe, orderOf_injective _ oRhoOne_injective g, hg]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : oRhoTwo oe hQ hSL (g ^ k) = oRhoOne oe hQ hSL g := by
      apply Subtype.ext
      rw [map_zpow, Subgroup.coe_zpow]
      exact hk
    have h2 := congrArg (fun z : StatedOmega Q => ((z : GL ι K) : Matrix ι ι K)) h1
    simp only [coe_oRhoTwo, coe_oRhoOne] at h2
    have h3 := (oblk_injective h2).2
    have h4 : rhoTwoMat ((g ^ k)⁻¹) * rhoOneMat g = 1 := by
      rw [← h3, ← map_mul, inv_mul_cancel, map_one]
    rw [(s16g_rhoTwo_mul_rhoOne_eq_one h4).2, orderOf_one] at hg
    exact hp.one_lt.ne hg
  · intro v hv
    have key : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, oblk oe 1 X *ᵥ v = v := by
      intro X
      funext i
      obtain ⟨j, rfl⟩ := oe.surjective i
      rcases j with a | b
      · rw [oblk_mulVec_inl, Matrix.one_mulVec]
      · rw [oblk_mulVec_inr, show (fun b' => v (oe (.inr b'))) = 0 from funext hv,
          Matrix.mulVec_zero, hv b]
        rfl
    exact ⟨key _, key _⟩

theorem s16g_omega_fixed_singular [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K}
    {Q₂ : (ι₂ → K) → K}
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K ^ 2 - 1)
    {u₂ : ι₂ → K} (hu₂ : Q₂ u₂ = 1) :
    ∃ g : Matrix.GeneralLinearGroup ι K, g ∈ StatedOmega Q ∧ orderOf g = p ∧
      ∃ u : ι → K, u ≠ 0 ∧ Q u = 0 ∧ (g : Matrix ι ι K) *ᵥ u = u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSL := s16g_commutator_sl2 hK
  obtain ⟨A, hA⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hA
    exact hp.one_lt.ne hA
  have hApow : A ^ p = 1 := by rw [← hA]; exact pow_orderOf_eq_one A
  set B : SL(2, K) := Matrix.SpecialLinearGroup.transpose A⁻¹ with hB
  have hcomm : Commute (oRhoTwo oe hQ hSL A) (oRhoOne oe hQ hSL B) :=
    (oRhoOne_commute_oRhoTwo (hQ := hQ) (hSL := hSL) A B).symm
  set g : StatedOmega Q := oRhoTwo oe hQ hSL A * oRhoOne oe hQ hSL B with hg
  have hcoe : ((g : GL ι K) : Matrix ι ι K) = oblk oe 1 (rhoTwoMat A * rhoOneMat B) := by
    change oblk oe 1 (rhoTwoMat A) * oblk oe 1 (rhoOneMat B) = _
    rw [oblk_mul, Matrix.one_mul]
  have hpow : g ^ p = 1 := by
    rw [hg, hcomm.mul_pow, ← map_pow, ← map_pow, hApow, s16g_transpose_inv_pow hApow, map_one,
      map_one, one_mul]
  have hg1 : g ≠ 1 := by
    intro h
    have h1 := congrArg (fun z : StatedOmega Q => ((z : GL ι K) : Matrix ι ι K)) h
    simp only [hcoe] at h1
    have h2 := (oblk_injective (h1.trans (oblk_one (oe := oe)).symm)).2
    exact hA1 (s16g_rhoTwo_mul_rhoOne_eq_one h2).1
  refine ⟨(g : GL ι K), g.2, by rw [Subgroup.orderOf_coe]; exact orderOf_eq_prime hpow hg1, ?_⟩
  let w₀ : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1
  let u : ι → K := fun i => Sum.elim u₂ w₀ (oe.symm i)
  have hu1 : ∀ a, u (oe (.inl a)) = u₂ a := fun a => by simp [u]
  have hu2 : ∀ b, u (oe (.inr b)) = w₀ b := fun b => by simp [u]
  have e1 : (fun a => u (oe (.inl a))) = u₂ := funext hu1
  have e2 : (fun b => u (oe (.inr b))) = w₀ := funext hu2
  refine ⟨u, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun h (oe (.inr (.inl 0)))
    rw [hu2] at h1
    simp [w₀] at h1
  · have hq : StatedQuadPlus 2 K w₀ = 1 := by
      show ∑ i : Fin 2, w₀ (.inl i) * w₀ (.inr i) = 1
      simp [w₀, Fin.sum_univ_two]
    rw [hQ, e1, e2, hu₂, hq]
    exact CharTwo.add_self_eq_zero 1
  · funext i
    obtain ⟨j, rfl⟩ := oe.surjective i
    rw [hcoe]
    rcases j with a | b
    · rw [oblk_mulVec_inl, Matrix.one_mulVec]
    · rw [oblk_mulVec_inr, e2, s16g_rhoTwo_mul_rhoOne_fix A, hu2]

private theorem s16g_single_ne_zero_om {ι : Type} [DecidableEq ι] (i : ι) :
    (Pi.single i 1 : ι → K) ≠ 0 := fun h => by
  have h1 := congrFun h i
  simp at h1

theorem s16g_fixNc_statedOmegaPlus_two [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 3 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) :
    FixNc (StatedOmega (StatedQuadPlus m K)) p := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 0 < k := by omega
  obtain ⟨x, y, hx, hy, hxy, hox, hoy, hyx, hfix⟩ :=
    s16g_omega_blocks (plusOe k) (statedQuadPlus_plusOe k) hK hp hpK
  let u : Fin (k + 2) ⊕ Fin (k + 2) → K := Pi.single (plusOe k (.inl (.inl ⟨0, hk⟩))) 1
  have hsupp : ∀ b, u (plusOe k (.inr b)) = 0 := fun b =>
    Pi.single_eq_of_ne ((plusOe k).injective.ne Sum.inr_ne_inl) _
  have hQu : StatedQuadPlus (k + 2) K u = 0 := by
    have h : ∀ i : Fin (k + 2), u (Sum.inr i) = 0 := fun i => Pi.single_eq_of_ne Sum.inr_ne_inl _
    show ∑ i : Fin (k + 2), u (.inl i) * u (.inr i) = 0
    exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
  have hfixu := hfix u hsupp
  exact s16g_fixNc_of_fixed_pair_singular (CFSG.LieType.Universal.Spin.quadPlus (k + 2) K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (k + 2) K) _ hp hp2
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq hm hx hy hxy)
    hx hy hxy hox hoy hyx (s16g_single_ne_zero_om _)
    (by rw [CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hQu) hfixu.1 hfixu.2

theorem s16g_fixNc_statedOmegaMinus_two [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 4 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixNc (StatedOmega (StatedQuadMinus m K b c)) p := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hj : 0 < j := by omega
  obtain ⟨x, y, hx, hy, hxy, hox, hoy, hyx, hfix⟩ :=
    s16g_omega_blocks (minusOe j) (statedQuadMinus_minusOe j b c) hK hp hpK
  let u : Fin (j + 2) ⊕ Fin (j + 2) ⊕ Fin 2 → K := Pi.single (minusOe j (.inl (.inl ⟨0, hj⟩))) 1
  have hsupp : ∀ b, u (minusOe j (.inr b)) = 0 := fun b =>
    Pi.single_eq_of_ne ((minusOe j).injective.ne Sum.inr_ne_inl) _
  have hQu : StatedQuadMinus (j + 3) K b c u = 0 := by
    have h : ∀ i : Fin (j + 2) ⊕ Fin 2, u (Sum.inr i) = 0 := fun i =>
      Pi.single_eq_of_ne Sum.inr_ne_inl _
    show (∑ i : Fin (j + 2), u (.inl i) * u (.inr (.inl i))) + u (.inr (.inr 0)) ^ 2 +
      b * u (.inr (.inr 0)) * u (.inr (.inr 1)) + c * u (.inr (.inr 1)) ^ 2 = 0
    rw [h (.inr 0), h (.inr 1)]
    simp [h]
  have hfixu := hfix u hsupp
  exact s16g_fixNc_of_fixed_pair_singular (CFSG.LieType.Universal.Spin.quadMinus (j + 3) K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (j + 3) K hirr) _
    hp hp2
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega) hirr hx hy hxy)
    hx hy hxy hox hoy hyx (s16g_single_ne_zero_om _)
    (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hQu) hfixu.1 hfixu.2

theorem s16g_fixOrd_statedOmegaMinus_three [CharP K 2] (hK : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixOrd (StatedOmega (StatedQuadMinus 3 K b c)) p := by
  have hu₂ : StatedQuadMinus (0 + 1) K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) = 1 := by
    have h : ∀ v : Fin (0 + 1 - 1) ⊕ Fin (0 + 1 - 1) ⊕ Fin 2 → K,
        StatedQuadMinus (0 + 1) K b c v =
          (∑ i : Fin (0 + 1 - 1), v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
            b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 :=
      fun v => rfl
    rw [h]
    simp
  obtain ⟨g, hgΩ, hg, u, hu, hQu, hfix⟩ := s16g_omega_fixed_singular (minusOe 0)
    (statedQuadMinus_minusOe 0 b c) hK hp hpK hu₂
  exact s16g_fixOrd_of_fixed_singular (CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) _ hp hp2
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega) hirr hx hy hxy)
    hgΩ hg hu (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hQu) hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
