module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Tensor3Aux

variable {K : Type} [Field K]

theorem b6c_act0_apply (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) (a b c : Fin 2) :
    tensor3Act0 A T a b c = A a 0 * T 0 b c + A a 1 * T 1 b c := by
  simp [tensor3Act0, Fin.sum_univ_two]

theorem b6c_act1_apply (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) (a b c : Fin 2) :
    tensor3Act1 A T a b c = A b 0 * T a 0 c + A b 1 * T a 1 c := by
  simp [tensor3Act1, Fin.sum_univ_two]

theorem b6c_act2_apply (A : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) (a b c : Fin 2) :
    tensor3Act2 A T a b c = A c 0 * T a b 0 + A c 1 * T a b 1 := by
  simp [tensor3Act2, Fin.sum_univ_two]

theorem b6c_act1_mul (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act1 (A * B) T = tensor3Act1 A (tensor3Act1 B T) := by
  funext a b c
  simp only [b6c_act1_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem b6c_act2_mul (A B : Matrix (Fin 2) (Fin 2) K) (T : Tensor3 K) :
    tensor3Act2 (A * B) T = tensor3Act2 A (tensor3Act2 B T) := by
  funext a b c
  simp only [b6c_act2_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem b6c_unit1 (Φ : Tensor3 K ≃ₗ[K] Tensor3 K)
    (h1 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act1 A T) = tensor3Act1 A (Φ T)) (b : Fin 2) :
    ∃ E : Matrix (Fin 2) (Fin 2) K, (∀ T, Φ (tensor3Act1 E T) = tensor3Act1 E (Φ T)) ∧
      ∀ T a y z, tensor3Act1 E T a y z = if y = 0 then T a b z else 0 := by
  have hA : ∀ T : Tensor3 K,
      Φ (tensor3Act1 !![0, 1; 0, 0] T) = tensor3Act1 !![0, 1; 0, 0] (Φ T) := by
    intro T
    have h := h1 !![1, 1; 0, 1] (by simp [Matrix.det_fin_two]) T
    have e : ∀ S : Tensor3 K,
        tensor3Act1 !![1, 1; 0, 1] S = S + tensor3Act1 !![0, 1; 0, 0] S := by
      intro S
      funext a y z
      simp only [b6c_act1_apply, Pi.add_apply]
      fin_cases y <;> simp
    rw [e, e, map_add] at h
    exact add_left_cancel h
  have hB : ∀ T : Tensor3 K,
      Φ (tensor3Act1 !![0, 0; 1, 0] T) = tensor3Act1 !![0, 0; 1, 0] (Φ T) := by
    intro T
    have h := h1 !![1, 0; 1, 1] (by simp [Matrix.det_fin_two]) T
    have e : ∀ S : Tensor3 K,
        tensor3Act1 !![1, 0; 1, 1] S = S + tensor3Act1 !![0, 0; 1, 0] S := by
      intro S
      funext a y z
      simp only [b6c_act1_apply, Pi.add_apply]
      fin_cases y <;> simp <;> ring
    rw [e, e, map_add] at h
    exact add_left_cancel h
  fin_cases b
  · refine ⟨!![0, 1; 0, 0] * !![0, 0; 1, 0], fun T => ?_, fun T a y z => ?_⟩
    · rw [b6c_act1_mul, b6c_act1_mul, hA, hB]
    · rw [b6c_act1_mul]
      simp only [b6c_act1_apply]
      fin_cases y <;> simp
  · refine ⟨!![0, 1; 0, 0], hA, fun T a y z => ?_⟩
    rw [b6c_act1_apply]
    fin_cases y <;> simp

theorem b6c_unit2 (Φ : Tensor3 K ≃ₗ[K] Tensor3 K)
    (h2 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act2 A T) = tensor3Act2 A (Φ T)) (c : Fin 2) :
    ∃ E : Matrix (Fin 2) (Fin 2) K, (∀ T, Φ (tensor3Act2 E T) = tensor3Act2 E (Φ T)) ∧
      ∀ T a y z, tensor3Act2 E T a y z = if z = 0 then T a y c else 0 := by
  have hA : ∀ T : Tensor3 K,
      Φ (tensor3Act2 !![0, 1; 0, 0] T) = tensor3Act2 !![0, 1; 0, 0] (Φ T) := by
    intro T
    have h := h2 !![1, 1; 0, 1] (by simp [Matrix.det_fin_two]) T
    have e : ∀ S : Tensor3 K,
        tensor3Act2 !![1, 1; 0, 1] S = S + tensor3Act2 !![0, 1; 0, 0] S := by
      intro S
      funext a y z
      simp only [b6c_act2_apply, Pi.add_apply]
      fin_cases z <;> simp
    rw [e, e, map_add] at h
    exact add_left_cancel h
  have hB : ∀ T : Tensor3 K,
      Φ (tensor3Act2 !![0, 0; 1, 0] T) = tensor3Act2 !![0, 0; 1, 0] (Φ T) := by
    intro T
    have h := h2 !![1, 0; 1, 1] (by simp [Matrix.det_fin_two]) T
    have e : ∀ S : Tensor3 K,
        tensor3Act2 !![1, 0; 1, 1] S = S + tensor3Act2 !![0, 0; 1, 0] S := by
      intro S
      funext a y z
      simp only [b6c_act2_apply, Pi.add_apply]
      fin_cases z <;> simp <;> ring
    rw [e, e, map_add] at h
    exact add_left_cancel h
  fin_cases c
  · refine ⟨!![0, 1; 0, 0] * !![0, 0; 1, 0], fun T => ?_, fun T a y z => ?_⟩
    · rw [b6c_act2_mul, b6c_act2_mul, hA, hB]
    · rw [b6c_act2_mul]
      simp only [b6c_act2_apply]
      fin_cases z <;> simp
  · refine ⟨!![0, 1; 0, 0], hA, fun T a y z => ?_⟩
    rw [b6c_act2_apply]
    fin_cases z <;> simp

theorem b6c_slice (Φ : Tensor3 K ≃ₗ[K] Tensor3 K)
    (h1 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act1 A T) = tensor3Act1 A (Φ T))
    (h2 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act2 A T) = tensor3Act2 A (Φ T)) (b c : Fin 2) :
    ∃ U : Tensor3 K → Tensor3 K, (∀ T, Φ (U T) = U (Φ T)) ∧
      ∀ V a y z, U V a y z = if y = 0 ∧ z = 0 then V a b c else 0 := by
  obtain ⟨E1, hE1, hE1'⟩ := b6c_unit1 Φ h1 b
  obtain ⟨E2, hE2, hE2'⟩ := b6c_unit2 Φ h2 c
  refine ⟨fun T => tensor3Act2 E2 (tensor3Act1 E1 T), fun T => ?_, fun V a y z => ?_⟩
  · rw [hE2, hE1]
  · simp only [hE2', hE1']
    by_cases hz : z = 0 <;> by_cases hy : y = 0 <;> simp [hz, hy]

end Tensor3Aux

theorem tensor3_commutant {K : Type} [Field K] [CharP K 2] (Φ : Tensor3 K ≃ₗ[K] Tensor3 K)
    (h1 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act1 A T) = tensor3Act1 A (Φ T))
    (h2 : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ T,
      Φ (tensor3Act2 A T) = tensor3Act2 A (Φ T))
    (hform : ∀ T, tensor3Form (Φ T) = tensor3Form T) :
    ∃ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 ∧ ∀ T, Φ T = tensor3Act0 B T := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 2 → Tensor3 K, ∀ i x y z,
      δ i x y z = if x = i ∧ y = 0 ∧ z = 0 then 1 else 0 :=
    ⟨fun i x y z => if x = i ∧ y = 0 ∧ z = 0 then 1 else 0, fun _ _ _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 2) (Fin 2) K, ∀ a a', B a a' = Φ (δ a') a 0 0 :=
    ⟨Matrix.of fun a a' => Φ (δ a') a 0 0, fun _ _ => rfl⟩
  have hΦ : ∀ T, Φ T = tensor3Act0 B T := by
    intro T
    funext a b c
    obtain ⟨U, hU, hU'⟩ := b6c_slice Φ h1 h2 b c
    have e1 : Φ T a b c = U (Φ T) a 0 0 := by rw [hU']; simp
    have hUT : U T = T 0 b c • δ 0 + T 1 b c • δ 1 := by
      funext x y z
      simp only [hU', Pi.add_apply, Pi.smul_apply, hδ, smul_eq_mul]
      fin_cases x <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;> simp [hy, hz]
    rw [e1, ← hU, hUT, map_add, map_smul, map_smul, b6c_act0_apply, hB, hB]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨B, ?_, hΦ⟩
  have hT := hform (fun x y z => if (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) then 1 else 0)
  rw [hΦ] at hT
  simp [tensor3Form, b6c_act0_apply] at hT
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add]
  exact hT

theorem centY {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z)
    (θ : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K) (hθ : ∀ e, AM.M₀.Qf e = tensor3Form (θ e))
    {Y Fb Fc : Subgroup G} (hQY : Q ≤ Y)
    (hY : FactorAct AM θ Y tensor3Act0) (hFb : FactorAct AM θ Fb tensor3Act1)
    (hFc : FactorAct AM θ Fc tensor3Act2) {x : G} (hx : x ∈ H0 M Z)
    (hb : ∀ f ∈ Fb, ⁅x, f⁆ ∈ Q) (hc : ∀ f ∈ Fc, ⁅x, f⁆ ∈ Q) : x ∈ Y := by
  set x' : ↥(H0 M Z) := ⟨x, hx⟩ with hx'
  have hcomm : ∀ f : ↥(H0 M Z), ⁅x, (f : G)⁆ ∈ Q →
      ∀ e, AM.φ x' (AM.φ f e) = AM.φ f (AM.φ x' e) := by
    intro f hf e
    have h1 : AM.φ ⁅x', f⁆ = 1 := (AM.φ_ker _).2 hf
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact LinearEquiv.congr_fun h1 e
  let Φ : Tensor3 AM.K ≃ₗ[AM.K] Tensor3 AM.K := θ.symm.trans ((AM.φ x').trans θ)
  have hΦ : ∀ e, Φ (θ e) = θ (AM.φ x' e) := by
    intro e
    simp [Φ]
  have hΦ1 : ∀ A : Matrix (Fin 2) (Fin 2) AM.K, A.det = 1 → ∀ T,
      Φ (tensor3Act1 A T) = tensor3Act1 A (Φ T) := by
    intro A hA T
    obtain ⟨f, hf, hfe⟩ := hFb.2 A hA
    obtain ⟨e, rfl⟩ := θ.surjective T
    rw [← hfe e, hΦ, hΦ, ← hfe (AM.φ x' e), hcomm f (hb _ hf) e]
  have hΦ2 : ∀ A : Matrix (Fin 2) (Fin 2) AM.K, A.det = 1 → ∀ T,
      Φ (tensor3Act2 A T) = tensor3Act2 A (Φ T) := by
    intro A hA T
    obtain ⟨f, hf, hfe⟩ := hFc.2 A hA
    obtain ⟨e, rfl⟩ := θ.surjective T
    rw [← hfe e, hΦ, hΦ, ← hfe (AM.φ x' e), hcomm f (hc _ hf) e]
  have hΦform : ∀ T, tensor3Form (Φ T) = tensor3Form T := by
    intro T
    obtain ⟨e, rfl⟩ := θ.surjective T
    rw [hΦ, ← hθ, AM.φ_Qf x' e, hθ]
  obtain ⟨B, hB, hΦB⟩ := tensor3_commutant Φ hΦ1 hΦ2 hΦform
  obtain ⟨y, hyY, hyθ⟩ := hY.2 B hB
  have hyx : AM.φ y = AM.φ x' := by
    ext e
    apply θ.injective
    rw [hyθ, ← hΦB, hΦ]
  have h1 : AM.φ (x'⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hq : x⁻¹ * (y : G) ∈ Y := hQY ((AM.φ_ker _).1 h1)
  have hxy : x = (y : G) * (x⁻¹ * (y : G))⁻¹ := by group
  rw [hxy]
  exact Y.mul_mem hyY (Y.inv_mem hq)

end CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

end
