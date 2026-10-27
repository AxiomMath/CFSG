module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Inv
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Roots

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

@[expose] def idxZeroE6 : Fin Tag.E6.rank := (0 : Fin 6)

@[expose] def yE6 : Fin Tag.E6.rank → ℤ := ![4, 3, 5, 6, 4, 2]

theorem cartan_mulVec_yE6 : Tag.cartan Tag.E6 *ᵥ yE6 = ![3, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem iform_comm_E6 (x y : Fin Tag.E6.rank → ℤ) : iform x y = iform y x := by
  simp only [iform_eq_E6, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [cartan_symmetric_E6 j i]; ring

theorem iform_yE6_right (d : Fin Tag.E6.rank → ℤ) : iform d yE6 = d idxZeroE6 * 3 := by
  rw [iform_eq_E6, cartan_mulVec_yE6]
  change ∑ i : Fin 6, d i * ![3, 0, 0, 0, 0, 0] i = d (0 : Fin 6) * 3
  simp [Fin.sum_univ_six]

theorem iform_add_left_E6 (x x' y : Fin Tag.E6.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp only [iform_eq_E6, add_dotProduct]

theorem iform_smul_left_E6 (c : ℤ) (x y : Fin Tag.E6.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform_eq_E6, smul_dotProduct, smul_eq_mul]

theorem iform_sub_left_E6 (x x' y : Fin Tag.E6.rank → ℤ) :
    iform (x - x') y = iform x y - iform x' y := by
  simp only [iform_eq_E6, sub_dotProduct]

theorem iform_right_neg_E6 (x y : Fin Tag.E6.rank → ℤ) : iform x (-y) = -iform x y := by
  simp only [iform_eq_E6, mulVec_neg, dotProduct_neg]

theorem iform_zero_left_E6 (y : Fin Tag.E6.rank → ℤ) : iform 0 y = 0 := by
  simp [iform_eq_E6]

theorem iform_single_left_E6 (i : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ) :
    iform (Pi.single i 1) y = (Tag.cartan Tag.E6 *ᵥ y) i := by
  simp [iform_eq_E6, single_dotProduct]

theorem theta_sub_self_neg
    {θ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ)} (hinv : ∀ v, θ (θ v) = v)
    (x : Fin Tag.E6.rank → ℤ) :
    θ (θ x - x) = -(θ x - x) := by
  rw [map_sub, hinv]
  abel

theorem exists_rel_of_fixed_five
    {θ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ)} (hinv : ∀ v, θ (θ v) = v)
    {f : Fin 5 → Fin Tag.E6.rank → ℤ} (hf : ∀ i, θ (f i) = f i) (hli : LinearIndependent ℤ f)
    (x y : Fin Tag.E6.rank → ℤ) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a • (θ x - x) + b • (θ y - y) = 0 := by
  classical
  have hnli : ¬ LinearIndependent ℤ (Sum.elim f ![θ x - x, θ y - y]) := by
    intro h
    have := h.fintype_card_le_finrank
    have h6 : Tag.E6.rank = 6 := rfl
    simp [h6] at this
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnli
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hc
  simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hθF : θ (∑ i, c (Sum.inl i) • f i) = ∑ i, c (Sum.inl i) • f i := by
    simp only [map_sum, map_smul, hf]
  have h2 := congrArg θ hc
  rw [map_add, map_add, hθF, map_smul, map_smul, theta_sub_self_neg hinv,
    theta_sub_self_neg hinv, map_zero] at h2
  have h3 : ∑ i, c (Sum.inl i) • f i = 0 := by
    ext k
    have e1 := congrFun hc k
    have e2 := congrFun h2 k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at e1 e2
    simp only [Pi.zero_apply]
    linarith
  have h4 : ∀ i, c (Sum.inl i) = 0 :=
    Fintype.linearIndependent_iff.1 hli (fun i => c (Sum.inl i)) h3
  refine ⟨c (Sum.inr 0), c (Sum.inr 1), ?_, by rwa [h3, zero_add] at hc⟩
  rcases i₀ with i | k
  · exact absurd (h4 i) hi₀
  · fin_cases k
    · exact Or.inl hi₀
    · exact Or.inr hi₀

theorem star_identity_E6
    {θ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ)} (hinv : ∀ v, θ (θ v) = v)
    (hiso : ∀ x y, iform (θ x) (θ y) = iform x y)
    {f : Fin 5 → Fin Tag.E6.rank → ℤ} (hf : ∀ i, θ (f i) = f i) (hli : LinearIndependent ℤ f)
    {e : Fin Tag.E6.rank → ℤ} (hd : θ e - e ≠ 0) (x : Fin Tag.E6.rank → ℤ) :
    iform (θ e - e) (θ e - e) • (θ x - x) = (-2 * iform x (θ e - e)) • (θ e - e) := by
  obtain ⟨a, b, hab, hrel⟩ := exists_rel_of_fixed_five hinv hf hli x e
  have hθd : θ (θ e - e) = -(θ e - e) := theta_sub_self_neg hinv e
  have h1 : iform (θ x) (θ e - e) = -iform x (θ e - e) := by
    have h := hiso x (θ e - e)
    rw [hθd, iform_right_neg_E6] at h
    linarith
  have hp : iform (θ x - x) (θ e - e) = -2 * iform x (θ e - e) := by
    rw [iform_sub_left_E6, h1]
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    rcases hab with h | h
    · exact h rfl
    · apply hd
      simp only [zero_smul, zero_add] at hrel
      exact (smul_eq_zero.1 hrel).resolve_left h
  have hS : a * (-2 * iform x (θ e - e)) + b * iform (θ e - e) (θ e - e) = 0 := by
    have h := congrArg (fun z => iform z (θ e - e)) hrel
    simp only [iform_add_left_E6, iform_smul_left_E6, iform_zero_left_E6, hp] at h
    exact h
  ext k
  have hk := congrFun hrel k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply] at hk ⊢
  have h : a * (iform (θ e - e) (θ e - e) * (θ x k - x k) -
      (-2 * iform x (θ e - e)) * (θ e k - e k)) = 0 := by
    linear_combination (iform (θ e - e) (θ e - e)) * hk - (θ e k - e k) * hS
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left ha)

theorem false_of_claimF_E6
    {θ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ)} (hinv : ∀ v, θ (θ v) = v)
    (hiso : ∀ x y, iform (θ x) (θ y) = iform x y) (hmod : ¬ (3 : ℤ) ∣ (θ yE6 - yE6) idxZeroE6)
    {f : Fin 5 → Fin Tag.E6.rank → ℤ} (hf : ∀ i, θ (f i) = f i) (hli : LinearIndependent ℤ f)
    {e : Fin Tag.E6.rank → ℤ} (hd : θ e - e ≠ 0)
    (hF : ¬ (3 : ℤ) ∣ iform (θ e - e) (θ e - e) ∨
      ∃ i, ¬ (3 : ℤ) ∣ (Tag.cartan Tag.E6 *ᵥ (θ e - e)) i) : False := by
  have key := star_identity_E6 hinv hiso hf hli hd
  by_cases hn : (3 : ℤ) ∣ iform (θ e - e) (θ e - e)
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (3 : ℤ) ∣ (Tag.cartan Tag.E6 *ᵥ (θ e - e)) i := by
      rcases hF with h | h
      · exact absurd hn h
      · exact h
    have hk : ∀ k, (3 : ℤ) ∣ (θ e - e) k := by
      intro k
      have h := congrFun (key (Pi.single i 1)) k
      simp only [Pi.smul_apply, smul_eq_mul, iform_single_left_E6] at h
      have h3 : (3 : ℤ) ∣ (-2 * (Tag.cartan Tag.E6 *ᵥ (θ e - e)) i) * (θ e - e) k := by
        rw [← h]
        exact Dvd.dvd.mul_right hn _
      rcases Int.prime_three.dvd_or_dvd h3 with h4 | h4
      · exfalso
        apply hi
        omega
      · exact h4
    exact hi (by
      simp only [mulVec, dotProduct]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hk k) _)
  · have h := congrFun (key yE6) idxZeroE6
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [iform_comm_E6 yE6 (θ e - e), iform_yE6_right] at h
    have h3 : (3 : ℤ) ∣ iform (θ e - e) (θ e - e) * (θ yE6 - yE6) idxZeroE6 := by
      rw [h]
      exact ⟨-2 * (θ e - e) idxZeroE6 * (θ e - e) idxZeroE6, by ring⟩
    rcases Int.prime_three.dvd_or_dvd h3 with h4 | h4
    · exact absurd h4 hn
    · exact hmod h4

theorem not_linearIndependent_fixed_five_E6
    {θ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ)} (hinv : ∀ v, θ (θ v) = v)
    (hiso : ∀ x y, iform (θ x) (θ y) = iform x y) (hroot : ∀ j, θ (Pi.single j 1) ∈ roots72)
    (hmod : ¬ (3 : ℤ) ∣ (θ yE6 - yE6) idxZeroE6)
    {f : Fin 5 → Fin Tag.E6.rank → ℤ} (hf : ∀ i, θ (f i) = f i) :
    ¬ LinearIndependent ℤ f := by
  intro hli
  obtain ⟨j, hj⟩ : ∃ j, θ (Pi.single j 1) ≠ Pi.single j 1 := by
    by_contra! h
    have hθ : θ = LinearMap.id := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simpa using h j
    exact hmod (by simp [hθ])
  exact false_of_claimF_E6 hinv hiso hmod hf hli (sub_ne_zero.2 hj)
    (claimF_check j _ (hroot j) hj)

end CFSG.StandardType.KGCentE6
