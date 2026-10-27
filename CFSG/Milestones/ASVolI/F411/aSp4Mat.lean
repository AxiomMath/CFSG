module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.ASVolI

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Sp4Mat

variable {K : Type} [Field K]

theorem burnsideF411a_sp_eq_of_proj_eq (p : ℕ) [Fact p.Prime] [CharP K p] {r : ℕ} (hr : 1 ≤ r)
    {g u : StatedSp r K} (m : ℕ) (hg : g ^ p ^ m = 1) (hu : u ^ p ^ m = 1)
    (h : proj r K g = proj r K u) : g = u := by
  have hz : g⁻¹ * u ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) :=
    QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hcen : ((g⁻¹ * u : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, hc⟩
  have hcomm : Commute g (g⁻¹ * u) :=
    Subtype.ext (Subgroup.mem_center_iff.mp hcen (g : GL (Fin r ⊕ Fin r) K))
  have hu' : u = g * (g⁻¹ * u) := by rw [mul_inv_cancel_left]
  have hzN : (g⁻¹ * u) ^ p ^ m = 1 := by
    have h2 := hcomm.mul_pow (p ^ m)
    rw [← hu', hu, hg, one_mul] at h2
    exact h2.symm
  have hcN : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (c ^ p ^ m) = 1 := by
    rw [map_pow, hc, ← Subgroup.coe_pow, hzN, Subgroup.coe_one]
  have hc1 : (c : K) ^ p ^ m = 1 := by
    have h3 := congrArg (fun x : GL (Fin r ⊕ Fin r) K =>
      (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl ⟨0, hr⟩) (Sum.inl ⟨0, hr⟩)) hcN
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq, Units.val_pow_eq_pow_val] at h3
    exact h3
  have hc2 : c = 1 := by
    have h0 : ((c : K) - 1) ^ p ^ m = 0 := by rw [sub_pow_char_pow, hc1, one_pow, sub_self]
    exact Units.ext
      (sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h0))
  have hz1 : g⁻¹ * u = 1 := by
    apply Subtype.ext
    rw [← hc, hc2, map_one]
    rfl
  rw [hu', hz1, mul_one]

theorem burnsideF411a_isPGroup_unipotent [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (r : ℕ) : IsPGroup p (unipotent r K) := by
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hk
  exact IsPGroup.of_card (n := k * r ^ 2) (by rw [card_unipotent, hk, pow_mul])

theorem burnsideF411a_sp_fix_of_fix [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : gsp 2 K) (σ : K ≃+* K)
    (hα : ∀ x ∈ projUnipotent 2 K, (conjAut 2 K A * fieldAut 2 K σ) x = x) :
    ∀ u ∈ unipotent 2 K, conjSp 2 K A (fieldSp 2 K σ u) = u := by
  intro u hu
  obtain ⟨m, hm⟩ := burnsideF411a_isPGroup_unipotent (K := K) p 2 ⟨u, hu⟩
  have hum : u ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine burnsideF411a_sp_eq_of_proj_eq p (by norm_num) m ?_ hum ?_
  · rw [← map_pow, ← map_pow, hum, map_one, map_one]
  · have h1 := hα _ (Subgroup.mem_map_of_mem (proj 2 K) hu)
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
    exact h1

theorem burnsideF411a_sp_intertwine {ι : Type*} [Fintype ι] [DecidableEq ι] {A : GL ι K}
    {X Y : Matrix ι ι K}
    (h : (A : Matrix ι ι K) * X * ((A⁻¹ : GL ι K) : Matrix ι ι K) = Y) :
    (A : Matrix ι ι K) * X = Y * (A : Matrix ι ι K) := by
  rw [← h, Matrix.mul_assoc _ ((A⁻¹ : GL ι K) : Matrix ι ι K), Units.inv_mul, Matrix.mul_one]

theorem burnsideF411a_sp4_inner_of_fix [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : gsp 2 K) (σ : K ≃+* K)
    (hα : ∀ x ∈ projUnipotent 2 K, (conjAut 2 K A * fieldAut 2 K σ) x = x) :
    ∃ g, conjAut 2 K A * fieldAut 2 K σ = MulAut.conj g := by
  have hfix := burnsideF411a_sp_fix_of_fix p A σ hα
  have hint : ∀ u ∈ unipotent 2 K,
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ) =
      ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro u hu
    have h1 := congrArg (fun x : StatedSp 2 K =>
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hfix u hu)
    simp only [coe_conjSp, Units.val_mul, coe_fieldSp] at h1
    exact burnsideF411a_sp_intertwine h1
  have h1 := hint _ (SymplecticFour.lam_mem_unipotent 1)
  have h2 := hint _ (SymplecticFour.tau_mem_unipotent (SymplecticFour.sym2_transpose (0 : K) 0 1))
  have h3 : ∀ t : K,
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (fromBlocks (SymplecticFour.unitri t) 0 0 (SymplecticFour.unitri (-t))ᵀ).map σ =
      fromBlocks (SymplecticFour.unitri t) 0 0 (SymplecticFour.unitri (-t))ᵀ *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := fun t => by
    rw [← SymplecticFour.coe_lam]
    exact hint _ (SymplecticFour.lam_mem_unipotent t)
  rw [SymplecticFour.coe_lam] at h1
  rw [SymplecticFour.coe_tau] at h2
  have hspec := multiplier_spec A
  generalize hM : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = M
    at h1 h2 h3 hspec
  have m10 : M (Sum.inl 1) (Sum.inl 0) = 0 := by
    have e : M (Sum.inl 0) (Sum.inl 0) * 1 + M (Sum.inl 0) (Sum.inl 1) * 0 +
        (M (Sum.inl 0) (Sum.inr 0) * 0 + M (Sum.inl 0) (Sum.inr 1) * 0) =
        1 * M (Sum.inl 0) (Sum.inl 0) + 1 * M (Sum.inl 1) (Sum.inl 0) +
        (0 * M (Sum.inr 0) (Sum.inl 0) + 0 * M (Sum.inr 1) (Sum.inl 0)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.unitri]
        using congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    linear_combination -e
  have m20 : M (Sum.inr 0) (Sum.inl 0) = 0 := by
    have e : M (Sum.inr 1) (Sum.inl 0) * 1 + M (Sum.inr 1) (Sum.inl 1) * 0 +
        (M (Sum.inr 1) (Sum.inr 0) * 0 + M (Sum.inr 1) (Sum.inr 1) * 0) =
        0 * M (Sum.inl 0) (Sum.inl 0) + 0 * M (Sum.inl 1) (Sum.inl 0) +
        (-1 * M (Sum.inr 0) (Sum.inl 0) + 1 * M (Sum.inr 1) (Sum.inl 0)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.unitri]
        using congrFun (congrFun h1 (Sum.inr 1)) (Sum.inl 0)
    linear_combination e
  have m11 : M (Sum.inl 0) (Sum.inl 0) = M (Sum.inl 1) (Sum.inl 1) := by
    have e : M (Sum.inl 0) (Sum.inl 0) * 1 + M (Sum.inl 0) (Sum.inl 1) * 1 +
        (M (Sum.inl 0) (Sum.inr 0) * 0 + M (Sum.inl 0) (Sum.inr 1) * 0) =
        1 * M (Sum.inl 0) (Sum.inl 1) + 1 * M (Sum.inl 1) (Sum.inl 1) +
        (0 * M (Sum.inr 0) (Sum.inl 1) + 0 * M (Sum.inr 1) (Sum.inl 1)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.unitri]
        using congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 1)
    linear_combination e
  have m22 : M (Sum.inr 0) (Sum.inr 0) = M (Sum.inr 1) (Sum.inr 1) := by
    have e : M (Sum.inr 1) (Sum.inl 0) * 0 + M (Sum.inr 1) (Sum.inl 1) * 0 +
        (M (Sum.inr 1) (Sum.inr 0) * 1 + M (Sum.inr 1) (Sum.inr 1) * -1) =
        0 * M (Sum.inl 0) (Sum.inr 0) + 0 * M (Sum.inl 1) (Sum.inr 0) +
        (-1 * M (Sum.inr 0) (Sum.inr 0) + 1 * M (Sum.inr 1) (Sum.inr 0)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.unitri]
        using congrFun (congrFun h1 (Sum.inr 1)) (Sum.inr 0)
    linear_combination e
  have m30 : M (Sum.inr 1) (Sum.inl 0) = 0 := by
    have e : M (Sum.inl 1) (Sum.inl 0) * 1 + M (Sum.inl 1) (Sum.inl 1) * 0 +
        (M (Sum.inl 1) (Sum.inr 0) * 0 + M (Sum.inl 1) (Sum.inr 1) * 0) =
        0 * M (Sum.inl 0) (Sum.inl 0) + 1 * M (Sum.inl 1) (Sum.inl 0) +
        (0 * M (Sum.inr 0) (Sum.inl 0) + 1 * M (Sum.inr 1) (Sum.inl 0)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.sym2]
        using congrFun (congrFun h2 (Sum.inl 1)) (Sum.inl 0)
    linear_combination -e
  have m33 : M (Sum.inl 1) (Sum.inl 1) = M (Sum.inr 1) (Sum.inr 1) := by
    have e : M (Sum.inl 1) (Sum.inl 0) * 0 + M (Sum.inl 1) (Sum.inl 1) * 1 +
        (M (Sum.inl 1) (Sum.inr 0) * 0 + M (Sum.inl 1) (Sum.inr 1) * 1) =
        0 * M (Sum.inl 0) (Sum.inr 1) + 1 * M (Sum.inl 1) (Sum.inr 1) +
        (0 * M (Sum.inr 0) (Sum.inr 1) + 1 * M (Sum.inr 1) (Sum.inr 1)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.sym2]
        using congrFun (congrFun h2 (Sum.inl 1)) (Sum.inr 1)
    linear_combination e
  have hJ : (Mᵀ * formJ 2 K * M) (Sum.inl 0) (Sum.inr 0) =
      M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, m10, m20, m30]
  have hμ : (multiplier 2 K A : K) = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 0) (Sum.inl 0) := by
    have e := congrFun (congrFun hspec (Sum.inl 0)) (Sum.inr 0)
    rw [hJ] at e
    simp at e
    rw [← e, m22, ← m33, ← m11]
  have ha : M (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    intro h0
    apply (multiplier 2 K A).ne_zero
    rw [hμ, h0, mul_zero]
  have hσt : ∀ t : K, σ t = t := by
    intro t
    have e : M (Sum.inl 0) (Sum.inl 0) * σ t + M (Sum.inl 0) (Sum.inl 1) * 1 +
        (M (Sum.inl 0) (Sum.inr 0) * 0 + M (Sum.inl 0) (Sum.inr 1) * 0) =
        1 * M (Sum.inl 0) (Sum.inl 1) + t * M (Sum.inl 1) (Sum.inl 1) +
        (0 * M (Sum.inr 0) (Sum.inl 1) + 0 * M (Sum.inr 1) (Sum.inl 1)) := by
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, SymplecticFour.unitri]
        using congrFun (congrFun (h3 t) (Sum.inl 0)) (Sum.inl 1)
    have e2 : M (Sum.inl 0) (Sum.inl 0) * (σ t - t) = 0 := by linear_combination e - t * m11
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left ha)
  have hσ : σ = 1 := RingEquiv.ext fun t => by rw [hσt t]; rfl
  rw [hσ, map_one, mul_one]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp
    (conjAut_mem_inner_of_isSquare (r := 2) (A := A) ⟨M (Sum.inl 0) (Sum.inl 0), hμ⟩)
  exact ⟨g, hg.symm⟩

end Sp4Mat

end CFSG.ASVolI
