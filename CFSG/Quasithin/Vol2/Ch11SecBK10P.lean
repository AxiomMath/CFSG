module

public import CFSG.Quasithin.Vol2.Ch11SecBK10O
public import CFSG.Quasithin.Vol2.Ch11SecBK10H
public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.Quasithin.Vol2.Ch11SecBK10N
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.OutStructure (mem_of_pow_mem_of_index_le_two)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem thetaAut_map_eq :
    (projUnitriangular 3 K).map thetaAut.toMonoidHom = projUnitriangular 3 K := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨u, hu, rfl⟩
    exact thetaAut_mem hu
  · rw [Subgroup.card_map_of_injective thetaAut.injective]

theorem thetaAut_inv_mem {u : projectiveSL 3 K} (hu : u ∈ projUnitriangular 3 K) :
    (thetaAut⁻¹ : MulAut (projectiveSL 3 K)) u ∈ projUnitriangular 3 K := by
  rw [← thetaAut_map_eq] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 : (thetaAut⁻¹ : MulAut (projectiveSL 3 K)) (thetaAut v) = v := by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  change (thetaAut⁻¹ : MulAut (projectiveSL 3 K)) (thetaAut v) ∈ _
  rw [h1]
  exact hv

theorem exists_conj_mul_theta {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f)
    (s : MulAut (projectiveSL 3 K)) {k : ℕ} (hs : s ^ (2 ^ k) = 1) :
    ∃ x : projectiveSL 3 K, ∃ ε : ℕ, ε ≤ 1 ∧ s = MulAut.conj x * thetaAut ^ ε := by
  obtain ⟨x, hx | hx⟩ := two_elt_cases hf hK s hs
  · exact ⟨x, 0, zero_le_one, by rw [pow_zero, mul_one, hx]⟩
  · refine ⟨x * proj 3 K wSL, 1, le_rfl, ?_⟩
    have hww : MulAut.conj (proj 3 K wSL) *
        MulAut.conj (proj 3 K (wSL : SpecialLinearGroup (Fin 3) K)) =
          (1 : MulAut (projectiveSL 3 K)) := by
      rw [← map_mul, ← map_mul, wSL_mul_self, map_one, map_one]
    rw [pow_one, hx, thetaAut, map_mul]
    calc MulAut.conj x * dualAut 3 K
        = MulAut.conj x * (MulAut.conj (proj 3 K wSL) * MulAut.conj (proj 3 K wSL)) *
            dualAut 3 K := by rw [hww, mul_one]
      _ = _ := by group

theorem torusRigidAt_L3 {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f) :
    TorusRigidAt (projectiveSL 3 K) (projUnitriangular 3 K) := by
  intro Sh hSh2 hSP hSs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := not_three_dvd hf hK
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  set y := torusMHom l with hy
  have hθy : thetaAut y = y := thetaAut_torusM l
  refine ⟨y, fun s hs => ?_, ?_, fun y' hy' _ β hβ hβy' => ?_⟩
  ·
    obtain ⟨k, hk⟩ := hSh2 ⟨s, hs⟩
    have hk' : s ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨x, ε, hε, hsx⟩ := exists_conj_mul_theta hf hK s hk'
    have hθε : ∀ u ∈ projUnitriangular 3 K,
        ((thetaAut ^ ε)⁻¹ : MulAut (projectiveSL 3 K)) u ∈ projUnitriangular 3 K := by
      intro u hu
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · simpa using hu
      · rw [pow_one]
        exact thetaAut_inv_mem hu
    have hxN : x ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
      apply CFSG.Quasithin.A4.mem_normalizer_of_conj_mem
      intro u hu
      have h1 : x * u * x⁻¹ = s (((thetaAut ^ ε)⁻¹ : MulAut (projectiveSL 3 K)) u) := by
        have h2 : (thetaAut ^ ε) (((thetaAut ^ ε)⁻¹ : MulAut (projectiveSL 3 K)) u) = u := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        rw [hsx, MulAut.mul_apply, h2, MulAut.conj_apply]
      rw [h1]
      exact (hSs s hs _).mp (hθε u hu)
    rw [normalizer_projUnitriangular 2] at hxN
    obtain ⟨X, hX, rfl⟩ := hxN
    have hsy : s y = proj 3 K (X * torusM l * X⁻¹) := by
      rw [hsx, MulAut.mul_apply]
      have hε' : (thetaAut ^ ε) y = y := by
        rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
        · rfl
        · rw [pow_one, hθy]
      rw [hε', MulAut.conj_apply, hy]
      change proj 3 K X * proj 3 K (torusM l) * (proj 3 K X)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
    rw [hsy, hy]
    change proj 3 K (torusM l) * (proj 3 K (X * torusM l * X⁻¹))⁻¹ ∈ _
    rw [← map_inv, ← map_mul]
    refine ⟨_, mul_inv_mem_unitriangular (torusM_mem_upper l)
      ((upperTriangular 3 K).mul_mem ((upperTriangular 3 K).mul_mem hX (torusM_mem_upper l))
        ((upperTriangular 3 K).inv_mem hX)) fun i => ?_, rfl⟩
    rw [diag_conj_of_upper hX (torusM_mem_upper l) i]
  ·
    have h1 : orderOf y = orderOf l := orderOf_injective _ torusMHom_injective l
    have h2 : orderOf l ∣ Nat.card Kˣ := orderOf_dvd_natCard l
    rw [Nat.card_units, hK] at h2
    have h4 : Odd (2 ^ f - 1) := by
      obtain ⟨m, rfl⟩ := hf
      have h6 : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
      have h5 : 0 < 2 ^ (2 * m + 1) := by positivity
      generalize 2 ^ (2 * m + 1) = N at h5 h6 ⊢
      exact Nat.odd_iff.mpr (by omega)
    rw [h1]
    exact Odd.of_dvd_nat h4 h2
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hrX
    have h1 := Subgroup.card_subgroup_dvd_card (projUnitriangular 3 K)
    rw [card_projUnitriangular, hK] at h1
    refine dvd_trans ?_ h1
    have hf1 : f ≠ 0 := by
      obtain ⟨m, rfl⟩ := hf
      omega
    exact dvd_pow (dvd_pow_self 2 hf1) (by norm_num)
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (le_refl 3)
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  have hidx' : (semilinearAutGroup 3 K).index ≤ 2 := by
    have h2 : (semilinearAutGroup 3 K).relIndex (standardAutGroup 3 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hE : β ∈ semilinearAutGroup 3 K :=
    mem_of_pow_mem_of_index_le_two _ hidx' (hr.odd_of_ne_two hr2) (by rw [hβr]; exact one_mem _)
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp hE
  obtain ⟨x, hx⟩ := linearAutGroup_le_inner h3 (conjAut_mem_linearAutGroup A)
  obtain ⟨X, rfl⟩ := proj_surjective 3 K x
  obtain ⟨Y', rfl⟩ := proj_surjective 3 K y'
  have hN : Y' * (torusM l)⁻¹ ∈ unitriangular 3 K := by
    obtain ⟨u, hu, hu'⟩ := hy'
    have h1 : u = Y' * (torusM l)⁻¹ := proj_injective h3 (by
      rw [hu', map_mul, map_inv]
      rfl)
    rw [← h1]
    exact hu
  have hdiag : ∀ i, (Y' : Matrix (Fin 3) (Fin 3) K) i i =
      (torusM l : Matrix (Fin 3) (Fin 3) K) i i := by
    intro i
    have hNu : ((Y' * (torusM l)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun _ _ h => hN.1 _ _ h
    have htu := mem_upperTriangular_iff_isUpperTriangular.mp (torusM_mem_upper l)
    have e : (Y' : Matrix (Fin 3) (Fin 3) K) = ((Y' * (torusM l)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (torusM l : Matrix (Fin 3) (Fin 3) K) := by
      change _ = (Y' : Matrix (Fin 3) (Fin 3) K) *
        (((torusM l)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (torusM l : Matrix (Fin 3) (Fin 3) K)
      rw [Matrix.mul_assoc, coe_inv_mul_coe, Matrix.mul_one]
    rw [e, mul_apply_self_of_isUpperTriangular hNu htu, hN.2 i, one_mul]
  have hfix : X * SpecialLinearGroup.map σ.toRingHom Y' * X⁻¹ = Y' := by
    apply proj_injective h3
    rw [hAσ, MulAut.mul_apply, ← hx, fieldAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul,
      ← map_mul] at hβy'
    exact hβy'
  have htr : σ ((Y' : Matrix (Fin 3) (Fin 3) K) 0 0 + (Y' : Matrix (Fin 3) (Fin 3) K) 1 1 +
      (Y' : Matrix (Fin 3) (Fin 3) K) 2 2) = (Y' : Matrix (Fin 3) (Fin 3) K) 0 0 +
        (Y' : Matrix (Fin 3) (Fin 3) K) 1 1 + (Y' : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin 3) K =>
      Matrix.trace (B : Matrix (Fin 3) (Fin 3) K)) hfix
    change Matrix.trace ((X : Matrix (Fin 3) (Fin 3) K) *
      ((Y' : Matrix (Fin 3) (Fin 3) K).map σ) *
        ((X⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
          Matrix.trace (Y' : Matrix (Fin 3) (Fin 3) K) at h1
    rw [Matrix.trace_mul_cycle, coe_inv_mul_coe, Matrix.one_mul, Matrix.trace_fin_three,
      Matrix.trace_fin_three, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply] at h1
    rw [map_add, map_add]
    exact h1
  rw [hdiag 0, hdiag 1, hdiag 2, coe_torusM] at htr
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at htr
  have hσl : σ (l : K) + (σ (l : K))⁻¹ = (l : K) + (l : K)⁻¹ := by
    rw [map_add, map_add, map_one, Units.val_inv_eq_inv_val, map_inv₀] at htr
    linear_combination htr
  have hσl' := L2.eq_or_eq_inv_of_add_inv ((map_ne_zero σ).mpr l.ne_zero) l.ne_zero hσl
  have hσ2 : σ ^ 2 = 1 := by
    have hl2 : (σ ^ 2) (l : K) = l := by
      rw [sq, RingAut.mul_apply]
      rcases hσl' with h | h
      · rw [h, h]
      · rw [h, map_inv₀, h, inv_inv]
    refine RingEquiv.ext fun z => ?_
    rw [RingAut.one_apply]
    by_cases hz : z = 0
    · rw [hz, map_zero]
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hl (Units.mk0 z hz))
      have hzn : z = (l : K) ^ n := by
        have := congrArg Units.val hn
        rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
        exact this.symm
      rw [hzn, map_zpow₀, hl2]
  have hσ1 : σ = 1 := by
    have hcard : Nat.card (RingAut K) = f := (card_ringAut_and_isCyclic Nat.prime_two K hK).1
    have : Finite (RingAut K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      DFunLike.coe_injective
    have h1 : orderOf σ ∣ f := hcard ▸ orderOf_dvd_natCard σ
    have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ2
    have h4 : Nat.Coprime 2 f := Nat.coprime_two_left.mpr hf
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h1)
  have hβin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) := by
    rw [hAσ, hσ1, map_one, mul_one, ← hx]
    exact ⟨_, rfl⟩
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ hβin

theorem torusRigid_L3 {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f) :
    TorusRigid (projectiveSL 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  refine TorusRigid.of_at ?_ (torusRigidAt_L3 hf hK)
  rw [← hQ]
  refine ⟨le_top, Q.isPGroup', ?_⟩
  change ¬ 2 ∣ (Q : Subgroup (projectiveSL 3 K)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Q.not_dvd_index

end BK10.L3

end CFSG.Quasithin.Vol2.Ch11.SecD
