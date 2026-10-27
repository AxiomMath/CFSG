module

public import CFSG.OddTranspositions.SixNineUnconditional

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_prime_orderOf_eq_AalphaStar (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) :
    ∃ p : ℕ, p.Prime ∧ ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = p := by
  classical
  have hD := hC.setup.oddT
  have hconst : ∀ a ∈ AalphaStar D hC.alpha, ∀ b ∈ AalphaStar D hC.alpha,
      orderOf (hC.d * b) = orderOf (hC.d * a) := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := cenGen_transitive_AalphaStar_unconditional hC hsecond a ha b hb
    have hxu : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.closure_le _).mpr (fun _ hy => hy.2) hx)
    have e : hC.d * (x * a * x⁻¹) = x * (hC.d * a) * x⁻¹ := by
      calc hC.d * (x * a * x⁻¹) = hC.d * x * a * x⁻¹ := by group
        _ = x * hC.d * a * x⁻¹ := by rw [hxu]
        _ = x * (hC.d * a) * x⁻¹ := by group
    rw [e]
    refine (SemiconjBy.orderOf_eq x ?_).symm
    unfold SemiconjBy
    rw [inv_mul_cancel_right]
  rcases (AalphaStar D hC.alpha).eq_empty_or_nonempty with hA | ⟨w₀, hw₀⟩
  · exact ⟨2, Nat.prime_two, fun w hw => by simp [hA] at hw⟩
  refine ⟨orderOf (hC.d * w₀), ?_, fun w hw => hconst w₀ hw₀ w hw⟩
  have hu : hC.d ∈ D := hC.hd
  obtain ⟨hw₀D, hw₀u, -⟩ := mem_Gamma_iff.mp (show w₀ ∈ Gamma hC from hw₀)
  have hu2 : hC.d * hC.d = 1 := hD.mul_self_eq_one hu
  have hw2 : w₀ * w₀ = 1 := hD.mul_self_eq_one hw₀D
  have huw : ¬ Commute hC.d w₀ := fun h => hw₀u h.symm
  have hodd : Odd (orderOf (hC.d * w₀)) := hD.odd_of_not_commute hu hw₀D huw
  have hp1 : orderOf (hC.d * w₀) ≠ 1 := by
    intro h
    have e := hD.eq_of_mul_eq_one hu (orderOf_eq_one_iff.mp h)
    rw [← e] at huw
    exact huw (Commute.refl _)
  have hp2 : 2 ≤ orderOf (hC.d * w₀) := by
    obtain ⟨m, hm⟩ := hodd
    omega
  by_contra hnp
  obtain ⟨j, hjdvd, hj2, hjlt⟩ := Nat.exists_dvd_of_not_prime2 hp2 hnp
  obtain ⟨k, hk⟩ : ∃ k, k = orderOf (hC.d * w₀) / j := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = (hC.d * w₀) ^ j := ⟨_, rfl⟩
  have hyord : orderOf y = k := by
    rw [hy, hk]
    exact orderOf_pow_of_dvd (by omega) hjdvd
  have hkodd : Odd k := hk ▸ hodd.of_dvd_nat (Nat.div_dvd_of_dvd hjdvd)
  have hyodd : Odd (orderOf y) := by
    rw [hyord]
    exact hkodd
  have hk1 : k ≠ 1 := by
    intro h
    have hjk := Nat.div_mul_cancel hjdvd
    rw [← hk, h, one_mul] at hjk
    omega
  have hklt : k < orderOf (hC.d * w₀) := by
    rw [hk]
    exact Nat.div_lt_self (by omega) (by omega)
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact hk1 hyord.symm
  have hinv1 : hC.d * (hC.d * w₀) * hC.d⁻¹ = (hC.d * w₀)⁻¹ := by
    rw [mul_inv_rev, hD.inv_eq hu, hD.inv_eq hw₀D, ← mul_assoc, hu2, one_mul]
  have hyinv : hC.d * y * hC.d⁻¹ = y⁻¹ := by
    rw [hy, ← conj_pow, hinv1, inv_pow]
  have hujD : hC.d * y ∈ D := by
    have hujeq : hC.d * y = (hC.d * w₀) ^ (-(j : ℤ)) * hC.d := by
      rw [zpow_neg, zpow_natCast, ← hy, ← hyinv, inv_mul_cancel_right]
    obtain ⟨m, hm⟩ := OddTransp.exists_zpow_conj_eq hu2 hw2 hodd (-(j : ℤ))
    rw [hujeq, ← hm]
    exact hC.setup.normal _ _ hu
  have hyeq : y = hC.d * (hC.d * y) := by
    rw [← mul_assoc, hu2, one_mul]
  have hujc : ¬ Commute (hC.d * y) hC.d := by
    intro hc
    have hyu : Commute y hC.d := by
      rw [hyeq]
      exact (Commute.refl _).mul_left hc
    have hyy : y = y⁻¹ := by
      rw [← hyinv, ← hyu.eq, mul_inv_cancel_right]
    exact hy1 (OddTransp.eq_one_of_mul_self_of_odd (mul_eq_one_iff_eq_inv.mpr hyy) hyodd)
  have hujα : hC.d * y ∈ hC.alpha := by
    rcases (Set.ext_iff.mp hC.eq_alpha_union _).mp hujD with (h | h) | h
    · exact h
    · exact (hujc (hC.DalphaStar_subset_commute h).2).elim
    · have h' := hconst w₀ hw₀ _ h
      rw [← hyeq, hyord] at h'
      omega
  obtain ⟨v, hv, hvw⟩ := exists_DalphaStar_not_commute hC (show w₀ ∈ Gamma hC from hw₀)
  obtain ⟨β, hβ, hvβ⟩ := mem_DalphaStar_iff.mp hv
  obtain ⟨-, -, -, hβc⟩ := mem_Dalpha_iff.mp hβ
  have huv : Commute hC.d v := hβc _ hC.d_mem_alpha v hvβ
  have hyv : Commute y v := by
    rw [hyeq]
    exact huv.mul_left (hβc _ hujα v hvβ)
  have hvD : v ∈ D := (hC.DalphaStar_subset_commute hv).1
  have hvu : v ≠ hC.d := by
    rw [hC.DalphaStar_alpha] at hv
    exact (OddLocal.subset_commSet hC.setup.normal hC.hE hv).2.2
  have htri : IsTriangle D hC.d w₀ v := ⟨hu, hvD, hw₀D, fun h => hvu h.symm, huv, huw, hvw⟩
  have h4 : orderOf (hC.d * v * w₀) = 4 := hsecond _ _ _ htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({hC.d, w₀} : Set G) → IsTriangle D hC.d x v →
      ¬ IsThirdKind hC.d x v := by
    intro x _ _ hx hthird
    have h4' : orderOf (hC.d * v * x) = 4 := hsecond _ x _ hx
    obtain ⟨n, hnodd, _hn1, hord⟩ := hthird
    have hn2 : n = 2 := by omega
    rw [hn2] at hnodd
    obtain ⟨m, hm⟩ := hnodd
    omega
  have SK : SecondKindStructure hC.d w₀ v :=
    OddTransp.secondKind_structure hD hC.setup.normal htri h4 hno
  have hyX : y ∈ Subgroup.closure ({hC.d, w₀} : Set G) := by
    rw [hy]
    exact pow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) j
  have h1 : y * (hC.d * v) * y⁻¹ ∈
      conjClosure (Subgroup.closure ({hC.d, w₀} : Set G)) (hC.d * v) :=
    Subgroup.subset_closure ⟨y, hyX, rfl⟩
  have h2 : hC.d * v ∈ conjClosure (Subgroup.closure ({hC.d, w₀} : Set G)) (hC.d * v) :=
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hyy : y * y ∈ conjClosure (Subgroup.closure ({hC.d, w₀} : Set G)) (hC.d * v) := by
    have e1 : v * y⁻¹ = y⁻¹ * v := hyv.inv_left.eq.symm
    have e2 : hC.d * y⁻¹ * hC.d⁻¹ = y := by
      rw [← conj_inv, hyinv, inv_inv]
    have e : y * (hC.d * v) * y⁻¹ * (hC.d * v)⁻¹ = y * y := by
      calc y * (hC.d * v) * y⁻¹ * (hC.d * v)⁻¹ = y * hC.d * (v * y⁻¹) * v⁻¹ * hC.d⁻¹ := by
            group
        _ = y * (hC.d * y⁻¹ * hC.d⁻¹) := by
            rw [e1]
            group
        _ = y * y := by rw [e2]
    rw [← e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  have hyy1 : y * y = 1 := by
    have hodd2 : Odd (orderOf (y * y)) := by
      have := OddTransp.odd_orderOf_zpow hyodd 2
      rwa [zpow_two] at this
    exact OddTransp.eq_one_of_mul_self_of_odd (SK.sq _ hyy) hodd2
  exact hy1 (OddTransp.eq_one_of_mul_self_of_odd hyy1 hyodd)

end CFSG.OddTranspositions

end
