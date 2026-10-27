module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorRot
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.D4Inner

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthComm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem card_rotGroup_of_anisotropic (hQ : Q.polarBilin.Nondegenerate) (h2 : finrank K W = 2)
    (hani : ∀ w : W, w ≠ 0 → Q w ≠ 0) : Nat.card (rotGroup Q hQ) = Nat.card K + 1 := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hO := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic h2 hani
  have hidx := relIndex_omegaGroup Q hQ
  have hmul := Subgroup.card_mul_index (dicksonHom Q hQ).ker
  rw [dicksonHom_ker] at hmul
  have hidx' : ((omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 :=
    hidx
  rw [hidx', hO] at hmul
  have hcard : Nat.card (rotGroup Q hQ) =
      Nat.card ((omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [rotGroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), dicksonHom_ker]
  omega

omit [Finite K] [FiniteDimensional K W] in
theorem eq_or_eq_mul_of_cyc3 (hQ : Q.polarBilin.Nondegenerate) (h2 : finrank K W = 2)
    (hirr : ∀ μ : K, μ ^ 2 + μ + 1 ≠ 0) {t t' : W ≃ₗ[K] W}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht' : t' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : ∀ w, t (t w) + t w + w = 0)
    (h1' : ∀ w, t' (t' w) + t' w + w = 0) : t' = t ∨ t' = t * t := by
  classical
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hiso := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ht
  have hiso' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ht'
  have hneg : ∀ v : W, -v = v := fun v => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul K v, h2K, zero_smul]
  have hsq : ∀ w, t (t w) = t w + w := fun w => by
    have h := h1 w
    rw [add_assoc] at h
    rw [eq_neg_of_add_eq_zero_left h, hneg]
  have hsq' : ∀ w, t' (t' w) = t' w + w := fun w => by
    have h := h1' w
    rw [add_assoc] at h
    rw [eq_neg_of_add_eq_zero_left h, hneg]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, Q w₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    refine hv (hQ.1 v fun w => ?_)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hall, hall, hall, sub_zero,
      sub_zero]
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀ (by rw [h, QuadraticMap.map_zero])
  have hpol : ∀ s : W ≃ₗ[K] W, (∀ v, Q (s v) = Q v) → (∀ w, s (s w) = s w + w) →
      QuadraticMap.polar Q (s w₀) w₀ = Q w₀ := by
    intro s hs hss
    have e1 := hs (s w₀)
    rw [hss, QuadraticMap.map_add Q] at e1
    have e2 : QuadraticMap.polar Q (s w₀) w₀ = -Q w₀ := by
      linear_combination e1
    rw [e2, CharTwo.neg_eq]
  have hpw : QuadraticMap.polar Q w₀ w₀ = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hli : LinearIndependent K ![w₀, t w₀] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.mp hab).resolve_right hw₀0, rfl⟩
    · exfalso
      have htw : t w₀ = (-(a / b)) • w₀ := by
        have : b • t w₀ = -(a • w₀) := eq_neg_of_add_eq_zero_right hab
        calc t w₀ = b⁻¹ • (b • t w₀) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = (-(a / b)) • w₀ := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      have h3 := h1 w₀
      rw [htw, map_smul, htw, smul_smul] at h3
      have h4 : ((-(a / b)) * (-(a / b)) + (-(a / b)) + 1) • w₀ = 0 := by
        rw [add_smul, add_smul, one_smul]
        exact h3
      exact hirr (-(a / b)) (by
        have := (smul_eq_zero.mp h4).resolve_right hw₀0
        linear_combination this)
  have hspan : Submodule.span K (Set.range ![w₀, t w₀]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h2])
  have hext : ∀ g g' : W ≃ₗ[K] W, g w₀ = g' w₀ → g (t w₀) = g' (t w₀) → g = g' := by
    intro g g' e0 e1
    refine LinearEquiv.toLinearMap_injective (LinearMap.ext_on_range hspan fun i => ?_)
    fin_cases i
    · exact e0
    · exact e1
  have hmem : t' w₀ ∈ Submodule.span K (Set.range ![w₀, t w₀]) := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hb1 : b = 1 := by
    have e := hpol t' hiso' hsq'
    rw [← hab, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hpw, hpol t hiso hsq, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at e
    have : (b - 1) * Q w₀ = 0 := by linear_combination e
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw₀)
  subst hb1
  rw [one_smul] at hab
  have ha : a * (a + 1) = 0 := by
    have e := hiso' w₀
    rw [← hab, QuadraticMap.map_add Q, QuadraticMap.map_smul, hiso, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_comm, hpol t hiso hsq, smul_eq_mul, smul_eq_mul] at e
    have : (a * (a + 1)) * Q w₀ = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_right hw₀
  rcases mul_eq_zero.mp ha with ha0 | ha1
  ·
    subst ha0
    rw [zero_smul, zero_add] at hab
    left
    refine hext t' t hab.symm ?_
    calc t' (t w₀) = t' (t' w₀) := by rw [hab]
      _ = t' w₀ + w₀ := hsq' w₀
      _ = t w₀ + w₀ := by rw [hab]
      _ = t (t w₀) := (hsq w₀).symm
  ·
    have ha' : a = 1 := by
      have : a = -1 := eq_neg_of_add_eq_zero_left ha1
      rw [this, CharTwo.neg_eq]
    subst ha'
    rw [one_smul] at hab
    right
    have e0 : t' w₀ = (t * t) w₀ := by
      rw [LinearEquiv.mul_apply, hsq, ← hab, add_comm]
    refine hext t' (t * t) e0 ?_
    have htw : t w₀ = t' w₀ + w₀ := by
      rw [← hab, add_comm w₀, add_assoc, ← two_smul K w₀, h2K, zero_smul, add_zero]
    have hL : t' (t w₀) = w₀ := by
      rw [htw, map_add, hsq' w₀, add_comm (t' w₀) w₀, add_assoc, ← two_smul K (t' w₀), h2K,
        zero_smul, add_zero]
    have hR : (t * t) (t w₀) = w₀ := by
      rw [LinearEquiv.mul_apply, hsq (t w₀), hsq w₀, add_comm (t w₀) w₀, add_assoc,
        ← two_smul K (t w₀), h2K, zero_smul, add_zero]
    rw [hL, hR]

omit [Finite K] [CharP K 2] in
theorem cyc3_of_mem_rotGroup {hQ : Q.polarBilin.Nondegenerate} (h2 : finrank K W = 2)
    {r : W ≃ₗ[K] W} (hr : r ∈ rotGroup Q hQ) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∀ w, r (r w) + r w + w = 0 := by
  intro w
  have hfree := ((mem_rotGroup_iff h2 (rotGroup_le_orthogonalGroup hQ hr)).mp hr).resolve_left hr1
  refine hfree _ ?_
  have h3 : r (r (r w)) = w := by
    have := LinearEquiv.congr_fun hr3 w
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  rw [map_add, map_add, h3]
  abel

theorem card_rotGroup_pow_three_eq_one (hQ : Q.polarBilin.Nondegenerate) (h2 : finrank K W = 2)
    (hani : ∀ w : W, w ≠ 0 → Q w ≠ 0) (hpq : 3 ∣ Nat.card K + 1)
    (hirr : ∀ μ : K, μ ^ 2 + μ + 1 ≠ 0) :
    Nat.card {r : rotGroup Q hQ // r ^ 3 = 1} = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcard := card_rotGroup_of_anisotropic hQ h2 hani
  obtain ⟨r₀, hr₀⟩ := exists_prime_orderOf_dvd_card' (G := rotGroup Q hQ) 3 (hcard ▸ hpq)
  have hr₀3 : r₀ ^ 3 = 1 := hr₀ ▸ pow_orderOf_eq_one r₀
  have hr₀1 : r₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr₀
    omega
  have hcoe3 : ∀ r : rotGroup Q hQ, r ^ 3 = 1 → (r : W ≃ₗ[K] W) ^ 3 = 1 := fun r hr => by
    rw [← Subgroup.coe_pow, hr, Subgroup.coe_one]
  have hcoe1 : ∀ r : rotGroup Q hQ, r ≠ 1 → (r : W ≃ₗ[K] W) ≠ 1 := fun r hr h =>
    hr (Subtype.ext h)
  have hset : {r : rotGroup Q hQ | r ^ 3 = 1} = {1, r₀, r₀ ^ 2} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hr
      by_cases hr1 : r = 1
      · exact Or.inl hr1
      · right
        have hc := cyc3_of_mem_rotGroup h2 r.2 (hcoe3 r hr) (hcoe1 r hr1)
        have hc₀ := cyc3_of_mem_rotGroup h2 r₀.2 (hcoe3 r₀ hr₀3) (hcoe1 r₀ hr₀1)
        rcases eq_or_eq_mul_of_cyc3 hQ h2 hirr (rotGroup_le_orthogonalGroup hQ r₀.2)
          (rotGroup_le_orthogonalGroup hQ r.2) hc₀ hc with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext (by rw [h, pow_two, Subgroup.coe_mul]))
    · rintro (rfl | rfl | rfl)
      · exact one_pow 3
      · exact hr₀3
      · rw [← pow_mul, mul_comm, pow_mul, hr₀3, one_pow]
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → r₀ ^ i = r₀ ^ j → i = j := fun i j hi hj h =>
    pow_injOn_Iio_orderOf (by rw [hr₀]; exact hi) (by rw [hr₀]; exact hj) h
  have h01 : (1 : rotGroup Q hQ) ≠ r₀ := fun h => by
    have := hne 0 1 (by norm_num) (by norm_num) (by rw [pow_zero, pow_one]; exact h)
    omega
  have h02 : (1 : rotGroup Q hQ) ≠ r₀ ^ 2 := fun h => by
    have := hne 0 2 (by norm_num) (by norm_num) (by rw [pow_zero]; exact h)
    omega
  have h12 : r₀ ≠ r₀ ^ 2 := fun h => by
    have := hne 1 2 (by norm_num) (by norm_num) (by rw [pow_one]; exact h)
    omega
  have hc : Nat.card {r : rotGroup Q hQ // r ^ 3 = 1} =
      Nat.card ({r : rotGroup Q hQ | r ^ 3 = 1} : Set (rotGroup Q hQ)) := rfl
  rw [hc, Nat.card_coe_set_eq, hset, Set.ncard_eq_three]
  exact ⟨1, r₀, r₀ ^ 2, h01, h02, h12, rfl⟩

end CFSG.StandardType.D4Inner

end
