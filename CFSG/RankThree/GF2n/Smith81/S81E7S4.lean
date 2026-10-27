module

public import CFSG.RankThree.GF2n.Smith81.S81E7Roots
public import CFSG.RankThree.GF2n.Smith81.S81E7Cent2
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe4
public import CFSG.RankThree.GF2n.Smith81.S81E7Conj

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem IsRootElt.mul_self_eq_one {t : (Module.End K (V K))ˣ} (ht : IsRootElt t) : t * t = 1 := by
  have h := ht.sub_one_sq
  have h2 : (2 : K) = 0 := CharP.ofNat_eq_zero K 2
  have h11 : (1 : Module.End K (V K)) + 1 = 0 := by
    rw [← two_smul K (1 : Module.End K (V K)), h2, zero_smul]
  have h22 : (t : Module.End K (V K)) + t = 0 := by
    rw [← two_smul K (t : Module.End K (V K)), h2, zero_smul]
  have e : (t : Module.End K (V K)) * t = ((t : Module.End K (V K)) - 1) * ((t : Module.End K (V K)) - 1)
      + ((t : Module.End K (V K)) + t) - 1 := by
    noncomm_ring
  apply Units.ext
  rw [Units.val_mul, Units.val_one, e, h, h22, zero_add, zero_sub]
  exact (eq_neg_of_add_eq_zero_left h11).symm

theorem rootElt_in_Lam (hq : 4 ≤ Nat.card K) {v t : (Module.End K (V K))ˣ} (hvJ : v ∈ Jgrp K)
    (hord : orderOf v = Nat.card K - 1 ∨ orderOf v = Nat.card K + 1) (ht : IsRootElt t)
    (hcomm : t * v = v * t) :
    ∃ u' ∈ UL K, ∃ β ∈ Perp, ∃ c : K, c ≠ 0 ∧ t = u' * e7Data_valid.xu K β c * u'⁻¹ := by
  obtain ⟨j, hj, l, hl, htjl, -, hodd⟩ := centralizer_le_J_Lam hq hvJ hord ht.mem_E hcomm
  have hlj : l * j = j * l := Lam_commute_J hl hj
  have hsq : t * t = 1 := ht.mul_self_eq_one
  have hjj : j * j = (l * l)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc j * j * (l * l) = j * (j * l) * l := by group
      _ = j * (l * j) * l := by rw [hlj]
      _ = (j * l) * (j * l) := by group
      _ = 1 := by rw [← htjl]; exact hsq
  have hjjL : j * j ∈ Lam K := by
    rw [hjj]
    exact inv_mem (mul_mem hl hl)
  have hjjJ : j * j ∈ Jgrp K := mul_mem hj hj
  have h1 : j * j = 1 := Lam_faithful_V0 hjjL (fun w hw => J_fixes_V0 hjjJ hw)
  have hj1 : j = 1 := by
    have hd : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    have ho : orderOf j = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 ho
  have htl : t = l := by rw [htjl, hj1, one_mul]
  exact rootElt_Lam_form ht (htl ▸ hl)

@[expose] def IsHWVec (w : V K) : Prop :=
  ∃ g ∈ EGrp K, ∃ c : K, c ≠ 0 ∧ w = c • (g : Module.End K (V K)) (w0 : V K)

theorem exists_idx0_pr_neg_one {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    ∃ μ ∈ idx0, pr μ β = -1 := by
  obtain ⟨hr, h0⟩ := perp_iff.1 hβ
  revert h0
  refine (forall_isRoot_iff fun γ => γ node1 = 0 → ∃ μ ∈ idx0, pr μ γ = -1).2 ?_ β hr
  decide +kernel

private theorem unit_inv_apply_apply {u : (Module.End K (V K))ˣ} (x : V K) :
    ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ((u : Module.End K (V K)) x) = x := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

private theorem unit_apply_eq_zero {u : (Module.End K (V K))ˣ} {x : V K}
    (h : (u : Module.End K (V K)) x = 0) : x = 0 := by
  have h1 := unit_inv_apply_apply (u := u) x
  rw [h, map_zero] at h1
  exact h1.symm

private theorem xu_sub_one_apply_single {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp)
    {μ : Fin e7Data.d} (hpr : pr μ β = -1) (c : K) :
    ((e7Data_valid.xu K β c : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single μ (1 : K)) - Finsupp.single μ (1 : K) =
      c • Finsupp.single (shift β μ) (1 : K) := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβ'.1 μ, if_pos hpr]
  abel

theorem exists_hwVec_range {u' : (Module.End K (V K))ˣ} (hu' : u' ∈ UL K)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {c : K} (hc : c ≠ 0) :
    ∃ w : V K, w ≠ 0 ∧ w ∈ V0 K ∧
      w ∈ LinearMap.range (((u' * e7Data_valid.xu K β c * u'⁻¹ : (Module.End K (V K))ˣ) :
        Module.End K (V K)) - 1) ∧ IsHWVec w := by
  obtain ⟨μ, hμ, hpr⟩ := exists_idx0_pr_neg_one hβ
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have hμ' : shift β μ ∈ idx0 := by
    rw [mem_idx0, pr_shift hβ'.1 hpr theta, hβ'.2, add_zero]
    exact mem_idx0.1 hμ
  have huL : u' ∈ Lam K := UL_le_Lam hu'
  have huE : u' ∈ EGrp K := Lam_le_E huL
  refine ⟨c • (u' : Module.End K (V K)) (Finsupp.single (shift β μ) (1 : K)), ?_, ?_, ?_, ?_⟩
  · intro h
    rcases smul_eq_zero.1 h with h1 | h1
    · exact hc h1
    · exact one_ne_zero (Finsupp.single_eq_zero.1 (unit_apply_eq_zero h1))
  · exact Submodule.smul_mem _ c (Lam_stabilizes_V0 huL (single_mem_V0 hμ'))
  · refine LinearMap.mem_range.2 ⟨(u' : Module.End K (V K)) (Finsupp.single μ (1 : K)), ?_⟩
    have hconj : ((u' * e7Data_valid.xu K β c * u'⁻¹ : (Module.End K (V K))ˣ) :
          Module.End K (V K)) ((u' : Module.End K (V K)) (Finsupp.single μ (1 : K))) =
        (u' : Module.End K (V K)) (((e7Data_valid.xu K β c : (Module.End K (V K))ˣ) :
          Module.End K (V K)) (Finsupp.single μ (1 : K))) := by
      rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, unit_inv_apply_apply]
    rw [LinearMap.sub_apply, Module.End.one_apply, hconj, ← map_sub,
      xu_sub_one_apply_single hβ hpr c, map_smul]
  · obtain ⟨g₀, hg₀, hg₀w⟩ := weight_vec_mem_orbit (K := K) (shift β μ)
    refine ⟨u' * g₀, mul_mem huE hg₀, c, hc, ?_⟩
    rw [Units.val_mul, Module.End.mul_apply, hg₀w]

theorem rootPoint_of_commuting_rootElt (hq : 4 ≤ Nat.card K) {v t : (Module.End K (V K))ˣ}
    (hvJ : v ∈ Jgrp K) (hord : orderOf v = Nat.card K - 1 ∨ orderOf v = Nat.card K + 1)
    (ht : IsRootElt t) (hcomm : t * v = v * t) :
    ∃ w : V K, w ≠ 0 ∧ w ∈ V0 K ∧ w ∈ LinearMap.range ((t : Module.End K (V K)) - 1) ∧ IsHWVec w := by
  obtain ⟨u', hu', β, hβ, c, hc, rfl⟩ := rootElt_in_Lam hq hvJ hord ht hcomm
  exact exists_hwVec_range hu' hβ hc

end CFSG.RankThree.GF2n.Smith81.E7Model
