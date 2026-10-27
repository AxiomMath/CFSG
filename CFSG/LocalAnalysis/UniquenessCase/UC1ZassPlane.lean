module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassEig
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

section Plane

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {G : Type*} [Group G]

theorem rep_inv_apply (ρ : Representation K G M) (g : G) (x : M) : ρ g⁻¹ (ρ g x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem span_pair_invariant (ρ : Representation K G M) (g : G) {v w : M}
    (hv : ρ g v ∈ Submodule.span K {v, w}) (hw : ρ g w ∈ Submodule.span K {v, w}) :
    ∀ x ∈ Submodule.span K {v, w}, ρ g x ∈ Submodule.span K {v, w} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hw
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem mul_eq_of_conj_eq_inv {c y : G} (hy : y * c * y⁻¹ = c⁻¹) : c * y = y * c⁻¹ := by
  have h1 : y * c = c⁻¹ * y := mul_inv_eq_iff_eq_mul.mp hy
  rw [eq_mul_inv_iff_mul_eq]
  calc c * y * c = c * (y * c) := mul_assoc _ _ _
    _ = c * (c⁻¹ * y) := by rw [h1]
    _ = y := mul_inv_cancel_left c y

theorem exists_plane (ρ : Representation K G M) [Nontrivial M] (hk : (2 : K) ≠ 0) {t : ℕ}
    (ht : 1 ≤ t) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (t + 1))) {c y : G}
    (hc : c ^ 2 ^ (t + 1) = 1) (hy : y * c * y⁻¹ = c⁻¹) (hy2 : y ^ 2 = c ^ 2 ^ t)
    (hz : ∀ v : M, ρ (c ^ 2 ^ t) v = -v) :
    ∃ W : Submodule K M, Module.finrank K W = 2 ∧ (∀ x ∈ W, ρ c x ∈ W) ∧
      (∀ x ∈ W, ρ y x ∈ W) ∧
      (∀ i : ℕ, (∃ μ : K, ∀ x ∈ W, ρ (c ^ i) x = μ • x) → c ^ i = 1 ∨ c ^ i = c ^ 2 ^ t) ∧
      ∀ i : ℕ, ¬ ∃ μ : K, ∀ x ∈ W, ρ (c ^ i * y) x = μ • x := by
  have hCN : ρ c ^ 2 ^ (t + 1) = 1 := by rw [← map_pow, hc, map_one]
  obtain ⟨l, v, hl, hv0, hv⟩ :=
    exists_eigenvector_of_pow_eq_one (pow_pos two_pos _) hζ (ρ c) hCN
  have hlt : l ^ 2 ^ t = -1 := by
    have h1 := pow_apply_eigen hv (2 ^ t)
    rw [← map_pow, hz] at h1
    have h2 : (l ^ 2 ^ t + 1) • v = 0 := by rw [add_smul, one_smul, ← h1, neg_add_cancel]
    exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h2).resolve_right hv0)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at hl
    exact zero_ne_one hl
  have horder : orderOf l = 2 ^ (t + 1) := orderOf_eq_two_pow_succ hk hlt
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    have h1 : l ^ 2 ^ t = 1 := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      rw [show 2 ^ (1 + s) = 2 * 2 ^ s by ring, pow_mul, h, one_pow]
    rw [hlt] at h1
    exact hk (by linear_combination -h1)
  set w := ρ y v with hw
  have hcinv : ρ c⁻¹ v = l⁻¹ • v := by
    have h1 : v = l⁻¹ • ρ c v := by rw [hv, smul_smul, inv_mul_cancel₀ hl0, one_smul]
    calc ρ c⁻¹ v = ρ c⁻¹ (l⁻¹ • ρ c v) := by rw [← h1]
      _ = l⁻¹ • v := by rw [map_smul, rep_inv_apply]
  have hcw : ρ c w = l⁻¹ • w := by
    rw [hw, ← Module.End.mul_apply, ← map_mul, mul_eq_of_conj_eq_inv hy, map_mul,
      Module.End.mul_apply, hcinv, map_smul]
  have hyw : ρ y w = -v := by
    rw [hw, ← Module.End.mul_apply, ← map_mul, ← pow_two, hy2, hz]
  have hw0 : w ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (ρ y⁻¹) h
    rwa [hw, rep_inv_apply, map_zero] at this
  have hinv : l⁻¹ - l ≠ 0 := by
    intro h
    have h' : l⁻¹ = l := sub_eq_zero.mp h
    apply hl2
    calc l ^ 2 = l * l⁻¹ := by rw [h', sq]
      _ = 1 := mul_inv_cancel₀ hl0
  have hli : LinearIndependent K ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have e1 : a • (l • v) + b • (l⁻¹ • w) = 0 := by
      simpa [map_add, map_smul, hv, hcw] using congrArg (ρ c) hab
    have e2 : a • (l • v) + b • (l • w) = 0 := by
      simpa [smul_add, smul_smul, mul_comm] using congrArg (fun x => l • x) hab
    have e3 : (b * (l⁻¹ - l)) • w = 0 := by
      calc (b * (l⁻¹ - l)) • w
          = (a • (l • v) + b • (l⁻¹ • w)) - (a • (l • v) + b • (l • w)) := by module
        _ = 0 := by rw [e1, e2, sub_zero]
    have hb : b = 0 := by
      have := (smul_eq_zero.mp e3).resolve_right hw0
      exact (mul_eq_zero.mp this).resolve_right hinv
    refine ⟨?_, hb⟩
    rw [hb, zero_smul, add_zero] at hab
    exact (smul_eq_zero.mp hab).resolve_right hv0
  have hrange : Set.range ![v, w] = {v, w} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr eq_comm eq_comm
  have hvW : v ∈ Submodule.span K {v, w} := Submodule.subset_span (by simp)
  have hwW : w ∈ Submodule.span K {v, w} := Submodule.subset_span (by simp)
  have hcv : ∀ n : ℕ, ρ (c ^ n) v = l ^ n • v := fun n => by
    rw [map_pow]; exact pow_apply_eigen hv n
  have hcw' : ∀ n : ℕ, ρ (c ^ n) w = l⁻¹ ^ n • w := fun n => by
    rw [map_pow]; exact pow_apply_eigen hcw n
  refine ⟨Submodule.span K {v, w}, ?_, ?_, ?_, ?_, ?_⟩
  · have := finrank_span_eq_card hli
    rwa [hrange, Fintype.card_fin] at this
  · refine span_pair_invariant ρ c ?_ ?_
    · rw [hv]; exact Submodule.smul_mem _ _ hvW
    · rw [hcw]; exact Submodule.smul_mem _ _ hwW
  · refine span_pair_invariant ρ y ?_ ?_
    · exact hwW
    · rw [hyw]; exact Submodule.neg_mem _ hvW
  · rintro i ⟨μ, hμ⟩
    have h1 : l ^ i = μ := by
      have := hμ v hvW
      rw [hcv] at this
      exact smul_left_injective K hv0 this
    have h2 : l⁻¹ ^ i = μ := by
      have := hμ w hwW
      rw [hcw'] at this
      exact smul_left_injective K hw0 this
    have h3 : l ^ (2 * i) = 1 := by
      rw [two_mul, pow_add]
      nth_rewrite 2 [h1.trans h2.symm]
      rw [← mul_pow, mul_inv_cancel₀ hl0, one_pow]
    have h4 : 2 ^ t ∣ i := by
      have hd := orderOf_dvd_of_pow_eq_one h3
      rw [horder, pow_succ] at hd
      exact Nat.dvd_of_mul_dvd_mul_right two_pos (by rwa [mul_comm i 2])
    obtain ⟨j, rfl⟩ := h4
    have hz2 : (c ^ 2 ^ t) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact hc
    rw [pow_mul]
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · left; rw [pow_mul, hz2, one_pow]
    · right; rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
  · rintro i ⟨μ, hμ⟩
    have h1 := hμ v hvW
    rw [map_mul, Module.End.mul_apply, ← hw, hcw'] at h1
    have := (LinearIndependent.pair_iff.mp hli) μ (-(l⁻¹ ^ i))
      (by rw [neg_smul, h1, add_neg_cancel])
    exact pow_ne_zero i (inv_ne_zero hl0) (neg_eq_zero.mp this.2)

end Plane

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
