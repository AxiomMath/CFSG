module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Theta

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

theorem fixed_span_finrank_le_four_E6 {w : WeylGroup Tag.E6} {ε : ℕ} (hε : ε % 2 = 1)
    (hθθ : ∀ v : Fin Tag.E6.rank → ℤ,
      w • permLattice (exactPerm .E6 ε) (w • permLattice (exactPerm .E6 ε) v) = v)
    {K : Type*} [Field K] {R : Set (Fin Tag.E6.rank → ℤ)}
    (hR : ∀ r ∈ R, w • permLattice (exactPerm .E6 ε) r = r) :
    Module.finrank K (Submodule.span K
      ((fun (r : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) => ((r i : ℤ) : K)) '' R)) ≤ 4 := by
  simp only [exactPerm_E6_of_odd hε] at hθθ hR
  let N : Submodule ℤ (Fin Tag.E6.rank → ℤ) := LinearMap.ker (thetaLinE6 w - LinearMap.id)
  have hmemN : ∀ v, v ∈ N ↔ w • permLattice diagPermE6 v = v := fun v => by
    simp [N, LinearMap.mem_ker, thetaLinE6_apply, sub_eq_zero]
  let B := Module.finBasis ℤ N
  have hfr : Module.finrank ℤ N ≤ 4 := by
    by_contra! h5
    have h5' : 5 ≤ Module.finrank ℤ N := h5
    refine not_linearIndependent_fix_E6 w hθθ
      (f := fun i => (B (Fin.castLE h5' i) : Fin Tag.E6.rank → ℤ))
      (fun i => (hmemN _).1 (B _).2) ?_
    exact (B.linearIndependent.comp _ (Fin.castLE_injective h5')).map' N.subtype
      (Submodule.ker_subtype N)
  let s : Fin (Module.finrank ℤ N) → (Fin Tag.E6.rank → K) :=
    fun k i => (((B k : Fin Tag.E6.rank → ℤ) i : ℤ) : K)
  have hsub : Submodule.span K ((fun (r : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) =>
      ((r i : ℤ) : K)) '' R) ≤ Submodule.span K (Set.range s) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, hr, rfl⟩
    have hrN : r ∈ N := (hmemN r).2 (hR r hr)
    have key : (fun i => ((r i : ℤ) : K)) = ∑ k, ((B.repr ⟨r, hrN⟩ k : ℤ) : K) • s k := by
      ext i
      have h := congrArg (fun v : N => ((v : Fin Tag.E6.rank → ℤ) i)) (B.sum_repr ⟨r, hrN⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h
      have h2 : ((r i : ℤ) : K) =
          ((∑ k, B.repr ⟨r, hrN⟩ k * (B k : Fin Tag.E6.rank → ℤ) i : ℤ) : K) := by
        rw [h]
      simp only [Finset.sum_apply, Pi.smul_apply, s, smul_eq_mul]
      rw [h2]
      push_cast
      rfl
    show (fun i => ((r i : ℤ) : K)) ∈ Submodule.span K (Set.range s)
    rw [key]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have : Module.Finite K (Submodule.span K (Set.range s)) :=
    Module.Finite.span_of_finite K (Set.finite_range s)
  calc _ ≤ Module.finrank K (Submodule.span K (Set.range s)) := Submodule.finrank_mono hsub
    _ ≤ Fintype.card (Fin (Module.finrank ℤ N)) := finrank_range_le_card s
    _ = Module.finrank ℤ N := Fintype.card_fin _
    _ ≤ 4 := hfr

theorem iform_sum_left_E6 {ι : Type*} (s : Finset ι) (f : ι → Fin Tag.E6.rank → ℤ)
    (y : Fin Tag.E6.rank → ℤ) : iform (∑ k ∈ s, f k) y = ∑ k ∈ s, iform (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iform_zero_left_E6]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_left_E6, ih]

theorem theta_add_self_eq_sum_E6 {w : WeylGroup Tag.E6} {ε : ℕ} (hε : ε % 2 = 1)
    (hθθ : ∀ v : Fin Tag.E6.rank → ℤ,
      w • permLattice (exactPerm .E6 ε) (w • permLattice (exactPerm .E6 ε) v) = v)
    {r : Fin 4 → Fin Tag.E6.rank → ℤ} (hroot : ∀ j, IsRoot Tag.E6 (r j))
    (horth : ∀ i j, i ≠ j → iform (r i) (r j) = 0)
    (hfix : ∀ j, w • permLattice (exactPerm .E6 ε) (r j) = r j) (v : Fin Tag.E6.rank → ℤ) :
    w • permLattice (exactPerm .E6 ε) v + v = ∑ j, iform v (r j) • r j := by
  simp only [exactPerm_E6_of_odd hε] at hθθ hfix ⊢
  have hθθ' : ∀ v, thetaLinE6 w (thetaLinE6 w v) = v := hθθ
  have hfix' : ∀ j, thetaLinE6 w (r j) = r j := hfix
  change thetaLinE6 w v + v = _
  set z := thetaLinE6 w v + v with hz
  have hzfix : thetaLinE6 w z = z := by rw [hz, map_add, hθθ']; abel
  have hF : ∀ i : Fin 5, thetaLinE6 w ((Fin.cons z r : Fin 5 → Fin Tag.E6.rank → ℤ) i) =
      (Fin.cons z r : Fin 5 → Fin Tag.E6.rank → ℤ) i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hzfix
    · simpa using hfix' k
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1
    (not_linearIndependent_fix_E6 w hθθ (f := Fin.cons z r) hF)
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have hm : ∀ m, g m.succ = -(g 0 * iform v (r m)) := by
    intro m
    have h := congrArg (fun x => iform x (r m)) hg
    simp only [iform_add_left_E6, iform_sum_left_E6, iform_smul_left_E6,
      iform_zero_left_E6] at h
    rw [Finset.sum_eq_single m (fun k _ hk => by rw [horth k m hk, mul_zero])
      (fun h => absurd (Finset.mem_univ m) h), iform_self_eq_two_of_isRoot_E6 (hroot m)] at h
    have hth : iform (thetaLinE6 w v) (r m) = iform v (r m) := by
      have h' := thetaLinE6_iso w v (r m)
      rwa [hfix' m] at h'
    have hz2 : iform z (r m) = 2 * iform v (r m) := by
      rw [hz, iform_add_left_E6, hth]
      ring
    rw [hz2] at h
    linarith
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hi₀
    induction i₀ using Fin.cases with
    | zero => exact h0
    | succ k => rw [hm k, h0]; ring
  have h3 : g 0 • (z - ∑ j, iform v (r j) • r j) = 0 := by
    rw [smul_sub, Finset.smul_sum]
    have : ∀ k, g k.succ • r k = -(g 0 • iform v (r k) • r k) := fun k => by
      rw [hm k, neg_smul, mul_smul]
    simp only [this, Finset.sum_neg_distrib] at hg
    rw [sub_eq_add_neg]
    exact hg
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_left hg0)

theorem sum_theta_mul_eq_neg_E6 {w : WeylGroup Tag.E6} {ε : ℕ} (hε : ε % 2 = 1)
    (hθθ : ∀ v : Fin Tag.E6.rank → ℤ,
      w • permLattice (exactPerm .E6 ε) (w • permLattice (exactPerm .E6 ε) v) = v)
    {r : Fin 4 → Fin Tag.E6.rank → ℤ} (hroot : ∀ j, IsRoot Tag.E6 (r j))
    (horth : ∀ i j, i ≠ j → iform (r i) (r j) = 0)
    (hfix : ∀ j, w • permLattice (exactPerm .E6 ε) (r j) = r j)
    {K : Type*} [CommRing K] (z : Fin Tag.E6.rank → K)
    (hz : ∀ j, ∑ i, ((r j i : ℤ) : K) * z i = 0) (v : Fin Tag.E6.rank → ℤ) :
    ∑ i, (((w • permLattice (exactPerm .E6 ε) v) i : ℤ) : K) * z i
      = -∑ i, ((v i : ℤ) : K) * z i := by
  have h := theta_add_self_eq_sum_E6 hε hθθ hroot horth hfix v
  have h2 : ∑ i, ((((w • permLattice (exactPerm .E6 ε) v + v) i : ℤ)) : K) * z i = 0 := by
    have e : ∀ i, (((w • permLattice (exactPerm .E6 ε) v + v) i : ℤ) : K) =
        ∑ j, ((iform v (r j) : ℤ) : K) * ((r j i : ℤ) : K) := by
      intro i
      rw [h]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rfl
    simp only [e, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hz j, mul_zero]
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib] at h2
  linear_combination h2

end CFSG.StandardType.KGCentE6
