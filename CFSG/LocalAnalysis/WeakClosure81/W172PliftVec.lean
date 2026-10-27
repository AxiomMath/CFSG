module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {Q : Type*} [CommGroup Q]

private lemma w172_plift_mul_inv_mul (a b : Q) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv]

private lemma w172_plift_mul_inv_inv (a b : Q) : (a * b⁻¹)⁻¹ = a⁻¹ * b := by
  rw [mul_inv, inv_inv]

private theorem w172_plift_aux {ι : Type*} (W : Subgroup Q)
    (hodd : ∀ w ∈ W, w * w = 1 → w = 1) (s : Finset ι) (g : ι → Q →* Q)
    (hsW : ∀ i ∈ s, ∀ w ∈ W, g i w ∈ W)
    (hsc : ∀ i ∈ s, ∀ j ∈ s, ∀ x, g i (g j x) = g j (g i x))
    (hs2 : ∀ i ∈ s, ∀ x, g i (g i x) = x) {i₀ : ι} (hi₀ : i₀ ∈ s)
    {q₀ : Q} (hq₀W : q₀ ∈ W) (hq₀inv : g i₀ q₀ = q₀⁻¹) (hq₀1 : q₀ ≠ 1)
    (t : Finset ι) (hts : ∀ i ∈ t, i ∈ s) :
    ∃ q ∈ W, q ≠ 1 ∧ g i₀ q = q⁻¹ ∧ ∀ i ∈ t, g i q = q ∨ g i q = q⁻¹ := by
  classical
  revert hts
  induction t using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨q₀, hq₀W, hq₀1, hq₀inv, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j t hjt ih =>
      intro hts
      have hjs : j ∈ s := hts j (Finset.mem_insert_self j t)
      have hts' : ∀ i ∈ t, i ∈ s := fun i hi => hts i (Finset.mem_insert_of_mem hi)
      obtain ⟨q, hqW, hq1, hqinv, hqeig⟩ := ih hts'
      have hgjqW : g j q ∈ W := hsW j hjs q hqW
      have hgjqinv : g i₀ (g j q) = (g j q)⁻¹ := by
        rw [hsc i₀ hi₀ j hjs q, hqinv, map_inv]
      have hqq : q * q ≠ 1 := fun h => hq1 (hodd q hqW h)
      have hprod : q * g j q * (q * (g j q)⁻¹) = q * q := by
        rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
      have key : ∀ r : Q, r ∈ W → r ≠ 1 → g i₀ r = r⁻¹ →
          (g j r = r ∨ g j r = r⁻¹) →
          (∀ i ∈ t, g i r = r ∨ g i r = r⁻¹) →
          ∃ z ∈ W, z ≠ 1 ∧ g i₀ z = z⁻¹ ∧
            ∀ i ∈ insert j t, g i z = z ∨ g i z = z⁻¹ := by
        intro r hr hr1 hrinv hrj hrt
        exact ⟨r, hr, hr1, hrinv, fun i hi => by
          rcases Finset.mem_insert.mp hi with rfl | hit
          · exact hrj
          · exact hrt i hit⟩
      by_cases hplus : q * g j q = 1
      · have hminus1 : q * (g j q)⁻¹ ≠ 1 := by
          intro h0
          apply hqq
          calc q * q = q * g j q * (q * (g j q)⁻¹) := hprod.symm
            _ = 1 * 1 := by rw [hplus, h0]
            _ = 1 := one_mul 1
        refine key _ (W.mul_mem hqW (W.inv_mem hgjqW)) hminus1 ?_ ?_ ?_
        · rw [map_mul, map_inv, hqinv, hgjqinv, inv_inv, w172_plift_mul_inv_inv]
        · right
          rw [map_mul, map_inv, hs2 j hjs q, w172_plift_mul_inv_inv]
          exact mul_comm _ _
        · intro i hi
          have hij : g i (g j q) = g j (g i q) := hsc i (hts' i hi) j hjs q
          rcases hqeig i hi with h | h
          · left
            rw [map_mul, map_inv, h, hij, h]
          · right
            rw [map_mul, map_inv, h, hij, h, map_inv, inv_inv,
              w172_plift_mul_inv_inv]
      · refine key _ (W.mul_mem hqW hgjqW) hplus ?_ ?_ ?_
        · rw [map_mul, hqinv, hgjqinv, w172_plift_mul_inv_mul]
        · left
          rw [map_mul, hs2 j hjs q]
          exact mul_comm _ _
        · intro i hi
          have hij : g i (g j q) = g j (g i q) := hsc i (hts' i hi) j hjs q
          rcases hqeig i hi with h | h
          · left
            rw [map_mul, h, hij, h]
          · right
            rw [map_mul, h, hij, h, map_inv, w172_plift_mul_inv_mul]

theorem w172_plift_eig_inverted {ι : Type*} (W : Subgroup Q)
    (hodd : ∀ w ∈ W, w * w = 1 → w = 1) (s : Finset ι) (g : ι → Q →* Q)
    (hsW : ∀ i ∈ s, ∀ w ∈ W, g i w ∈ W)
    (hsc : ∀ i ∈ s, ∀ j ∈ s, ∀ x, g i (g j x) = g j (g i x))
    (hs2 : ∀ i ∈ s, ∀ x, g i (g i x) = x) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hact : ∃ x ∈ W, g i₀ x ≠ x) :
    ∃ q ∈ W, q ≠ 1 ∧ g i₀ q = q⁻¹ ∧ ∀ i ∈ s, g i q = q ∨ g i q = q⁻¹ := by
  classical
  obtain ⟨x, hxW, hxne⟩ := hact
  have hq₀W : x⁻¹ * g i₀ x ∈ W := W.mul_mem (W.inv_mem hxW) (hsW i₀ hi₀ x hxW)
  have hq₀inv : g i₀ (x⁻¹ * g i₀ x) = (x⁻¹ * g i₀ x)⁻¹ := by
    rw [map_mul, map_inv, hs2 i₀ hi₀ x, mul_inv, inv_inv]
    exact mul_comm _ _
  have hq₀1 : x⁻¹ * g i₀ x ≠ 1 := by
    intro h0
    apply hxne
    have h1 : x * (x⁻¹ * g i₀ x) = x * 1 := by rw [h0]
    rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h1
  exact w172_plift_aux W hodd s g hsW hsc hs2 hi₀ hq₀W hq₀inv hq₀1 s
    (fun _ hi => hi)

end CFSG.LocalAnalysis.WeakClosure81

end
