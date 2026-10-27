module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocQ
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

section Closure

variable {G : Type*} [Group G]

theorem comm_closure_of_gens {z x : G} (hz : z * z = 1) {S : Set G}
    (hzS : ∀ s ∈ S, s * z = z * s) (hS : ∀ s ∈ S, x * s = s * x ∨ x * s = z * (s * x)) :
    ∀ y ∈ Subgroup.closure S, y * z = z * y ∧ (x * y = y * x ∨ x * y = z * (y * x)) := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact ⟨hzS s hs, hS s hs⟩
  | one => exact ⟨by simp, Or.inl (by simp)⟩
  | mul y1 y2 _ _ ih1 ih2 =>
    obtain ⟨hz1, h1⟩ := ih1
    obtain ⟨hz2, h2⟩ := ih2
    refine ⟨by rw [mul_assoc, hz2, ← mul_assoc, hz1, mul_assoc], ?_⟩
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · left
      calc x * (y1 * y2) = (x * y1) * y2 := (mul_assoc _ _ _).symm
        _ = (y1 * x) * y2 := by rw [h1]
        _ = y1 * (x * y2) := mul_assoc _ _ _
        _ = y1 * (y2 * x) := by rw [h2]
        _ = (y1 * y2) * x := (mul_assoc _ _ _).symm
    · right
      calc x * (y1 * y2) = (x * y1) * y2 := (mul_assoc _ _ _).symm
        _ = (y1 * x) * y2 := by rw [h1]
        _ = y1 * (x * y2) := mul_assoc _ _ _
        _ = y1 * (z * (y2 * x)) := by rw [h2]
        _ = (y1 * z) * (y2 * x) := (mul_assoc _ _ _).symm
        _ = (z * y1) * (y2 * x) := by rw [hz1]
        _ = z * (y1 * (y2 * x)) := mul_assoc _ _ _
        _ = z * ((y1 * y2) * x) := by rw [mul_assoc]
    · right
      calc x * (y1 * y2) = (x * y1) * y2 := (mul_assoc _ _ _).symm
        _ = (z * (y1 * x)) * y2 := by rw [h1]
        _ = z * ((y1 * x) * y2) := mul_assoc _ _ _
        _ = z * (y1 * (x * y2)) := by rw [mul_assoc]
        _ = z * (y1 * (y2 * x)) := by rw [h2]
        _ = z * ((y1 * y2) * x) := by rw [mul_assoc]
    · left
      calc x * (y1 * y2) = (x * y1) * y2 := (mul_assoc _ _ _).symm
        _ = (z * (y1 * x)) * y2 := by rw [h1]
        _ = z * ((y1 * x) * y2) := mul_assoc _ _ _
        _ = z * (y1 * (x * y2)) := by rw [mul_assoc]
        _ = z * (y1 * (z * (y2 * x))) := by rw [h2]
        _ = z * ((y1 * z) * (y2 * x)) := by rw [mul_assoc]
        _ = z * ((z * y1) * (y2 * x)) := by rw [hz1]
        _ = z * (z * (y1 * (y2 * x))) := by rw [mul_assoc]
        _ = (z * z) * (y1 * (y2 * x)) := (mul_assoc _ _ _).symm
        _ = (y1 * y2) * x := by rw [hz, one_mul, mul_assoc]
  | inv y _ ih =>
    obtain ⟨hz1, h1⟩ := ih
    have hzi : y⁻¹ * z = z * y⁻¹ := (Commute.inv_left (show Commute y z from hz1)).eq
    refine ⟨hzi, ?_⟩
    rcases h1 with h1 | h1
    · left
      exact (Commute.inv_right (show Commute x y from h1)).eq
    · right
      have h2 : y⁻¹ * x = z * (x * y⁻¹) := by
        calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
          _ = y⁻¹ * (z * (y * x)) * y⁻¹ := by rw [h1]
          _ = (y⁻¹ * z) * (y * x * y⁻¹) := by group
          _ = (z * y⁻¹) * (y * x * y⁻¹) := by rw [hzi]
          _ = z * (x * y⁻¹) := by group
      calc x * y⁻¹ = (z * z) * (x * y⁻¹) := by rw [hz, one_mul]
        _ = z * (z * (x * y⁻¹)) := mul_assoc _ _ _
        _ = z * (y⁻¹ * x) := by rw [← h2]

theorem comm_mem_of_gens {x : G} {S : Set G} {Q : Subgroup G}
    (hN : ∀ y ∈ Subgroup.closure S, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hS : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ Q) :
    ∀ y ∈ Subgroup.closure S, x * y * x⁻¹ * y⁻¹ ∈ Q := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul y1 y2 hy1 _ ih1 ih2 =>
    have h := Q.mul_mem ih1 (hN y1 hy1 _ ih2)
    rwa [show x * y1 * x⁻¹ * y1⁻¹ * (y1 * (x * y2 * x⁻¹ * y2⁻¹) * y1⁻¹) =
      x * (y1 * y2) * x⁻¹ * (y1 * y2)⁻¹ by group] at h
  | inv y hy ih =>
    have h := hN y⁻¹ (Subgroup.inv_mem _ hy) _ (Q.inv_mem ih)
    rwa [show y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ = x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ by group] at h

end Closure

section Cert


theorem Q_comm_gen {x : D} (hx : x ∈ d4Q) {k : ℕ} (hk : k < qGens.size) :
    x * qGH k = qGH k * x ∨ x * qGH k = d4z * (qGH k * x) := by
  obtain ⟨-, -, -, -, h4, -⟩ := locQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_Q hx
  have h := List.all_eq_true.1 (allLt_spec h4 hi) k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  have hg := repE_qGens hk
  rcases h with h | h
  · exact Or.inl (eq_of_repE d4E_injective (repE_mul hrep hg) (h ▸ repE_mul hg hrep))
  · exact Or.inr (eq_of_repE d4E_injective (repE_mul hrep hg)
      (h ▸ repE_mul repE_z0R (repE_mul hg hrep)))

theorem Q_sq_spec {x : D} (hx : x ∈ d4Q) : x * x = 1 ∨ x * x = d4z := by
  obtain ⟨-, -, -, -, -, h5, -⟩ := locQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_Q hx
  have h := allLt_spec h5 hi
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl (mul_eq_of_arr hrep hrep repE_one h)
  · exact Or.inr (mul_eq_of_arr hrep hrep repE_z0R h)

theorem Q_centre_spec {w : D} (hw : w ∈ d4Q) (hc : ∀ k < qGens.size, w * qGH k = qGH k * w) :
    w = 1 ∨ w = d4z := by
  obtain ⟨-, -, -, -, -, -, h6, -⟩ := locQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_Q hw
  have hval := validR_Q hi
  have h := allLt_spec h6 hi
  have hall : ((List.range qGens.size).all fun k => locComm locEQ.El[i]! qGens[k]!) = true := by
    simp only [List.all_eq_true, List.mem_range]
    intro k hk
    rw [locComm_iff hval (validR_qGens hk) hrep (repE_qGens hk)]
    exact hc k hk
  simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl ((eqOneR_iff hval hrep).1 h)
  · exact Or.inr (eq_of_repE d4E_injective hrep (h ▸ repE_z0R))

theorem gen_mem_Q {k : ℕ} (hk : k < qGens.size) : qGH k ∈ d4Q :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

section Struct


theorem d4_hQcomm : ∀ x ∈ d4Q, ∀ y ∈ d4Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = d4z := by
  intro x hx y hy
  obtain ⟨-, hxy⟩ := comm_closure_of_gens (z := d4z) (x := x) d4z_sq.1
    (fun s hs => by
      obtain ⟨k, hk, rfl⟩ := hs
      exact Subgroup.mem_centralizer_singleton_iff.1 (d4Q_le_centralizer (gen_mem_Q hk)))
    (fun s hs => by
      obtain ⟨k, hk, rfl⟩ := hs
      exact Q_comm_gen hx hk) y hy
  rcases hxy with h | h
  · left
    rw [h]
    group
  · right
    rw [h]
    group

theorem d4_hQsq : ∀ x ∈ d4Q, x * x = 1 ∨ x * x = d4z := fun _ hx => Q_sq_spec hx

theorem d4_hQZ : ∀ w ∈ d4Q, (∀ q ∈ d4Q, q * w = w * q) → w = 1 ∨ w = d4z := by
  intro w hw hc
  exact Q_centre_spec hw fun k hk => (hc _ (gen_mem_Q hk)).symm

end Struct

end Cert

section TQ


theorem d4U_le_d4H : d4U ≤ d4H := d4U_le_d4B.trans inf_le_left

theorem gen_comm_mem {x : D} (hx : x ∈ d4U) {k : ℕ} (hk : k < uGens.size) :
    x * uGH k * x⁻¹ * (uGH k)⁻¹ ∈ d4Q := by
  obtain ⟨-, -, -, hinv, -, -, -, -, h8, -⟩ := locQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_T hx
  have hsz : locET.El.size = 4096 := locT_parts.2.1.2
  obtain ⟨-, hrepInv⟩ := repE_inv_of_invOK
    (fun j hj => exists_of_T (by rw [hsz]; exact hj)) hinv (hsz ▸ hi) hrep
  have hm := List.all_eq_true.1 (allLt_spec h8 hi) k (List.mem_range.2 hk)
  obtain ⟨a, ha, harep⟩ := mem_Q_of_memR hm
  have hg := repE_uGens hk
  have e2 : a = x * uGH k * (x⁻¹ * uGH k) := eq_of_repE d4E_injective harep
    (repE_mul (repE_mul hrep hg) (repE_mul hrepInv hg))
  have hginv : (uGH k)⁻¹ = uGH k := inv_eq_of_mul_eq_one_right (uGens_hyp' k hk).2
  rw [hginv, mul_assoc (x * uGH k) x⁻¹ (uGH k), ← e2]
  exact ha

theorem d4_hTQ : ∀ x ∈ d4U, ∀ y ∈ d4U, x * y * x⁻¹ * y⁻¹ ∈ d4Q := by
  intro x hx y hy
  refine comm_mem_of_gens (S := genSet uGH uGens.size) (Q := d4Q) ?_ ?_ y hy
  · intro y hy q hq
    exact d4H_norm_Q y (d4U_le_d4H hy) q hq
  · intro s hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact gen_comm_mem hx hk

end TQ

end CFSG.Quasithin.D4Hex
