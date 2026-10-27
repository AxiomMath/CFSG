module

public import CFSG.RankThree.Classical.CentralPairing

public section

namespace CFSG.RankThree.PartOne.SLB4B

open CFSG.RankThree.Classical

variable {Y X : Type*} [Group Y] [Group X] {φ : Y →* X} (hφ : Function.Surjective φ)
  {V : Type*} [AddCommGroup V] (ρ : Multiplicative V →* X) (hZ : φ.ker ≤ Subgroup.center Y)
include hZ

theorem liftPair_eq_one_of_opposite_signs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {v w : V}
    (hpv : p • v = 0) (hpw : p • w = 0) (g : X)
    (hv : g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd v))
    (hw : g * ρ (Multiplicative.ofAdd w) * g⁻¹ = (ρ (Multiplicative.ofAdd w))⁻¹) :
    liftPair hφ ρ v w = 1 := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hnw : (p - 1) • w = -w := by
    have : (p - 1) • w + w = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel hp1, hpw]
    exact eq_neg_of_add_eq_zero_left this
  have hw' : g * ρ (Multiplicative.ofAdd w) * g⁻¹ = ρ (Multiplicative.ofAdd ((p - 1) • w)) := by
    rw [hnw, ofAdd_neg, map_inv, hw]
  have hv' : g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd ((1 : ℕ) • v)) := by
    rw [one_smul, hv]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine liftPair_eq_one_of_weight hφ ρ hZ hp hpv (s := 1) (t := p - 1) (by omega) ?_
    (liftPair_conj' hφ ρ hZ g hv' hw')
  rw [one_mul]
  have : p - 1 - 1 = p - 2 := by omega
  rw [this]
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem liftPair_swap (v w : V) : liftPair hφ ρ w v = (liftPair hφ ρ v w)⁻¹ := by
  have h := liftPair_add_left hφ ρ hZ v w (v + w)
  rw [liftPair_self hφ ρ (v + w), liftPair_add_right hφ ρ hZ, liftPair_add_right hφ ρ hZ,
    liftPair_self hφ ρ v, liftPair_self hφ ρ w, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem liftPair_eq_one_of_opposite_signs' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {v w : V}
    (hpv : p • v = 0) (hpw : p • w = 0) (g : X)
    (hv : g * ρ (Multiplicative.ofAdd v) * g⁻¹ = (ρ (Multiplicative.ofAdd v))⁻¹)
    (hw : g * ρ (Multiplicative.ofAdd w) * g⁻¹ = ρ (Multiplicative.ofAdd w)) :
    liftPair hφ ρ v w = 1 := by
  have h := liftPair_eq_one_of_opposite_signs hφ ρ hZ hp hp2 hpw hpv g hw hv
  rw [liftPair_swap hφ ρ hZ] at h
  exact inv_eq_one.mp h

include hφ in
theorem exists_lift_pow_eq_one_of_inverted {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {v : V}
    (hpv : p • v = 0) (g : X)
    (hg : g * ρ (Multiplicative.ofAdd v) * g⁻¹ = (ρ (Multiplicative.ofAdd v))⁻¹) :
    ∃ z : Y, φ z = ρ (Multiplicative.ofAdd v) ∧ z ^ p = 1 := by
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨y, hy⟩ := hφ (ρ (Multiplicative.ofAdd v))
  obtain ⟨ĝ, hĝ⟩ := hφ g
  have hker : ∀ a, φ a = 1 → a ∈ Subgroup.center Y := fun a ha => hZ (MonoidHom.mem_ker.mpr ha)
  set c : Y := ĝ * y * ĝ⁻¹ * y with hc
  have hcker : φ c = 1 := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, hĝ, hy, hg, inv_mul_cancel]
  have hcC : c ∈ Subgroup.center Y := hker c hcker
  have hwker : φ (y ^ p) = 1 := by
    rw [map_pow, hy, ← map_pow, ← ofAdd_nsmul, hpv, ofAdd_zero, map_one]
  have hwC : y ^ p ∈ Subgroup.center Y := hker _ hwker
  have hcom : ∀ {a : Y}, a ∈ Subgroup.center Y → ∀ b : Y, Commute a b := fun {a} ha b =>
    (Subgroup.mem_center_iff.mp ha b).symm
  have h1 : ĝ * y * ĝ⁻¹ = c * y⁻¹ := by
    rw [hc, mul_inv_cancel_right]
  have h2 : y ^ p = c ^ p * (y ^ p)⁻¹ := by
    have e1 : (ĝ * y * ĝ⁻¹) ^ p = y ^ p := by
      rw [conj_pow, Subgroup.mem_center_iff.mp hwC ĝ, mul_inv_cancel_right]
    have e2 : (ĝ * y * ĝ⁻¹) ^ p = c ^ p * (y ^ p)⁻¹ := by
      rw [h1, Commute.mul_pow (hcom hcC y⁻¹), inv_pow]
    exact e1.symm.trans e2
  have h3 : (y ^ p) ^ 2 = c ^ p := by
    have : y ^ p * y ^ p = c ^ p := by
      calc y ^ p * y ^ p = c ^ p * (y ^ p)⁻¹ * y ^ p := by rw [← h2]
        _ = c ^ p := inv_mul_cancel_right _ _
    rwa [sq]
  let _ : CommGroup (Subgroup.center Y) := centerCommGroup Y
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup.center Y, (C : Y) = c := ⟨⟨c, hcC⟩, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup.center Y, (W : Y) = y ^ p := ⟨⟨y ^ p, hwC⟩, rfl⟩
  have hCW : W ^ 2 = C ^ p := Subtype.ext (by
    change (W : Y) ^ 2 = (C : Y) ^ p
    rw [hWdef, hCdef, h3])
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup.center Y, M = C ^ (k + 1) * W⁻¹ := ⟨_, rfl⟩
  have hMp : M ^ p = W := by
    rw [hMdef]
    calc (C ^ (k + 1) * W⁻¹) ^ p = (C ^ p) ^ (k + 1) * (W ^ p)⁻¹ := by
          rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k + 1) p]
      _ = (W ^ 2) ^ (k + 1) * (W ^ p)⁻¹ := by rw [hCW]
      _ = W := by rw [hk]; group
  have hMker : φ (M : Y) = 1 := by
    have : (M : Y) = c ^ (k + 1) * (y ^ p)⁻¹ := by
      rw [hMdef]
      change (C : Y) ^ (k + 1) * ((W : Y))⁻¹ = _
      rw [hCdef, hWdef]
    rw [this, map_mul, map_pow, hcker, one_pow, map_inv, hwker, inv_one, one_mul]
  refine ⟨y * (M : Y)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hMker, inv_one, mul_one, hy]
  · have hMpY : (M : Y) ^ p = y ^ p := by
      have := congrArg Subtype.val hMp
      change (M : Y) ^ p = (W : Y) at this
      rw [this, hWdef]
    rw [Commute.mul_pow ((hcom M.2 y).symm.inv_right), inv_pow, hMpY, mul_inv_cancel]

omit hZ in
theorem exists_lift_pow_eq_one_of_gen {p : ℕ} (S : Set V) (hS : AddSubgroup.closure S = ⊤)
    (hcomm : ∀ x ∈ ρ.range.comap φ, ∀ y ∈ ρ.range.comap φ, x * y = y * x)
    (hgen : ∀ a ∈ S, ∃ z : Y, φ z = ρ (Multiplicative.ofAdd a) ∧ z ^ p = 1) :
    ∀ e ∈ ρ.range, ∃ x : Y, φ x = e ∧ x ^ p = 1 := by
  have hall : ∀ v : V, ∃ x : Y, φ x = ρ (Multiplicative.ofAdd v) ∧ x ^ p = 1 := by
    intro v
    have hv : v ∈ AddSubgroup.closure S := by rw [hS]; trivial
    induction hv using AddSubgroup.closure_induction with
    | mem a ha => exact hgen a ha
    | zero => exact ⟨1, by simp, one_pow p⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hap⟩ := hx
      obtain ⟨b, hb, hbp⟩ := hy
      have hac : a ∈ ρ.range.comap φ := ⟨Multiplicative.ofAdd x, ha.symm⟩
      have hbc : b ∈ ρ.range.comap φ := ⟨Multiplicative.ofAdd y, hb.symm⟩
      refine ⟨a * b, by rw [map_mul, ha, hb, ← map_mul, ← ofAdd_add], ?_⟩
      rw [Commute.mul_pow (hcomm a hac b hbc), hap, hbp, one_mul]
    | neg x _ hx =>
      obtain ⟨a, ha, hap⟩ := hx
      exact ⟨a⁻¹, by rw [map_inv, ha, ofAdd_neg, map_inv], by rw [inv_pow, hap, inv_one]⟩
  rintro e ⟨m, rfl⟩
  exact hall m.toAdd

omit hZ in
theorem liftPair_eq_one_of_gen (hZ : φ.ker ≤ Subgroup.center Y) (S : Set V)
    (hS : AddSubgroup.closure S = ⊤)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, liftPair hφ ρ a b = 1) (v w : V) : liftPair hφ ρ v w = 1 := by
  have hright : ∀ a ∈ S, ∀ w : V, liftPair hφ ρ a w = 1 := by
    intro a ha w
    have hw : w ∈ AddSubgroup.closure S := by rw [hS]; trivial
    induction hw using AddSubgroup.closure_induction with
    | mem b hb => exact hpair a ha b hb
    | zero => exact liftPair_zero_right hφ ρ hZ a
    | add x y _ _ hx hy => rw [liftPair_add_right hφ ρ hZ, hx, hy, one_mul]
    | neg x _ hx =>
      have h := liftPair_add_right hφ ρ hZ a x (-x)
      rw [add_neg_cancel, liftPair_zero_right hφ ρ hZ, hx, one_mul] at h
      exact h.symm
  have hv : v ∈ AddSubgroup.closure S := by rw [hS]; trivial
  induction hv using AddSubgroup.closure_induction with
  | mem a ha => exact hright a ha w
  | zero => exact liftPair_zero_left hφ ρ hZ w
  | add x y _ _ hx hy => rw [liftPair_add_left hφ ρ hZ, hx, hy, one_mul]
  | neg x _ hx =>
    have h := liftPair_add_left hφ ρ hZ x (-x) w
    rw [add_neg_cancel, liftPair_zero_left hφ ρ hZ, hx, one_mul] at h
    exact h.symm

end CFSG.RankThree.PartOne.SLB4B
