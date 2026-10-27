module

public import CFSG.Quasithin.H13.GoldschmidtU43Act

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def FixedSing (x : OC) : Prop :=
  Ord3 x.cols → ∀ v : V4, q v = 0 → v ≠ 0 → app x.cols v ≠ v

instance (x : OC) : Decidable (FixedSing x) :=
  inferInstanceAs (Decidable (Ord3 x.cols → ∀ v : V4, q v = 0 → v ≠ 0 → app x.cols v ≠ v))

theorem fixed_sing : ∀ x : OC, Ord3 x.cols → ∀ v : V4, q v = 0 → v ≠ 0 → app x.cols v ≠ v := by
  have h : ∀ x : OC, FixedSing x := by decide +kernel
  exact h

theorem card_sing : Nat.card {v : V4 // q v = 0 ∧ v ≠ 0} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem bq_nondeg : ∀ v : V4, v ≠ 0 → ∃ w : V4, bq v w = 1 := by
  decide +kernel

theorem bq_comm (v w : V4) : bq v w = bq w v := by
  unfold bq
  rw [add_comm v w]
  ring

theorem exists_pow_orderOf_three {α : Type*} [Group α] {s : α} (hs : s ≠ 1)
    (h9 : orderOf s ∣ 9) : ∃ k : ℕ, orderOf (s ^ k) = 3 := by
  have hne : orderOf s ≠ 1 := fun h1 => hs (orderOf_eq_one_iff.mp h1)
  have h0 : orderOf s ≠ 0 := by
    intro h0
    rw [h0] at h9
    exact absurd (Nat.eq_zero_of_zero_dvd h9) (by norm_num)
  have h3 : 3 ∣ orderOf s := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (by simpa using h9 : orderOf s ∣ 3 ^ 2)
    interval_cases k
    · exact absurd hk' hne
    · rw [hk']; simp
    · rw [hk']; norm_num
  exact ⟨orderOf s / 3, orderOf_pow_orderOf_div h0 h3⟩

theorem fixed_pow {s : MulAut (Multiplicative V4)} {x : Multiplicative V4} (hx : s x = x) (k : ℕ) :
    (s ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem exists_mem_of_card_nine {R : Subgroup (MulAut (Multiplicative V4))} (hR : R ≤ Oq)
    (hcard : Nat.card R = 9) {v w : V4} (hv : q v = 0) (hv0 : v ≠ 0) (hw : q w = 0)
    (hw0 : w ≠ 0) : ∃ r ∈ R, Multiplicative.toAdd (r (Multiplicative.ofAdd v)) = w := by
  have hmem : ∀ r : R, q (Multiplicative.toAdd ((r : MulAut (Multiplicative V4))
      (Multiplicative.ofAdd v))) = 0 ∧
      Multiplicative.toAdd ((r : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v)) ≠ 0 := by
    intro r
    refine ⟨?_, ?_⟩
    · rw [hR r.2 v]
      exact hv
    · intro h0
      apply hv0
      have h1 : (r : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v) = 1 :=
        Multiplicative.toAdd.injective (by simpa using h0)
      have h2 := (r : MulAut (Multiplicative V4)).injective (h1.trans (map_one _).symm)
      simpa using congrArg Multiplicative.toAdd h2
  let f : R → {u : V4 // q u = 0 ∧ u ≠ 0} := fun r =>
    ⟨Multiplicative.toAdd ((r : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v)), hmem r⟩
  have hinj : Function.Injective f := by
    intro r r' hrr
    have hv' : (r : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v) =
        (r' : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v) :=
      Multiplicative.toAdd.injective (congrArg Subtype.val hrr)
    by_contra hne
    set s : R := r⁻¹ * r' with hs
    have hs1 : s ≠ 1 := fun h1 => hne (by
      have := congrArg (r * ·) h1
      simpa [hs] using this.symm)
    have hsfix : (s : MulAut (Multiplicative V4)) (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd v := by
      rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, ← hv']
      simp
    have hord : orderOf (s : MulAut (Multiplicative V4)) ∣ 9 := by
      rw [Subgroup.orderOf_coe, ← hcard]
      exact orderOf_dvd_natCard s
    obtain ⟨k, hk⟩ := exists_pow_orderOf_three
      (s := (s : MulAut (Multiplicative V4))) (fun h1 => hs1 (Subtype.ext h1)) hord
    set s' : MulAut (Multiplicative V4) := (s : MulAut (Multiplicative V4)) ^ k with hs'
    have hs'R : s' ∈ Oq := hR (pow_mem s.2 k)
    have hOrd3 : Ord3 (toOC ⟨s', hs'R⟩).cols := by
      rw [toOC_mk_cols, ord3_colsOf_iff]
      refine ⟨fun h1 => by rw [h1, orderOf_one] at hk; omega, ?_⟩
      have := pow_orderOf_eq_one s'
      rwa [hk] at this
    have hfix := fixed_sing _ hOrd3 v hv hv0
    apply hfix
    rw [toOC_mk_cols, ← app_colsOf, hs', fixed_pow hsfix k]
    simp
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, card_sing]
  obtain ⟨r, hr⟩ := hbij.2 ⟨w, hw, hw0⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem exists_act_eq [Finite G] {v w : V4} (hv : q v = 0) (hv0 : v ≠ 0) (hw : q w = 0)
    (hw0 : w ≠ 0) :
    ∃ x : ↥(Hz z), Multiplicative.toAdd (h.act x (Multiplicative.ofAdd v)) = w := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(h.act).range) 3
    (n := 2) (by rw [h.card_range_act]; norm_num)
  have hR : Nat.card (K.map (h.act).range.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (h.act).range.subtype_injective, hK]
    norm_num
  have hRle : K.map (h.act).range.subtype ≤ Oq := by
    rintro _ ⟨⟨_, ⟨x, rfl⟩⟩, -, rfl⟩
    exact h.act_mem_Oq x
  obtain ⟨r, ⟨⟨_, ⟨x, rfl⟩⟩, -, rfl⟩, hr⟩ := exists_mem_of_card_nine hRle hR hv hv0 hw hw0
  exact ⟨x, hr⟩

theorem θ_ne_one {t : G} (ht : t ∈ Uz z) (ht1 : t ≠ 1) (htz : t ≠ z) :
    h.θ ⟨t, ht⟩ ≠ 1 := by
  intro h1
  rcases (h.θ_eq_one_iff _).1 h1 with h2 | h2
  · exact ht1 h2
  · exact htz h2

theorem q_θ_eq_zero {t : G} (ht : t ∈ Uz z) (ht2 : t * t = 1) :
    q (Multiplicative.toAdd (h.θ ⟨t, ht⟩)) = 0 := by
  rcases h.sq_cases ⟨t, ht⟩ with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exfalso
    have : t ^ 2 = 1 := by rw [pow_two]; exact ht2
    exact h.z_ne_one (h2.symm.trans this)

theorem exists_comm_eq_z {t : G} (ht : t ∈ Uz z) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ u ∈ Uz z, u * t * u⁻¹ * t⁻¹ = z := by
  have hv0 : Multiplicative.toAdd (h.θ ⟨t, ht⟩) ≠ 0 := fun h0 =>
    h.θ_ne_one ht ht1 htz (Multiplicative.toAdd.injective (by simpa using h0))
  obtain ⟨ω, hω⟩ := bq_nondeg _ hv0
  obtain ⟨u, hu⟩ := h.θ_surj (Multiplicative.ofAdd ω)
  refine ⟨u, u.2, ?_⟩
  have := h.comm_eq u ⟨t, ht⟩
  rw [hu, toAdd_ofAdd, bq_comm, hω, zp_one] at this
  simpa using this

theorem exists_conj [Finite G] {t t' : G} (ht : t ∈ Uz z) (ht1 : t ≠ 1) (htz : t ≠ z)
    (ht2 : t * t = 1)
    (ht' : t' ∈ Uz z) (ht1' : t' ≠ 1) (htz' : t' ≠ z) (ht2' : t' * t' = 1) :
    ∃ x ∈ Hz z, x * t * x⁻¹ = t' := by
  have hv0 : Multiplicative.toAdd (h.θ ⟨t, ht⟩) ≠ 0 := fun h0 =>
    h.θ_ne_one ht ht1 htz (Multiplicative.toAdd.injective (by simpa using h0))
  have hw0 : Multiplicative.toAdd (h.θ ⟨t', ht'⟩) ≠ 0 := fun h0 =>
    h.θ_ne_one ht' ht1' htz' (Multiplicative.toAdd.injective (by simpa using h0))
  obtain ⟨x, hx⟩ := h.exists_act_eq (h.q_θ_eq_zero ht ht2) hv0 (h.q_θ_eq_zero ht' ht2') hw0
  rw [ofAdd_toAdd] at hx
  have hx' : h.θ (conjU x ⟨t, ht⟩) = h.θ ⟨t', ht'⟩ := by
    rw [← h.act_θ]
    exact Multiplicative.toAdd.injective hx
  have hθ : h.θ (conjU x ⟨t, ht⟩ * ⟨t', ht'⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hx']
    exact mul_inv_cancel _
  have hcoe : ((conjU x ⟨t, ht⟩ * ⟨t', ht'⟩⁻¹ : ↥(Uz z)) : G) =
      (x : G) * t * (x : G)⁻¹ * t'⁻¹ := by simp
  rcases (h.θ_eq_one_iff _).1 hθ with h1 | h1
  · rw [hcoe] at h1
    exact ⟨x, x.2, mul_inv_eq_one.mp h1⟩
  · rw [hcoe] at h1
    have e : (x : G) * t * (x : G)⁻¹ = z * t' :=
      calc (x : G) * t * (x : G)⁻¹ = ((x : G) * t * (x : G)⁻¹ * t'⁻¹) * t' := by group
        _ = z * t' := by rw [h1]
    obtain ⟨u, hu, hcomm⟩ := h.exists_comm_eq_z ht' ht1' htz'
    refine ⟨u * x, mul_mem (Uz_le_Hz z hu) x.2, ?_⟩
    have e2 : u * t' * u⁻¹ = z * t' :=
      calc u * t' * u⁻¹ = (u * t' * u⁻¹ * t'⁻¹) * t' := by group
        _ = z * t' := by rw [hcomm]
    have hzu : z * u = u * z := h.z_comm hu
    have e3 : u * z * u⁻¹ = z := by
      rw [← hzu]
      group
    calc u * (x : G) * t * (u * (x : G))⁻¹ = u * ((x : G) * t * (x : G)⁻¹) * u⁻¹ := by group
      _ = u * (z * t') * u⁻¹ := by rw [e]
      _ = (u * z * u⁻¹) * (u * t' * u⁻¹) := by group
      _ = z * (z * t') := by rw [e3, e2]
      _ = t' := by rw [← mul_assoc, h.sq_z, one_mul]

end Hyp

end CFSG.Quasithin.H13.U43
