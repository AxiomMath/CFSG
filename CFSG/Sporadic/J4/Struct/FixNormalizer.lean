module

public import CFSG.Sporadic.J4.Struct.FixCount

public section

open MulAction

namespace CFSG.Sporadic.J4.Struct

section Five

variable {L : Type*} [Group L] [Finite L]

theorem conj_pow_two_pow {ξ r : L} (hr : r * ξ * r⁻¹ = ξ ^ 2) :
    ∀ k : ℕ, r ^ k * ξ * (r ^ k)⁻¹ = ξ ^ (2 ^ k)
  | 0 => by simp
  | k + 1 => by
    have e : r ^ (k + 1) * ξ * (r ^ (k + 1))⁻¹ = r * (r ^ k * ξ * (r ^ k)⁻¹) * r⁻¹ := by
      rw [pow_succ']
      group
    rw [e, conj_pow_two_pow hr k, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hr, ← pow_mul,
      pow_succ, mul_comm (2 ^ k) 2]

theorem card_normalizer_ge {ξ r : L} (hξ : orderOf ξ = 5) (hr : r * ξ * r⁻¹ = ξ ^ 2) :
    4 * Nat.card (Subgroup.centralizer ({ξ} : Set L)) ≤
      Nat.card (Subgroup.normalizer ((Subgroup.zpowers ξ : Subgroup L) : Set L)) := by
  classical
  have hmem : ∀ (k : ℕ) (c : L), c ∈ Subgroup.centralizer ({ξ} : Set L) →
      r ^ k * c ∈ Subgroup.normalizer ((Subgroup.zpowers ξ : Subgroup L) : Set L) := by
    intro k c hc
    have hc' : c * ξ = ξ * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hx : (r ^ k * c) * ξ * (r ^ k * c)⁻¹ = ξ ^ (2 ^ k) := by
      have e : (r ^ k * c) * ξ * (r ^ k * c)⁻¹ = r ^ k * (c * ξ * c⁻¹) * (r ^ k)⁻¹ := by group
      rw [e, hc', mul_inv_cancel_right, conj_pow_two_pow hr k]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have e2 : (r ^ k * c) * ξ ^ m * (r ^ k * c)⁻¹ = (ξ ^ (2 ^ k)) ^ m := by
      rw [← hx, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [SetLike.mem_coe, e2]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers ξ) _) m
  have hne : ∀ k j : ℕ, j < k → k < 4 → (r ^ j)⁻¹ * r ^ k ∉ Subgroup.centralizer ({ξ} : Set L) := by
    intro k j hjk hk hc
    have e : (r ^ j)⁻¹ * r ^ k = r ^ (k - j) := by
      rw [← Nat.add_sub_cancel' hjk.le, pow_add, inv_mul_cancel_left, Nat.add_sub_cancel_left]
    rw [e] at hc
    have hc' : r ^ (k - j) * ξ = ξ * r ^ (k - j) := Subgroup.mem_centralizer_singleton_iff.1 hc
    have h2 := conj_pow_two_pow hr (k - j)
    rw [hc', mul_inv_cancel_right] at h2
    have h3 : ξ ^ 1 = ξ ^ (2 ^ (k - j)) := by rw [pow_one]; exact h2
    rw [pow_eq_pow_iff_modEq, hξ] at h3
    have hd : k - j < 4 := by omega
    have hd0 : 0 < k - j := by omega
    interval_cases (k - j) <;> simp [Nat.ModEq] at h3
  let f : Fin 4 × Subgroup.centralizer ({ξ} : Set L) →
      Subgroup.normalizer ((Subgroup.zpowers ξ : Subgroup L) : Set L) :=
    fun p => ⟨r ^ (p.1 : ℕ) * p.2, hmem _ _ p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨k, c⟩ ⟨j, d⟩ e
    have e1 : r ^ (k : ℕ) * (c : L) = r ^ (j : ℕ) * d := congrArg Subtype.val e
    have hkj : (k : ℕ) = j := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with h | h
      · apply hne j k h j.isLt
        have : (r ^ (k : ℕ))⁻¹ * r ^ (j : ℕ) = (c : L) * (d : L)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← e1, inv_mul_cancel_left]
        rw [this]
        exact Subgroup.mul_mem _ c.2 (Subgroup.inv_mem _ d.2)
      · apply hne k j h k.isLt
        have : (r ^ (j : ℕ))⁻¹ * r ^ (k : ℕ) = (d : L) * (c : L)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, e1, inv_mul_cancel_left]
        rw [this]
        exact Subgroup.mul_mem _ d.2 (Subgroup.inv_mem _ c.2)
    have hk : k = j := Fin.ext hkj
    subst hk
    have hcd : (c : L) = d := mul_left_cancel e1
    rw [Subtype.ext hcd]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this

theorem card_order_five_mul_le {ξ r : L} (hξ : orderOf ξ = 5) (hr : r * ξ * r⁻¹ = ξ ^ 2)
    (h25 : ¬ 25 ∣ Nat.card L) {c : ℕ} (hc : c ≤ Nat.card (Subgroup.centralizer ({ξ} : Set L))) :
    Nat.card {g : L // orderOf g = 5} * c ≤ Nat.card L := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_zpowers (p := 5) (by norm_num; exact h25) hξ
  have h1 := card_orderOf_eq_le (p := 5) (by norm_num; exact h25) Q
  have hN := card_normalizer_ge hξ hr
  rw [← hQ] at hN
  have hidx := Subgroup.card_mul_index (Subgroup.normalizer ((Q : Subgroup L) : Set L))
  calc Nat.card {g : L // orderOf g = 5} * c
      ≤ ((5 - 1) * (Subgroup.normalizer ((Q : Subgroup L) : Set L)).index) * c :=
        Nat.mul_le_mul_right _ h1
    _ = (Subgroup.normalizer ((Q : Subgroup L) : Set L)).index * (4 * c) := by ring
    _ ≤ (Subgroup.normalizer ((Q : Subgroup L) : Set L)).index *
          Nat.card (Subgroup.normalizer ((Q : Subgroup L) : Set L)) :=
        Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left 4 hc) hN)
    _ = Nat.card L := by rw [mul_comm, hidx]

end Five

section Orbit

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

theorem card_fix_mul_le (q : X) {h r : G} (ho : orderOf h = 5) (hfix : h • q = q)
    (hrq : r • q = q) (hr : r * h * r⁻¹ = h ^ 2) (h25 : ¬ 25 ∣ Nat.card (stabilizer G q))
    {c m : ℕ}
    (hc : c ≤ Nat.card ↥(Subgroup.centralizer ({h} : Set G) ⊓ stabilizer G q))
    (hm : Nat.card (Subgroup.centralizer ({h} : Set G)) ≤ m) :
    Nat.card {x : X // x ∈ orbit G q ∧ h • x = x} * c ≤ m := by
  set L := stabilizer G q with hL
  let hL' : L := ⟨h, hfix⟩
  let rL : L := ⟨r, hrq⟩
  have hoL : orderOf hL' = 5 := by rw [← Subgroup.orderOf_coe]; exact ho
  have hrL : rL * hL' * rL⁻¹ = hL' ^ 2 := Subtype.ext hr
  have hcL : c ≤ Nat.card (Subgroup.centralizer ({hL'} : Set L)) := by
    refine le_trans hc (Nat.card_le_card_of_injective
      (fun x => (⟨⟨x.1, (Subgroup.mem_inf.1 x.2).2⟩, ?_⟩ :
        Subgroup.centralizer ({hL'} : Set L))) ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).1)
    · intro x y e
      exact Subtype.ext (congrArg (fun z : Subgroup.centralizer ({hL'} : Set L) => ((z : L) : G)) e)
  have h1 := card_order_five_mul_le hoL hrL h25 hcL
  have hinj : Nat.card {s : G // s ∈ L ∧ IsConj h s} ≤ Nat.card {g : L // orderOf g = 5} := by
    refine Nat.card_le_card_of_injective (fun s => ⟨⟨s.1, s.2.1⟩, ?_⟩) ?_
    · rw [← Subgroup.orderOf_coe, Subgroup.coe_mk]
      obtain ⟨c', hc'⟩ := isConj_iff.1 s.2.2
      rw [← hc']
      exact (orderOf_injective (MulAut.conj c').toMonoidHom (MulAut.conj c').injective h).trans ho
    · intro s t e
      exact Subtype.ext (congrArg (fun g : {g : L // orderOf g = 5} => ((g.1 : L) : G)) e)
  have e := card_fix_orbit_mul q h
  have hpos : 0 < Nat.card L := Nat.card_pos
  have key : Nat.card {x : X // x ∈ orbit G q ∧ h • x = x} * c * Nat.card L ≤ m * Nat.card L := by
    calc Nat.card {x : X // x ∈ orbit G q ∧ h • x = x} * c * Nat.card L
        = (Nat.card {x : X // x ∈ orbit G q ∧ h • x = x} * Nat.card L) * c := by ring
      _ = Nat.card (Subgroup.centralizer ({h} : Set G)) *
            Nat.card {s : G // s ∈ L ∧ IsConj h s} * c := by rw [e]
      _ ≤ m * (Nat.card {g : L // orderOf g = 5} * c) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul hm (Nat.mul_le_mul_right _ hinj)
      _ ≤ m * Nat.card L := Nat.mul_le_mul_left _ h1
  exact Nat.le_of_mul_le_mul_right key hpos

end Orbit

end CFSG.Sporadic.J4.Struct

end
