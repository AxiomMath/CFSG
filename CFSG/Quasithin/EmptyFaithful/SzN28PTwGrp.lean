module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace SzN28P

section Grp

variable {P : Type*} [Group P] {t s : P}

noncomputable def tw12_prodHom (hc : Commute t s) :
    ↥(Subgroup.zpowers t) × ↥(Subgroup.zpowers s) →* P :=
  MonoidHom.noncommCoprod (Subgroup.zpowers t).subtype (Subgroup.zpowers s).subtype
    (fun m n => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp m.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp n.2
      simp only [Subgroup.coe_subtype]
      rw [← hi, ← hj]
      exact hc.zpow_zpow i j)

theorem tw12_prodHom_range (hc : Commute t s) :
    (tw12_prodHom hc).range = Subgroup.zpowers t ⊔ Subgroup.zpowers s := by
  rw [tw12_prodHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

theorem tw12_mem_sup (hc : Commute t s) {e : P}
    (he : e ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s) : ∃ i j : ℤ, e = t ^ i * s ^ j := by
  rw [← tw12_prodHom_range hc] at he
  obtain ⟨⟨m, n⟩, rfl⟩ := he
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp m.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp n.2
  refine ⟨i, j, ?_⟩
  simp [tw12_prodHom, MonoidHom.noncommCoprod_apply, hi, hj]

theorem tw12_card_sup (ht : t ^ 3 = 1) (ht1 : t ≠ 1) (hs : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hc : Commute t s) (hd : Disjoint (Subgroup.zpowers t) (Subgroup.zpowers s)) :
    Nat.card ↥(Subgroup.zpowers t ⊔ Subgroup.zpowers s) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (tw12_prodHom hc) := by
    refine (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨Subtype.val_injective,
      Subtype.val_injective, ?_⟩
    simpa [Subgroup.range_subtype] using hd
  rw [← tw12_prodHom_range hc, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ht ht1,
    orderOf_eq_prime hs hs1]

theorem tw12_sup_comm (hc : Commute t s) {e f : P}
    (he : e ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s)
    (hf : f ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s) : e * f = f * e := by
  obtain ⟨i, j, rfl⟩ := tw12_mem_sup hc he
  obtain ⟨k, l, rfl⟩ := tw12_mem_sup hc hf
  have h1 : Commute (t ^ i) (t ^ k) := (Commute.refl t).zpow_zpow i k
  have h2 : Commute (s ^ j) (s ^ l) := (Commute.refl s).zpow_zpow j l
  have h3 : Commute (t ^ i) (s ^ l) := hc.zpow_zpow i l
  have h4 : Commute (s ^ j) (t ^ k) := (hc.zpow_zpow k j).symm
  calc t ^ i * s ^ j * (t ^ k * s ^ l) = t ^ i * (s ^ j * t ^ k) * s ^ l := by group
    _ = t ^ i * (t ^ k * s ^ j) * s ^ l := by rw [h4.eq]
    _ = (t ^ i * t ^ k) * (s ^ j * s ^ l) := by group
    _ = (t ^ k * t ^ i) * (s ^ l * s ^ j) := by rw [h1.eq, h2.eq]
    _ = t ^ k * (t ^ i * s ^ l) * s ^ j := by group
    _ = t ^ k * (s ^ l * t ^ i) * s ^ j := by rw [h3.eq]
    _ = t ^ k * s ^ l * (t ^ i * s ^ j) := by group

theorem tw12_sup_pow (ht : t ^ 3 = 1) (hs : s ^ 3 = 1) (hc : Commute t s) {e : P}
    (he : e ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s) : e ^ 3 = 1 := by
  obtain ⟨i, j, rfl⟩ := tw12_mem_sup hc he
  have h3 : Commute (t ^ i) (s ^ j) := hc.zpow_zpow i j
  have key : ∀ (a : P) (k : ℤ), a ^ 3 = 1 → (a ^ k) ^ 3 = 1 := fun a k h => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  rw [h3.mul_pow, key t i ht, key s j hs, one_mul]

end Grp

end SzN28P

end CFSG.Quasithin
