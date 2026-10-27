module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.BlueprintB2

open CFSG

variable {G : Type*} [Group G]

theorem isElementaryAbelian_iff {p : ℕ} {A : Subgroup G} :
    IsElementaryAbelian p A ↔
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ p = 1 := by
  constructor
  · intro h
    exact ⟨fun a ha b hb =>
      congrArg Subtype.val (h.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
      fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha⟩
  · rintro ⟨hc, hp⟩
    exact
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (by simpa using hp x x.2) }

theorem isElementaryAbelian_of_le {p : ℕ} {A B : Subgroup G} (hAB : A ≤ B)
    (hB : IsElementaryAbelian p B) : IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_le hB hAB

theorem isElementaryAbelian_bot (p : ℕ) : IsElementaryAbelian p (⊥ : Subgroup G) :=
  isElementaryAbelian_iff.mpr
    ⟨fun a ha b hb => by rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
      fun a ha => by rw [Subgroup.mem_bot.mp ha]; exact one_pow p⟩

theorem isElementaryAbelian_map {p : ℕ} {H : Type*} [Group H] {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (f : G →* H) : IsElementaryAbelian p (A.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map hA _

@[expose] def centerTorsion (p : ℕ) {E : Type*} [Group E] (K : Subgroup E) : Subgroup E where
  carrier := {z | z ∈ (Subgroup.center K).map K.subtype ∧ z ^ p = 1}
  one_mem' := ⟨one_mem _, one_pow p⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, ha, rfl⟩, hap⟩ ⟨⟨b, hb, rfl⟩, hbp⟩
    refine ⟨mul_mem (Subgroup.mem_map_of_mem _ ha) (Subgroup.mem_map_of_mem _ hb), ?_⟩
    have hab : Commute (a : E) b :=
      (show Commute b a from Subgroup.mem_center_iff.mp ha b).symm.map K.subtype
    change (a : E) ^ p = 1 at hap
    change (b : E) ^ p = 1 at hbp
    change ((a : E) * b) ^ p = 1
    rw [hab.mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro _ ⟨hz, hzp⟩
    exact ⟨inv_mem hz, by rw [inv_pow, hzp, inv_one]⟩

theorem mem_centerTorsion_iff {p : ℕ} {K : Subgroup G} {z : G} :
    z ∈ centerTorsion p K ↔ z ∈ K ∧ (∀ k ∈ K, k * z = z * k) ∧ z ^ p = 1 := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hp⟩
    exact ⟨y.2, fun k hk => congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨k, hk⟩), hp⟩
  · rintro ⟨hz, hc, hp⟩
    exact ⟨⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hc k k.2), rfl⟩, hp⟩

theorem centerTorsion_eq_closure (p : ℕ) (K : Subgroup G) :
    centerTorsion p K =
      Subgroup.closure {z : G | z ∈ (Subgroup.center K).map K.subtype ∧ z ^ p = 1} :=
  (Subgroup.closure_eq (centerTorsion p K)).symm

theorem centerTorsion_le (p : ℕ) (K : Subgroup G) : centerTorsion p K ≤ K := fun _ hz =>
  (mem_centerTorsion_iff.mp hz).1

theorem elemThompsonCenterTorsion_eq_centerTorsion (P : Type*) [Group P] (p : ℕ) :
    elemThompsonCenterTorsion P p = centerTorsion p (elemThompson P p) := rfl

end CFSG.Quasithin.BlueprintB2
