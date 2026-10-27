module

public import CFSG.Assembly.Defs
import CFSG.RankThree.PartOne.SP4GA.Unique

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Assembly

theorem exists_plane {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) {a y : T}
    (hap : a ^ p = 1) (hyp : y ^ p = 1) (ha1 : a ≠ 1) (hcomm : a * y = y * a)
    (hy : y ∉ Subgroup.zpowers a) :
    ∃ A : Subgroup T, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ a ∈ A ∧ y ∈ A := by
  have : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hoa : orderOf a = p := orderOf_eq_prime hap ha1
  have hoy : orderOf y = p := orderOf_eq_prime hyp hy1
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers y = ⊥ := by
    by_contra hne
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hga : (g : T) ∈ Subgroup.zpowers a := g.2.1
    have hgy : (g : T) ∈ Subgroup.zpowers y := g.2.2
    have hg1' : (g : T) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hgp : (g : T) ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hga
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    have hog : orderOf (g : T) = p := orderOf_eq_prime hgp hg1'
    have hle : Subgroup.zpowers (g : T) ≤ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_le]; exact hgy
    have heq : Subgroup.zpowers (g : T) = Subgroup.zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hog, hoy]
    have : y ∈ Subgroup.zpowers (g : T) := by rw [heq]; exact Subgroup.mem_zpowers y
    exact hy ((Subgroup.zpowers_le.mpr hga) this)
  refine ⟨Subgroup.zpowers a ⊔ Subgroup.zpowers y, ?_, ?_, Subgroup.mem_sup_left
    (Subgroup.mem_zpowers a), Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
  · have hform : ∀ g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, ∃ i j : ℤ, g = a ^ i * y ^ j :=
      fun g hg => SP4GA.exists_zpow_mul_of_sup hcomm hg
    have hcomm' : ∀ i j k l : ℤ, (a ^ i * y ^ j) * (a ^ k * y ^ l) = (a ^ k * y ^ l) * (a ^ i * y ^ j) := by
      intro i j k l
      have h1 : Commute a y := hcomm
      have e1 : Commute (a ^ i) (a ^ k) := (Commute.refl a).zpow_zpow i k
      have e2 : Commute (y ^ j) (y ^ l) := (Commute.refl y).zpow_zpow j l
      have e3 : Commute (a ^ i) (y ^ l) := h1.zpow_zpow i l
      have e4 : Commute (y ^ j) (a ^ k) := (h1.zpow_zpow k j).symm
      calc a ^ i * y ^ j * (a ^ k * y ^ l) = a ^ i * (y ^ j * a ^ k) * y ^ l := by group
        _ = a ^ i * (a ^ k * y ^ j) * y ^ l := by rw [e4.eq]
        _ = (a ^ i * a ^ k) * (y ^ j * y ^ l) := by group
        _ = (a ^ k * a ^ i) * (y ^ l * y ^ j) := by rw [e1.eq, e2.eq]
        _ = a ^ k * (a ^ i * y ^ l) * y ^ j := by group
        _ = a ^ k * (y ^ l * a ^ i) * y ^ j := by rw [e3.eq]
        _ = a ^ k * y ^ l * (a ^ i * y ^ j) := by group
    refine ⟨⟨⟨fun g g' => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨i, j, hij⟩ := hform g g.2
      obtain ⟨k, l, hkl⟩ := hform g' g'.2
      apply Subtype.ext
      show (g : T) * g' = g' * g
      rw [hij, hkl]
      exact hcomm' i j k l
    · obtain ⟨i, j, rfl⟩ := hform g hg
      have h1 : Commute (a ^ i) (y ^ j) := (show Commute a y from hcomm).zpow_zpow i j
      rw [h1.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i (p : ℤ),
        mul_comm j (p : ℤ), zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hap, hyp, one_zpow,
        one_zpow, one_mul]
  · rw [SP4GA.card_sup_zpowers hcomm hdisj, hoa, hoy, sq]
