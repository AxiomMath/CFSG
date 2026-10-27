module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.H13.Abs523

variable {V : Type} [CommGroup V]

@[expose] def cmSet (t : MulAut V) : Set V := {w | ∃ u : V, w = t u * u⁻¹}

theorem one_mem_cmSet (t : MulAut V) : (1 : V) ∈ cmSet t := ⟨1, by simp⟩

theorem mul_mem_cmSet (t : MulAut V) {a b : V} (ha : a ∈ cmSet t) (hb : b ∈ cmSet t) :
    a * b ∈ cmSet t := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨u', rfl⟩ := hb
  exact ⟨u * u', by simp only [map_mul, mul_inv]; ac_rfl⟩

theorem inv_mem_cmSet (t : MulAut V) {a : V} (ha : a ∈ cmSet t) : a⁻¹ ∈ cmSet t := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨u⁻¹, by simp only [map_inv, mul_inv, inv_inv]⟩

@[expose] def cmSub (t : MulAut V) : Subgroup V where
  carrier := cmSet t
  mul_mem' := fun {a b} ha hb => mul_mem_cmSet t ha hb
  one_mem' := one_mem_cmSet t
  inv_mem' := fun {a} ha => inv_mem_cmSet t ha

theorem mem_cmSub {t : MulAut V} {w : V} : w ∈ cmSub t ↔ ∃ u : V, w = t u * u⁻¹ := Iff.rfl

theorem mem_zpowers_of_invol {t : MulAut V} (ht : t * t = 1) (y : MulAut V) :
    y ∈ Subgroup.zpowers t → y = 1 ∨ y = t := by
  intro hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, sq]
    exact ht
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem commV_zpowers_le {t : MulAut V} (ht : t * t = 1) :
    CFSG.Quasithin.commV (Subgroup.zpowers t) ≤ cmSub t := by
  unfold CFSG.Quasithin.commV
  apply (Subgroup.closure_le (cmSub t)).mpr
  rintro w ⟨y, hy, u, rfl⟩
  rcases mem_zpowers_of_invol ht y hy with rfl | rfl
  · simpa using one_mem_cmSet t
  · exact ⟨u, rfl⟩

theorem card_cmSub_of_rk {t : MulAut V} [Finite V] (ht : t * t = 1)
    (h : 3 ≤ CFSG.Quasithin.rk ↥(CFSG.Quasithin.commV (Subgroup.zpowers t))) :
    8 ≤ Nat.card ↥(cmSub t) := by
  have hle : Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers t)) ≤ Nat.card ↥(cmSub t) :=
    Subgroup.card_le_of_le (commV_zpowers_le ht)
  have hpos : Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers t)) ≠ 0 := Nat.card_pos.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 3 ∣ Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers t)) :=
    (padicValNat_dvd_iff_le hpos).mpr h
  have := Nat.le_of_dvd (Nat.card_pos) hdvd
  omega

end CFSG.Quasithin.H13.Abs523
