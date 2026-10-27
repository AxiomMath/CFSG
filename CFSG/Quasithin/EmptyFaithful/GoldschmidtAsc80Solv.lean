module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin.E2P.Asc80

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_abelian_normal {Y : Subgroup G} (hs : Group.IsSolvable ↥Y) (hY : Y ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ Y ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
  have hex : ∃ k, derivedSeries ↥Y k = ⊥ := hs.solvable
  classical
  set m := Nat.find hex with hm
  have hmspec : derivedSeries ↥Y m = ⊥ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hmspec
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ (⊥ : Subgroup ↥Y) := by rw [← hmspec]; trivial
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hkne : derivedSeries ↥Y k ≠ ⊥ := Nat.find_min hex (by omega)
  have hcomm : ⁅derivedSeries ↥Y k, derivedSeries ↥Y k⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← hk]
    exact hmspec
  have : (derivedSeries ↥Y k).Normal := derivedSeries_normal ↥Y k
  refine ⟨(derivedSeries ↥Y k).map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h
    apply hkne
    rw [eq_bot_iff]
    intro d hd
    have : (d : G) ∈ (derivedSeries ↥Y k).map Y.subtype := ⟨d, hd, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup ↥Y) :=
      hcomm ▸ Subgroup.commutator_mem_commutator ha hb
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp h1
    have h3 : a * b = b * a := by
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h2, one_mul]
    exact congrArg Subtype.val h3
  · rintro y hy _ ⟨a, ha, rfl⟩
    refine ⟨⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹, ?_, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance a ha ⟨y, hy⟩

theorem exists_primary_normal {Y : Subgroup G} (hs : Group.IsSolvable ↥Y) (hY : Y ≠ ⊥) :
    ∃ (r : ℕ) (N : Subgroup G), r.Prime ∧ r ∣ Nat.card G ∧ N ≤ Y ∧ N ≠ ⊥ ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ a ∈ N, a ^ r = 1) ∧
      ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N := by
  obtain ⟨A, hAY, hAne, hAcomm, hAnorm⟩ := exists_abelian_normal hs hY
  have hcard : Nat.card A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) r hrd
  let N : Subgroup G :=
    { carrier := {a | a ∈ A ∧ a ^ r = 1}
      one_mem' := ⟨A.one_mem, one_pow r⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        have hc : Commute a b := hAcomm a ha.1 b hb.1
        rw [hc.mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hxN : (x : G) ∈ N := ⟨x.2, by
    have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    exact congrArg Subtype.val h1⟩
  have hx1 : (x : G) ≠ 1 := fun h => by
    have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    exact hr.ne_one hx.symm
  refine ⟨r, N, hr, hrd.trans (Subgroup.card_subgroup_dvd_card A), fun a ha => hAY ha.1,
    fun h => hx1 (Subgroup.mem_bot.mp (h ▸ hxN)), fun a ha b hb => hAcomm a ha.1 b hb.1,
    fun a ha => ha.2, fun y hy a ha => ⟨hAnorm y hy a ha.1, ?_⟩⟩
  rw [conj_pow, ha.2, mul_one, mul_inv_cancel]

end CFSG.Quasithin.E2P.Asc80
