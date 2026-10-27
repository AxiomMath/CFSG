module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Grp

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

omit [Finite V] in
theorem isElemAbelian2_zpowers_of_sq {x : MulAut V} (hx2 : x ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers x) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hx2

theorem eq_zpowers_of_isElemAbelian2 (h : E9Z4Str X Tb P) {A : Subgroup (MulAut V)} (hAX : A ≤ X)
    (hA : IsElemAbelian2 A) {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    A = Subgroup.zpowers a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hA.2 a ha) ha1
  refine le_antisymm (fun b hb => ?_) (Subgroup.zpowers_le.mpr ha)
  by_cases hb1 : b = 1
  · rw [hb1]
    exact Subgroup.one_mem _
  · have hb2 : orderOf b = 2 := orderOf_eq_prime (hA.2 b hb) hb1
    rw [h.eq_of_commute_of_involution (hAX hb) (hAX ha) hb2 ha2 (hA.1 b hb a ha)]
    exact Subgroup.mem_zpowers a

theorem isA2_iff (h : E9Z4Str X Tb P) {A : Subgroup (MulAut V)} :
    IsA2 X A ↔ ∃ x ∈ X, orderOf x = 2 ∧ A = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hAX, hA1, hA2⟩
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
    exact ⟨a, hAX ha, orderOf_eq_prime (hA2.2 a ha) ha1', h.eq_zpowers_of_isElemAbelian2 hAX hA2
      ha ha1'⟩
  · rintro ⟨x, hx, hx2, rfl⟩
    have hx1 : x ≠ 1 := fun e => by rw [e] at hx2; simp at hx2
    exact ⟨Subgroup.zpowers_le.mpr hx,
      fun e => hx1 (Subgroup.mem_bot.mp (e ▸ Subgroup.mem_zpowers x)),
      isElemAbelian2_zpowers_of_sq (by rw [← hx2]; exact pow_orderOf_eq_one x)⟩

theorem rAV_eq_two (h : E9Z4Str X Tb P) {A : Subgroup (MulAut V)} (hA : IsA2 X A) : rAV A = 2 := by
  obtain ⟨x, hx, hx2, rfl⟩ := h.isA2_iff.mp hA
  have hrk : rk (Subgroup.zpowers x) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hx2]
    simp
  unfold rAV
  rw [hrk, rkIdx_fixV_zpowers, h.rk_commV_involution hx hx2]
  norm_num

theorem commSeries_two_eq_bot_of_involution (h : E9Z4Str X Tb P) {x : MulAut V}
    (hx2 : orderOf x = 2) : commSeries (Subgroup.zpowers x) 2 = ⊥ :=
  (isQuadratic_iff_commSeries_two _).mp
    (isQuadratic_zpowers h.sq (by rw [← hx2]; exact pow_orderOf_eq_one x))

theorem Qset_eq (h : E9Z4Str X Tb P) :
    Qset X = {A | ∃ x ∈ X, orderOf x = 2 ∧ A = Subgroup.zpowers x} := by
  ext A
  constructor
  · rintro ⟨⟨hA, -⟩, -⟩
    exact h.isA2_iff.mp hA
  · rintro ⟨x, hx, hx2, rfl⟩
    have hA2 : IsA2 X (Subgroup.zpowers x) := h.isA2_iff.mpr ⟨x, hx, hx2, rfl⟩
    exact ⟨⟨hA2, (h.rAV_eq_two hA2).le⟩, h.commSeries_two_eq_bot_of_involution hx2⟩

end E9Z4Str

end CFSG.Quasithin
