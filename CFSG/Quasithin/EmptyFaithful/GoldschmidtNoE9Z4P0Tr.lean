module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Off

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U W : Subgroup V}
  {Tb P : Subgroup (MulAut ↥U)}

theorem mem_Qset_iff {V' : Type} [CommGroup V'] [Finite V'] {X Tb' P' : Subgroup (MulAut V')}
    (h : E9Z4Str X Tb' P') {A : Subgroup (MulAut V')} : A ∈ Qset X ↔ IsA2 X A := by
  rw [h.Qset_eq]
  exact ⟨fun hA => h.isA2_iff.mpr hA, fun hA => h.isA2_iff.mp hA⟩

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {y z : M} (hy2 : orderOf y = 2)
    (hz : z ∈ Subgroup.zpowers y) : z = 1 ∨ z = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hmod : y ^ (k % (orderOf y : ℤ)) = y ^ k := zpow_mod_orderOf y k
  rw [hy2] at hmod
  push_cast at hmod
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hmod, h0, zpow_zero]
  · right
    rw [← hmod, h1, zpow_one]

omit [Finite V] in
theorem isA2_zpowers_of_orderOf_two {x : MulAut V} (hxG : x ∈ G) (hx2 : orderOf x = 2) :
    IsA2 G (Subgroup.zpowers x) := by
  have hx1 : x ≠ 1 := fun e => by rw [e] at hx2; simp at hx2
  exact ⟨Subgroup.zpowers_le.mpr hxG,
    fun e => hx1 (Subgroup.mem_bot.mp (e ▸ Subgroup.mem_zpowers x)),
    isElemAbelian2_zpowers_of_sq (by rw [← hx2]; exact pow_orderOf_eq_one x)⟩

theorem isA2_iff_of_suppData (hS : SuppData G U W) (h : E9Z4Str (autSub G U) Tb P)
    {A : Subgroup (MulAut V)} :
    IsA2 G A ↔ ∃ x ∈ G, orderOf x = 2 ∧ A = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hA
    obtain ⟨hAG, hA1, hA2⟩ := hA
    have hres : IsA2 (autSub G U) (autSub A U) := (hS.isA2_autSub_iff hAG).mpr ⟨hAG, hA1, hA2⟩
    obtain ⟨y, -, hy2, hAy⟩ := h.isA2_iff.mp hres
    have key : ∀ (b : MulAut V) (hb : b ∈ A),
        resHom U ⟨b, hS.stab (hAG hb)⟩ = 1 ∨ resHom U ⟨b, hS.stab (hAG hb)⟩ = y := by
      intro b hb
      have hmem : resHom U ⟨b, hS.stab (hAG hb)⟩ ∈ autSub A U :=
        mem_autSub.mpr ⟨⟨b, hS.stab (hAG hb)⟩, hb, rfl⟩
      rw [hAy] at hmem
      exact eq_one_or_eq_of_mem_zpowers hy2 hmem
    have hres1 : ∀ (b : MulAut V) (hb : b ∈ A),
        resHom U ⟨b, hS.stab (hAG hb)⟩ = 1 → b = 1 := by
      intro b hb e
      refine hS.eq_of_resHom_eq (hAG hb) G.one_mem ?_
      rw [e]
      exact (map_one (resHom U)).symm
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
    have hra : resHom U ⟨a, hS.stab (hAG ha)⟩ = y :=
      (key a ha).resolve_left fun e => ha1' (hres1 a ha e)
    refine ⟨a, hAG ha, orderOf_eq_prime (hA2.2 a ha) ha1',
      le_antisymm (fun b hb => ?_) (Subgroup.zpowers_le.mpr ha)⟩
    rcases key b hb with e | e
    · rw [hres1 b hb e]
      exact Subgroup.one_mem _
    · rw [hS.eq_of_resHom_eq (hAG hb) (hAG ha) (e.trans hra.symm)]
      exact Subgroup.mem_zpowers a
  · rintro ⟨x, hx, hx2, rfl⟩
    exact isA2_zpowers_of_orderOf_two hx hx2

theorem Qset_eq_of_suppData (hS : SuppData G U W) (h : E9Z4Str (autSub G U) Tb P) :
    Qset G = {A | ∃ x ∈ G, orderOf x = 2 ∧ A = Subgroup.zpowers x} := by
  ext A
  constructor
  · intro hA
    exact (isA2_iff_of_suppData hS h).mp hA.1.1
  · intro hA
    have hA2 : IsA2 G A := (isA2_iff_of_suppData hS h).mpr hA
    have hres : autSub A U ∈ kRle (autSub G U) 2 2 :=
      (h.mem_Qset_iff).mpr ((hS.isA2_autSub_iff hA2.1).mpr hA2)
    exact (hS.mem_kRle_iff hA2.1 (k := 2) 2 (by norm_num)).mp hres

end E9Z4Str

end CFSG.Quasithin
