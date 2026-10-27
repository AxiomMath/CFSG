module

public import CFSG.Quasithin.EmptyFaithful.R3c12Cfg

public section

namespace CFSG.Quasithin.R3c12

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

set_option maxRecDepth 100000 in
theorem a6_no_six : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 → g ^ 6 = 1 →
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem alt6_no_order_six (g : alternatingGroup (Fin 6)) (h6 : g ^ 6 = 1) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  have h := a6_no_six (g : Equiv.Perm (Fin 6)) (Equiv.Perm.mem_alternatingGroup.mp g.2)
    (by simpa using congrArg Subtype.val h6)
  rcases h with h | h
  · exact Or.inl (Subtype.ext (by simpa using h))
  · exact Or.inr (Subtype.ext (by simpa using h))

theorem alt6_no_cent {e a : alternatingGroup (Fin 6)} (he : e ^ 3 = 1) (he1 : e ≠ 1)
    (ha : a * a = 1) (ha1 : a ≠ 1) (hc : e * a = a * e) : False := by
  have hcomm : Commute e a := hc
  have h6 : (e * a) ^ 6 = 1 := by
    rw [hcomm.mul_pow]
    have : a ^ 6 = 1 := by
      have : a ^ 2 = 1 := by rw [sq]; exact ha
      calc a ^ 6 = (a ^ 2) ^ 3 := by rw [← pow_mul]
        _ = 1 := by rw [this, one_pow]
    rw [this, mul_one]
    calc e ^ 6 = (e ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [he, one_pow]
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact ha
  have ha3 : a ^ 3 = a := by
    calc a ^ 3 = a ^ 2 * a := by rw [pow_succ]
      _ = a := by rw [ha2, one_mul]
  rcases alt6_no_order_six (e * a) h6 with h | h
  ·
    rw [hcomm.mul_pow, ha2, mul_one] at h
    apply he1
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [he, h]; group
  · rw [hcomm.mul_pow, he, ha3, one_mul] at h
    exact ha1 h

theorem not_clConfig_alt6 : ¬ ClConfig (alternatingGroup (Fin 6)) := by
  rintro ⟨T, V, e, -, -, hV4, hV2, -, he1, he3, hec⟩
  obtain ⟨v, hv⟩ : ∃ v : ↥V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  exact alt6_no_cent he3 he1 (hV2 v v.2) (fun h => hv (Subtype.ext h)) (hec v v.2)

theorem not_clConfig_of_alt6 {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 6)) :
    ¬ ClConfig X := fun h => not_clConfig_alt6 (h.map φ)

end CFSG.Quasithin.R3c12
