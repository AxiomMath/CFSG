module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem card_fixV_of_card_sixteen [Finite V] (hV : Nat.card V = 2 ^ 4) {H : Subgroup (MulAut V)}
    {a : ↥H} {p : ℕ} [Fact p.Prime] (ha : orderOf a = p) (ha1 : a ≠ 1) :
    ∃ d, Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V))) = d ∧ d ∣ 16 ∧ d ≠ 16 ∧
      16 % p = d % p := by
  have ha' : orderOf (a : MulAut V) = p := by
    rw [← ha]
    exact orderOf_injective H.subtype Subtype.val_injective a
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · have := Subgroup.card_subgroup_dvd_card (fixV (Subgroup.zpowers (a : MulAut V)))
    rwa [hV] at this
  · have := card_fixV_ne ha1
    rwa [hV] at this
  · have := card_fixV_modEq ha'
    rw [hV] at this
    exact this

theorem orbitA7Four :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 4 →
      ∀ H : Subgroup (MulAut V), Nonempty (↥H ≃* alternatingGroup (Fin 7)) →
        OrbitLengthsIn H [15] ∧ OrbitsSeparated H := by
  intro V _ _ _ hV H ⟨φ⟩
  have : Fintype ↥H := Fintype.ofFinite _
  have hH : Fintype.card ↥H = 2520 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 5 (by rw [hH]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 7 (by rw [hH]; norm_num)
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; norm_num at hb
  obtain ⟨d5, hd5, hd5d, hd5n, hd5m⟩ := card_fixV_of_card_sixteen hV ha ha1
  obtain ⟨d7, hd7, hd7d, hd7n, hd7m⟩ := card_fixV_of_card_sixteen hV hb hb1
  have h5 : d5 = 1 := by
    have := Nat.le_of_dvd (by norm_num) hd5d
    interval_cases d5 <;> omega
  have h7 : d7 = 2 := by
    have := Nat.le_of_dvd (by norm_num) hd7d
    interval_cases d7 <;> omega
  have hV16 : Nat.card V = 16 := by rw [hV]; norm_num
  have key : ∀ v : V, v ≠ 1 → Nat.card ↥(orbitIn H v) + 1 = Nat.card V := by
    intro v hv
    have hO5 := card_orbitIn_modEq ha v
    have hO7 := card_orbitIn_modEq hb v
    have hFa : orbitIn H v ∩ (fixV (Subgroup.zpowers (a : MulAut V)) : Set V) = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw hwa
      have hbot : fixV (Subgroup.zpowers (a : MulAut V)) = ⊥ := by
        rw [← Subgroup.card_eq_one, hd5, h5]
      have : w ∈ (⊥ : Subgroup V) := hbot ▸ hwa
      exact ne_one_of_mem_orbitIn hv hw (Subgroup.mem_bot.1 this)
    have hFb : (orbitIn H v ∩ (fixV (Subgroup.zpowers (b : MulAut V)) : Set V)).ncard ≤ 1 := by
      have hsub : orbitIn H v ∩ (fixV (Subgroup.zpowers (b : MulAut V)) : Set V) ⊆
          (fixV (Subgroup.zpowers (b : MulAut V)) : Set V) \ {1} := fun w hw =>
        ⟨hw.2, ne_one_of_mem_orbitIn hv hw.1⟩
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_sdiff_singleton_add_one
        (s := (fixV (Subgroup.zpowers (b : MulAut V)) : Set V)) (a := 1) (Subgroup.one_mem _)
        (Set.toFinite _)
      have h3 : ((fixV (Subgroup.zpowers (b : MulAut V)) : Set V)).ncard = 2 := by
        rw [← Nat.card_coe_set_eq]
        exact hd7.trans h7
      omega
    rw [hFa, Nat.card_coe_set_eq (∅ : Set V), Set.ncard_empty] at hO5
    rw [Nat.card_coe_set_eq (orbitIn H v ∩ (fixV (Subgroup.zpowers (b : MulAut V)) : Set V))]
      at hO7
    have hle : Nat.card ↥(orbitIn H v) + 1 ≤ Nat.card V := by
      have hsub : orbitIn H v ⊆ {x | x ≠ 1} := fun x hx => ne_one_of_mem_orbitIn hv hx
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq] at h1
      have := ncard_ne_one (V := V)
      omega
    have hpos : 0 < Nat.card ↥(orbitIn H v) := by
      have : Nonempty ↥(orbitIn H v) := ⟨⟨v, 1, H.one_mem, rfl⟩⟩
      exact Nat.card_pos
    have hm5 : Nat.card ↥(orbitIn H v) % 5 = 0 := by
      unfold Nat.ModEq at hO5
      omega
    have hm7 : Nat.card ↥(orbitIn H v) % 7 ≤ 1 := by
      unfold Nat.ModEq at hO7
      rw [hO7]
      exact (Nat.mod_le _ _).trans hFb
    rw [hV16] at hle ⊢
    have hn : Nat.card ↥(orbitIn H v) ≤ 15 := by omega
    generalize Nat.card ↥(orbitIn H v) = n at hm5 hm7 hpos hn ⊢
    interval_cases n <;> omega
  have h := orbits_of_card_eq H key
  rwa [hV] at h

end CFSG.Quasithin.H13.Orbit
