module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem orbit_subset_neighborSet {a b : V} (hab : Γ.Adj a b) {H : Subgroup G}
    (hH : H ≤ MulAction.stabilizer G a) : MulAction.orbit ↥H b ⊆ Γ.neighborSet a := by
  rintro _ ⟨h, rfl⟩
  exact F.adj_smul_of_mem_stabilizer (hH h.2) hab

omit F in
theorem relIndex_stabilizer_eq_ncard_orbit (H : Subgroup G) (b : V) :
    (MulAction.stabilizer G b).relIndex H = (MulAction.orbit ↥H b).ncard := by
  rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]

theorem relIndex_stabilizer_eq_valence {a b : V} (hab : Γ.Adj a b) {H : Subgroup G}
    (hH : H ≤ MulAction.stabilizer G a)
    (htr : ∀ u w, Γ.Adj a u → Γ.Adj a w → ∃ h ∈ H, h • u = w) :
    (MulAction.stabilizer G b).relIndex H = Fan86.valence Γ a := by
  rw [relIndex_stabilizer_eq_ncard_orbit]
  have : MulAction.orbit ↥H b = Γ.neighborSet a := by
    refine Set.Subset.antisymm (F.orbit_subset_neighborSet hab hH) fun w hw => ?_
    obtain ⟨h, hh, hhw⟩ := htr b w hab hw
    exact ⟨⟨h, hh⟩, hhw⟩
  rw [this, Fan86.valence, Nat.card_coe_set_eq]

theorem card_eq_valence_mul {a b : V} (hab : Γ.Adj a b) {H : Subgroup G}
    (hH : H ≤ MulAction.stabilizer G a)
    (htr : ∀ u w, Γ.Adj a u → Γ.Adj a w → ∃ h ∈ H, h • u = w) :
    Nat.card ↥H = Fan86.valence Γ a * Nat.card ↥(MulAction.stabilizer G b ⊓ H) := by
  rw [← F.relIndex_stabilizer_eq_valence hab hH htr, Subgroup.relIndex_mul_card]

theorem exists_card_stabilizer (v : V) :
    ∃ k : ℕ, Nat.card ↥(MulAction.stabilizer G v) = Fan86.valence Γ v * 2 ^ k := by
  obtain ⟨b, hb⟩ := F.exists_adj v
  have h := F.card_eq_valence_mul hb (H := MulAction.stabilizer G v) le_rfl (fun u w hu hw => by
    obtain ⟨g, hg, hgu⟩ := F.loc_trans v u w hu hw
    exact ⟨g, hg, hgu⟩)
  have := F.finite_stabilizer_inf b v
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (F.edge_two b v hb.symm)
  exact ⟨k, by rw [h, hk]⟩

theorem fixes_or_trans (v : V) {H : Subgroup G} (hH : H ≤ MulAction.stabilizer G v) :
    (∃ w, Γ.Adj v w ∧ ∀ h ∈ H, h • w = w) ∨
      (∀ u w, Γ.Adj v u → Γ.Adj v w → ∃ h ∈ H, h • u = w) := by
  have hfinH : Finite ↥H := by
    have := F.loc_finite v
    exact Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective _)
  by_cases hP : IsPGroup 2 H
  · refine Or.inl (F.exists_fixed_nbr_of_two_group v H hH fun g hg => ?_)
    obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
    have hgk : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact ⟨k, by rw [hgk]; exact (nbrStab Γ G v).one_mem⟩
  right
  obtain ⟨q, hq, hqd, hq2⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card ↥H ∧ q ≠ 2 := by
    by_contra hcon
    push Not at hcon
    exact hP (IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdd => hcon d hd hdd)))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨h₀, hh₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) q hqd
  have hxo : orderOf (h₀ : G) = q := by rw [Subgroup.orderOf_coe]; exact hh₀
  have hxH : (h₀ : G) ∈ H := h₀.2
  obtain ⟨k, hk⟩ := F.exists_card_stabilizer v
  have hqv : q ∣ Fan86.valence Γ v := by
    have h1 : q ∣ Fan86.valence Γ v * 2 ^ k := hk ▸ (hqd.trans (Subgroup.card_dvd_of_le hH))
    rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)) hq2
  have hqeq : q = Fan86.valence Γ v := (Nat.prime_dvd_prime_iff_eq hq (F.valence_isPrime v)).1 hqv
  have hnofix : ∀ u, Γ.Adj v u → (h₀ : G) • u ≠ u := by
    intro u hu hfix
    have hmem : (h₀ : G) ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G u :=
      ⟨hH hxH, MulAction.mem_stabilizer_iff.2 hfix⟩
    obtain ⟨j, hj⟩ := F.edge_two v u hu ⟨(h₀ : G), hmem⟩
    have hj' : (h₀ : G) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have := orderOf_dvd_of_pow_eq_one hj'
    rw [hxo] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow this))
  set Z : Subgroup G := Subgroup.zpowers (h₀ : G) with hZ
  have hZH : Z ≤ H := Subgroup.zpowers_le.2 hxH
  have hZv : Z ≤ MulAction.stabilizer G v := hZH.trans hH
  have hZc : Nat.card ↥Z = q := by rw [hZ, Nat.card_zpowers, hxo]
  intro u w hu hw
  have horb : MulAction.orbit ↥Z u = Γ.neighborSet v := by
    have hsub := F.orbit_subset_neighborSet hu hZv
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (F.ncard_neighborSet_le v).2
    rw [← relIndex_stabilizer_eq_ncard_orbit]
    have hcard := Subgroup.relIndex_mul_card (MulAction.stabilizer G u) Z
    have hd : Nat.card ↥(MulAction.stabilizer G u ⊓ Z) ∣ q :=
      hZc ▸ Subgroup.card_dvd_of_le inf_le_right
    have h1 : Nat.card ↥(MulAction.stabilizer G u ⊓ Z) = 1 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hd) with h | h
      · exact h
      · exfalso
        have hle : MulAction.stabilizer G u ⊓ Z = Z := by
          have := Finite.of_injective (Subgroup.inclusion hZH) (Subgroup.inclusion_injective _)
          exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZc])
        have : (h₀ : G) ∈ MulAction.stabilizer G u := by
          have hx : (h₀ : G) ∈ Z := Subgroup.mem_zpowers _
          rw [← hle] at hx
          exact hx.1
        exact hnofix u hu (MulAction.mem_stabilizer_iff.1 this)
    rw [h1, mul_one, hZc] at hcard
    rw [hcard, hqeq, Fan86.valence, Nat.card_coe_set_eq]
  have hw' : w ∈ MulAction.orbit ↥Z u := by rw [horb]; exact hw
  obtain ⟨z, hz⟩ := hw'
  exact ⟨(z : G), hZH z.2, hz⟩

end FanTree

end CFSG.Quasithin.Fan86
