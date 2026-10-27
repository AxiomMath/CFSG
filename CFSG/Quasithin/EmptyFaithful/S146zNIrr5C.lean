module

public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5B

public section

namespace CFSG.Quasithin.A6Irr5

variable {V : Type*} [CommGroup V]

theorem exists_invariant_finset [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 32)
    (L : Subgroup (MulAut V)) (hL : Nat.card L = 360) :
    ∃ T : Finset V, (∀ l ∈ L, ∀ t ∈ T, l t ∈ T) ∧ (∃ t ∈ T, t ≠ 1) ∧
      (T.card = 1 ∨ T.card = 6) := by
  classical
  have h5fact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hLfin : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 (by rw [hL]; norm_num)
  have hy' : orderOf (y : MulAut V) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  obtain ⟨v, hv1, hvy, hvuniq⟩ := exists_fixed_pair hV hcard hy'
  have hne : ∀ l : L, (l : MulAut V) v ≠ 1 := fun l h =>
    hv1 ((EmbeddingLike.map_eq_one_iff (f := (l : MulAut V))).mp h)
  have hOfix : Nat.card (MulAction.fixedBy (MulAction.orbit L v) y) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have key : ∀ x : MulAction.fixedBy (MulAction.orbit L v) y, (x.1 : V) = v := by
      rintro ⟨⟨x, l, rfl⟩, hx⟩
      have hx' : (y : MulAut V) ((l : MulAut V) v) = (l : MulAut V) v :=
        congrArg Subtype.val hx
      rcases hvuniq _ hx' with h | h
      · exact absurd h (hne l)
      · exact h
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ((key a).trans (key b).symm))⟩,
      ⟨⟨⟨v, MulAction.mem_orbit_self v⟩, ?_⟩⟩⟩
    exact Subtype.ext hvy
  have hmod : Nat.card (MulAction.orbit L v) ≡
      Nat.card (MulAction.fixedBy (MulAction.orbit L v) y) [MOD 5] := card_modEq_card_fixedBy hy
  rw [hOfix] at hmod
  have hdvd : Nat.card (MulAction.orbit L v) ∣ 360 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup L v)
    rw [Nat.card_prod, hL] at h
    exact ⟨_, h.symm⟩
  have hle : Nat.card (MulAction.orbit L v) ≤ 32 := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hmod5 : Nat.card (MulAction.orbit L v) % 5 = 1 := hmod
  have hnonempty : Nonempty (MulAction.orbit L v) := ⟨⟨v, MulAction.mem_orbit_self v⟩⟩
  have hpos : 0 < Nat.card (MulAction.orbit L v) := Nat.card_pos
  have hn : Nat.card (MulAction.orbit L v) = 1 ∨ Nat.card (MulAction.orbit L v) = 6 := by
    generalize Nat.card (MulAction.orbit L v) = n at hdvd hle hmod5 hpos
    interval_cases n <;> omega
  have hfin : (MulAction.orbit L v).Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ⟨v, ?_, hv1⟩, ?_⟩
  · intro l hl t ht
    rw [Set.Finite.mem_toFinset] at ht ⊢
    exact MulAction.mem_orbit_of_mem_orbit (⟨l, hl⟩ : L) ht
  · rw [Set.Finite.mem_toFinset]
    exact MulAction.mem_orbit_self v
  · have h1 : hfin.toFinset.card = Nat.card (MulAction.orbit L v) := by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
    rw [h1]
    exact hn

end CFSG.Quasithin.A6Irr5
