module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7End
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoprimeCentralizer

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.OrdinaryProofs

namespace Case34A7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_fixed_modEq [Finite V] {g : GLV V} {p : ℕ} [Fact p.Prime] (hg : orderOf g = p) :
    Nat.card V ≡ Nat.card {v : V // g v = v} [MOD p] := by
  have hfin : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite (V := V)
  have hG : IsPGroup p (Subgroup.zpowers g) := by
    have hc : Nat.card (Subgroup.zpowers g) = p ^ 1 := by
      rw [Nat.card_zpowers, hg, pow_one]
    exact IsPGroup.of_card hc
  have h := hG.card_modEq_card_fixedPoints V
  have hfp : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) =
      Nat.card {v : V // g v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro hv x
      have hmem : g ∈ MulAction.stabilizer (GLV V) v := by
        rw [MulAction.mem_stabilizer_iff]
        exact hv
      have := (Subgroup.zpowers_le.2 hmem) x.2
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
  rwa [hfp] at h

@[expose] def fixedAddSubgroup (g : GLV V) : AddSubgroup V where
  carrier := {v | g v = v}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  zero_mem' := map_zero g
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, ha]

theorem card_fixed_eq_two [Finite V] {g : GLV V} (hg : orderOf g = 7) (hV : Nat.card V = 16) :
    Nat.card {v : V // g v = v} = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_fixed_modEq hg
  rw [hV] at hmod
  have hK : Nat.card {v : V // g v = v} = Nat.card (fixedAddSubgroup g) := rfl
  have hdvd : Nat.card (fixedAddSubgroup g) ∣ 16 := by
    rw [← hV]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  rw [hK] at hmod ⊢
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 4) (i := Nat.card (fixedAddSubgroup g))).1
    (by simpa using hdvd)
  rw [hkc] at hmod ⊢
  interval_cases k
  · simp [Nat.ModEq] at hmod
  · rfl
  · simp [Nat.ModEq] at hmod
  · simp [Nat.ModEq] at hmod
  · exfalso
    have htop : fixedAddSubgroup g = ⊤ := by
      refine AddSubgroup.eq_top_of_card_eq _ ?_
      rw [hV]; exact hkc
    have h1 : g = 1 := by
      apply LinearEquiv.ext
      intro v
      have : v ∈ fixedAddSubgroup g := by rw [htop]; trivial
      exact this
    rw [h1, orderOf_one] at hg
    omega

theorem exists_fixed_probe [Finite V] {g : GLV V} (hg : orderOf g = 7) (hV : Nat.card V = 16) :
    ∃ u : V, u ≠ 0 ∧ g u = u ∧ ∀ w : V, g w = w → w = 0 ∨ w = u := by
  have h2 := card_fixed_eq_two hg hV
  have h0 : (⟨0, map_zero g⟩ : {v : V // g v = v}) = ⟨0, map_zero g⟩ := rfl
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (⟨0, map_zero g⟩ : {v : V // g v = v})).1 h2
  refine ⟨y.1, fun h => hy (Subtype.ext h), y.2, fun w hw => ?_⟩
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  · right
    have := hy' ⟨w, hw⟩ (fun h => hw0 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem endIsField_one_of_order_seven [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    {g : GLV V} (hgL : g ∈ L) (hg : orderOf g = 7) (hV : Nat.card V = 16) : EndIsField L 1 := by
  obtain ⟨u, hu, hgu, hS⟩ := exists_fixed_probe hg hV
  refine endIsField_one_of_fixed hL (H₀ := {g}) (by simpa using hgL) hu
    (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hgu) (fun w hw => hS w (hw g rfl))

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
