module

public import CFSG.Quasithin.Background.C116Two.NatMod

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

theorem card_evenWeight_three : Nat.card (evenWeight 3) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl) :
      ↥(evenWeight 3) ≃ {f : Fin 3 → ZMod 2 // ∑ i, f i = 0}), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide +kernel

theorem alt3_card_mult : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 3) ≃ evenWeight 3)]
  exact card_evenWeight_three

theorem alt3_finite : Finite (Multiplicative (evenWeight 3)) :=
  Nat.finite_of_card_ne_zero (by rw [alt3_card_mult]; norm_num)

@[expose] def alt3NzEquiv (b : MulAut (Multiplicative (evenWeight 3))) :
    Equiv.Perm {x : Multiplicative (evenWeight 3) // x ≠ 1} where
  toFun x := ⟨b x.1, fun h => x.2 ((MulEquiv.map_eq_one_iff b).mp h)⟩
  invFun x := ⟨b.symm x.1, fun h => x.2 ((MulEquiv.map_eq_one_iff b.symm).mp h)⟩
  left_inv x := Subtype.ext (MulEquiv.symm_apply_apply b x.1)
  right_inv x := Subtype.ext (MulEquiv.apply_symm_apply b x.1)

@[expose] def alt3NzHom : MulAut (Multiplicative (evenWeight 3)) →*
    Equiv.Perm {x : Multiplicative (evenWeight 3) // x ≠ 1} where
  toFun b := alt3NzEquiv b
  map_one' := Equiv.ext fun x => Subtype.ext rfl
  map_mul' b c := Equiv.ext fun x => Subtype.ext rfl

theorem alt3NzHom_eq_one {b : MulAut (Multiplicative (evenWeight 3))} (h : alt3NzHom b = 1) :
    b = 1 := by
  refine MulEquiv.ext fun y => ?_
  by_cases hy : y = 1
  · subst hy
    exact map_one b
  · have h' := congrArg (fun p : Equiv.Perm {x : Multiplicative (evenWeight 3) // x ≠ 1} =>
      (p ⟨y, hy⟩ : {x : Multiplicative (evenWeight 3) // x ≠ 1}).1) h
    exact h'

theorem alt3_card_nonzero : Nat.card {x : Multiplicative (evenWeight 3) // x ≠ 1} = 3 := by
  haveI := alt3_finite
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : Multiplicative (evenWeight 3)))
  rw [Finite.card_option, alt3_card_mult] at h
  omega

theorem alt3_card_perm :
    Nat.card (Equiv.Perm {x : Multiplicative (evenWeight 3) // x ≠ 1}) = 6 := by
  haveI := alt3_finite
  rw [Nat.card_perm, alt3_card_nonzero]
  rfl

theorem card_le_two_of_elemAbelian (B : Subgroup (MulAut (Multiplicative (evenWeight 3))))
    (hB : IsElemAbelian 2 B) : Nat.card B ≤ 2 := by
  haveI := alt3_finite
  have hinj : Function.Injective (alt3NzHom.comp B.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : alt3NzHom (g : MulAut (Multiplicative (evenWeight 3))) = 1 := hg
    exact Subtype.ext (alt3NzHom_eq_one hg')
  haveI : Finite B := Finite.of_injective _ hinj
  have hdvd : Nat.card B ∣ 6 := by
    rw [← alt3_card_perm]
    exact Subgroup.card_dvd_of_injective _ hinj
  have h3 : ¬ 3 ∣ Nat.card B := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
    have hsq : g ^ 2 = 1 := Subtype.ext (hB.2 (g : MulAut (Multiplicative (evenWeight 3))) g.2)
    have h2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hg] at h2
    norm_num at h2
  generalize Nat.card B = n at hdvd h3 ⊢
  have hn : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> first | omega | norm_num at hdvd h3

theorem card_fixed_le_two {b : MulAut (Multiplicative (evenWeight 3))} (hb : b ≠ 1) :
    Nat.card {x : Multiplicative (evenWeight 3) // b x = x} ≤ 2 := by
  have hV : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 3) ≃ evenWeight 3)]
    exact card_evenWeight_three
  haveI : Finite (Multiplicative (evenWeight 3)) :=
    Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  let H : Subgroup (Multiplicative (evenWeight 3)) :=
    { carrier := {x | b x = x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx, hy]
      one_mem' := map_one b
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, hx]
        rfl }
  have hcard : Nat.card {x : Multiplicative (evenWeight 3) // b x = x} = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hne : H ≠ ⊤ := by
    intro htop
    apply hb
    refine MulEquiv.ext fun y => ?_
    have hy : y ∈ H := by rw [htop]; exact Subgroup.mem_top y
    show b y = y
    exact hy
  have hne' : Nat.card H ≠ 4 := by
    intro h4
    exact hne (Subgroup.eq_top_of_card_eq H (h4.trans hV.symm))
  have hdvd : Nat.card H ∣ 4 := by
    have h := Subgroup.card_subgroup_dvd_card H
    rwa [hV] at h
  have hle : Nat.card H ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  rw [hcard]
  generalize Nat.card H = n at hdvd hle hne' ⊢
  interval_cases n <;> first | omega | norm_num at hdvd

theorem card_multiplicative_evenWeight_three : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 3) ≃ evenWeight 3)]
  exact card_evenWeight_three

theorem natCountMod_alt3 : NatCountMod (Multiplicative (evenWeight 3)) (altAct 3).range := by
  intro B hB _
  haveI : Finite (Multiplicative (evenWeight 3)) :=
    Nat.finite_of_card_ne_zero (by rw [card_multiplicative_evenWeight_three]; norm_num)
  by_cases hbot : B = ⊥
  · subst hbot
    rw [Subgroup.card_bot, card_multiplicative_evenWeight_three, one_mul]
    have := Nat.card_le_card_of_injective
      (fun x : {x : Multiplicative (evenWeight 3) //
        ∀ b ∈ (⊥ : Subgroup (MulAut (Multiplicative (evenWeight 3)))), b x = x} => x.1)
      Subtype.val_injective
    rw [card_multiplicative_evenWeight_three] at this
    exact this
  · obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have h2 : Nat.card B ≤ 2 := card_le_two_of_elemAbelian B hB
    have hfix : Nat.card {x : Multiplicative (evenWeight 3) // ∀ b ∈ B, b x = x} ≤ 2 := by
      refine le_trans ?_ (card_fixed_le_two (b := b) ?_)
      · refine Nat.card_le_card_of_injective
          (fun x => ⟨x.1, x.2 b hbB⟩) ?_
        intro x y h
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        exact hb1 (Subtype.ext h)
    rw [card_multiplicative_evenWeight_three]
    calc Nat.card B * Nat.card {x : Multiplicative (evenWeight 3) // ∀ b ∈ B, b x = x}
        ≤ 2 * 2 := Nat.mul_le_mul h2 hfix
      _ = 4 := rfl

end CFSG.Quasithin.C116Two
