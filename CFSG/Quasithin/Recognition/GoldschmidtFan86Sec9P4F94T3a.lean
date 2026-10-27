module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T2a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Iso

public section

namespace CFSG.Quasithin.Fan86

theorem units5_pow_four : ∀ u : (ZMod 5)ˣ, u ^ 4 = 1 := by
  decide

theorem card_zmod4_sq : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4),
    Nat.card_zmod]

theorem card_zmod4_sq_two :
    Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) =
      32 := by
  rw [Nat.card_prod, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
    Nat.card_zmod, Nat.card_zmod]

theorem exists_iso_two_of {K : Type*} [Group K] (Φ : K →* (Fin 3 → (ZMod 5)ˣ)) (W V : K)
    (ha0 : Φ W 0 * Φ W 0 ≠ 1) (ha2 : Φ W 2 = 1) (hb0 : Φ V 0 = 1) (hb2 : Φ V 2 * Φ V 2 ≠ 1)
    (hcard : Φ.ker.index = 16) :
    ∃ φ : K →* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)),
      Function.Surjective φ ∧ φ.ker = Φ.ker := by
  have : Finite Φ.range :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_ker, hcard]; norm_num)
  let x : Φ.range := Φ.rangeRestrict W
  let y : Φ.range := Φ.rangeRestrict V
  have hx : x ^ 4 = 1 := Subtype.ext (funext fun i => by simpa [x] using units5_pow_four (Φ W i))
  have hy : y ^ 4 = 1 := Subtype.ext (funext fun i => by simpa [y] using units5_pow_four (Φ V i))
  let ι : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* Φ.range :=
    ((zmodHom x 4 hx).comp (MonoidHom.fst _ _)) * ((zmodHom y 4 hy).comp (MonoidHom.snd _ _))
  have hinj : Function.Injective ι := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' := congrArg (fun t : Φ.range => (t : Fin 3 → (ZMod 5)ˣ)) h
    simp only [ι, MonoidHom.mul_apply, MonoidHom.comp_apply, zmodHom_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Subgroup.coe_mul, Subgroup.coe_pow, x, y,
      MonoidHom.coe_rangeRestrict] at h'
    have key : ((Multiplicative.toAdd a, Multiplicative.toAdd b) : Fin 4 × Fin 4) =
        (Multiplicative.toAdd a', Multiplicative.toAdd b') := pow_inj_two ha0 ha2 hb0 hb2 h'
    exact Prod.ext (Multiplicative.toAdd.injective (congrArg Prod.fst key))
      (Multiplicative.toAdd.injective (congrArg Prod.snd key))
  have hbij : Function.Bijective ι :=
    hinj.bijective_of_nat_card_le (by rw [← Subgroup.index_ker, hcard, card_zmod4_sq])
  let e := MulEquiv.ofBijective ι hbij
  refine ⟨e.symm.toMonoidHom.comp Φ.rangeRestrict,
    e.symm.surjective.comp Φ.rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, MonoidHom.ker_rangeRestrict]

theorem exists_iso_three_of {K : Type*} [Group K] (Φ : K →* (Fin 3 → (ZMod 5)ˣ)) (W V Cc : K)
    (ha0 : Φ W 0 * Φ W 0 ≠ 1) (ha2 : Φ W 2 = 1) (hb0 : Φ V 0 = 1) (hb2 : Φ V 2 * Φ V 2 ≠ 1)
    (hc0 : Φ Cc 0 = 1) (hc2 : Φ Cc 2 = 1) (hc1 : Φ Cc 1 = -1) (hcard : Φ.ker.index = 32) :
    ∃ φ : K →* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 2)),
      Function.Surjective φ ∧ φ.ker = Φ.ker := by
  have : Finite Φ.range :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_ker, hcard]; norm_num)
  let x : Φ.range := Φ.rangeRestrict W
  let y : Φ.range := Φ.rangeRestrict V
  let z : Φ.range := Φ.rangeRestrict Cc
  have hx : x ^ 4 = 1 := Subtype.ext (funext fun i => by simpa [x] using units5_pow_four (Φ W i))
  have hy : y ^ 4 = 1 := Subtype.ext (funext fun i => by simpa [y] using units5_pow_four (Φ V i))
  have hz : z ^ 2 = 1 := Subtype.ext (funext fun i => by
    fin_cases i
    · simp [z, hc0]
    · simp [z, hc1]
    · simp [z, hc2])
  let ι : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 2) →*
      Φ.range :=
    ((zmodHom x 4 hx).comp (MonoidHom.fst _ _)) *
      ((zmodHom y 4 hy).comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))) *
      ((zmodHom z 2 hz).comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))
  have hinj : Function.Injective ι := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h' := congrArg (fun t : Φ.range => (t : Fin 3 → (ZMod 5)ˣ)) h
    simp only [ι, MonoidHom.mul_apply, MonoidHom.comp_apply, zmodHom_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Subgroup.coe_mul, Subgroup.coe_pow, x, y, z,
      MonoidHom.coe_rangeRestrict] at h'
    have key : ((Multiplicative.toAdd a, Multiplicative.toAdd b, Multiplicative.toAdd c) :
        Fin 4 × Fin 4 × Fin 2) =
        (Multiplicative.toAdd a', Multiplicative.toAdd b', Multiplicative.toAdd c') :=
      pow_inj_three ha0 ha2 hb0 hb2 hc0 hc2 hc1 h'
    exact Prod.ext (Multiplicative.toAdd.injective (congrArg Prod.fst key))
      (Prod.ext (Multiplicative.toAdd.injective (congrArg (fun p => p.2.1) key))
        (Multiplicative.toAdd.injective (congrArg (fun p => p.2.2) key)))
  have hbij : Function.Bijective ι :=
    hinj.bijective_of_nat_card_le (by rw [← Subgroup.index_ker, hcard, card_zmod4_sq_two])
  let e := MulEquiv.ofBijective ι hbij
  refine ⟨e.symm.toMonoidHom.comp Φ.rangeRestrict,
    e.symm.surjective.comp Φ.rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, MonoidHom.ker_rangeRestrict]

end CFSG.Quasithin.Fan86
