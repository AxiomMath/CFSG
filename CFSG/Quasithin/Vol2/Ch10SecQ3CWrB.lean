module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrA
public import CFSG.Quasithin.Vol2.Ch10SecB3Aut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

section Coord

variable (φ : MulAut (AFive × AFive))

@[expose] noncomputable def coordU : AFive →* AFive :=
  (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (MonoidHom.inl _ _))

@[expose] noncomputable def coordV : AFive →* AFive :=
  (MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (MonoidHom.inl _ _))

@[expose] noncomputable def coordU' : AFive →* AFive :=
  (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (MonoidHom.inr _ _))

@[expose] noncomputable def coordV' : AFive →* AFive :=
  (MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (MonoidHom.inr _ _))

theorem apply_prod (a b : AFive) :
    φ (a, b) = (coordU φ a * coordU' φ b, coordV φ a * coordV' φ b) := by
  have h : (a, b) = MonoidHom.inl AFive AFive a * MonoidHom.inr AFive AFive b := by
    simp
  rw [h, map_mul]
  rfl

theorem commute_U (a b : AFive) : coordU φ a * coordU' φ b = coordU' φ b * coordU φ a := by
  have h : MonoidHom.inl AFive AFive a * MonoidHom.inr AFive AFive b =
      MonoidHom.inr AFive AFive b * MonoidHom.inl AFive AFive a := by
    simp
  have := congrArg (fun x => (φ x).1) h
  simp only [map_mul, Prod.fst_mul] at this
  exact this

theorem commute_V (a b : AFive) : coordV φ a * coordV' φ b = coordV' φ b * coordV φ a := by
  have h : MonoidHom.inl AFive AFive a * MonoidHom.inr AFive AFive b =
      MonoidHom.inr AFive AFive b * MonoidHom.inl AFive AFive a := by
    simp
  have := congrArg (fun x => (φ x).2) h
  simp only [map_mul, Prod.snd_mul] at this
  exact this

theorem exists_coordU_mul (x : AFive) : ∃ a b : AFive, coordU φ a * coordU' φ b = x := by
  obtain ⟨⟨a, b⟩, h⟩ := φ.surjective (x, 1)
  exact ⟨a, b, by simpa [apply_prod] using congrArg Prod.fst h⟩

theorem exists_coordV_mul (x : AFive) : ∃ a b : AFive, coordV φ a * coordV' φ b = x := by
  obtain ⟨⟨a, b⟩, h⟩ := φ.surjective (1, x)
  exact ⟨a, b, by simpa [apply_prod] using congrArg Prod.snd h⟩

theorem coordU'_eq_one (h : Function.Injective (coordU φ)) : coordU' φ = 1 := by
  refine MonoidHom.ext fun b => ?_
  rw [MonoidHom.one_apply]
  apply eq_one_of_forall_commute_aFive
  intro x
  obtain ⟨a, rfl⟩ := Finite.surjective_of_injective h x
  exact (commute_U φ a b).symm

theorem coordV'_eq_one (h : Function.Injective (coordV φ)) : coordV' φ = 1 := by
  refine MonoidHom.ext fun b => ?_
  rw [MonoidHom.one_apply]
  apply eq_one_of_forall_commute_aFive
  intro x
  obtain ⟨a, rfl⟩ := Finite.surjective_of_injective h x
  exact (commute_V φ a b).symm

theorem coordU_eq_one (h : Function.Injective (coordU' φ)) : coordU φ = 1 := by
  refine MonoidHom.ext fun a => ?_
  rw [MonoidHom.one_apply]
  apply eq_one_of_forall_commute_aFive
  intro x
  obtain ⟨b, rfl⟩ := Finite.surjective_of_injective h x
  exact commute_U φ a b

theorem coordV_eq_one (h : Function.Injective (coordV' φ)) : coordV φ = 1 := by
  refine MonoidHom.ext fun a => ?_
  rw [MonoidHom.one_apply]
  apply eq_one_of_forall_commute_aFive
  intro x
  obtain ⟨b, rfl⟩ := Finite.surjective_of_injective h x
  exact commute_V φ a b

theorem injective_U' (h : coordU φ = 1) : Function.Injective (coordU' φ) := by
  refine Finite.injective_iff_surjective.mpr fun x => ?_
  obtain ⟨a, b, hab⟩ := exists_coordU_mul φ x
  exact ⟨b, by rwa [h, MonoidHom.one_apply, one_mul] at hab⟩

theorem not_U_V (hu : coordU φ = 1) (hv : coordV φ = 1) : False := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : AFive)
  have h1 : φ (a₀, 1) = φ 1 := by
    rw [apply_prod, hu, hv, map_one]
    simp
  exact ha₀ (congrArg Prod.fst (φ.injective h1))

theorem not_U'_V' (hu : coordU' φ = 1) (hv : coordV' φ = 1) : False := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : AFive)
  have h1 : φ (1, a₀) = φ 1 := by
    rw [apply_prod, hu, hv, map_one]
    simp
  exact ha₀ (congrArg Prod.snd (φ.injective h1))

end Coord

abbrev InjEnd : Type := {f : AFive →* AFive // Function.Injective f}

noncomputable def injEndEquiv : InjEnd ≃ MulAut AFive where
  toFun f := MulEquiv.ofBijective f.1 ⟨f.2, Finite.surjective_of_injective f.2⟩
  invFun φ := ⟨φ.toMonoidHom, φ.injective⟩
  left_inv _ := Subtype.ext (MonoidHom.ext fun _ => rfl)
  right_inv _ := MulEquiv.ext fun _ => rfl

theorem card_injEnd : Nat.card InjEnd = 120 := by
  rw [Nat.card_congr injEndEquiv, card_mulAut_of_equiv_A5 (MulEquiv.refl _)]

noncomputable def codeAut (φ : MulAut (AFive × AFive)) : Bool × InjEnd × InjEnd :=
  if h : coordU φ = 1 then
    (false, ⟨coordV φ, (eq_one_or_injective_aFive _).resolve_left (not_U_V φ h)⟩,
      ⟨coordU' φ, injective_U' φ h⟩)
  else
    (true, ⟨coordU φ, (eq_one_or_injective_aFive _).resolve_left h⟩,
      ⟨coordV' φ, (eq_one_or_injective_aFive _).resolve_left fun hv =>
        not_U'_V' φ (coordU'_eq_one φ ((eq_one_or_injective_aFive _).resolve_left h)) hv⟩)

theorem codeAut_injective : Function.Injective codeAut := by
  intro φ ψ h
  by_cases hφ : coordU φ = 1 <;> by_cases hψ : coordU ψ = 1 <;>
    simp only [codeAut, hφ, hψ, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, true_and] at h
  · have h1 := coordV'_eq_one φ ((eq_one_or_injective_aFive _).resolve_left (not_U_V φ hφ))
    have h2 := coordV'_eq_one ψ ((eq_one_or_injective_aFive _).resolve_left (not_U_V ψ hψ))
    refine MulEquiv.ext fun p => ?_
    rw [← Prod.mk.eta (p := p), apply_prod, apply_prod, hφ, hψ, h1, h2, h.1, h.2]
  · have h1 := coordU'_eq_one φ ((eq_one_or_injective_aFive _).resolve_left hφ)
    have h2 := coordU'_eq_one ψ ((eq_one_or_injective_aFive _).resolve_left hψ)
    have h3 := coordV_eq_one φ ((eq_one_or_injective_aFive _).resolve_left
      fun hv => not_U'_V' φ h1 hv)
    have h4 := coordV_eq_one ψ ((eq_one_or_injective_aFive _).resolve_left
      fun hv => not_U'_V' ψ h2 hv)
    refine MulEquiv.ext fun p => ?_
    rw [← Prod.mk.eta (p := p), apply_prod, apply_prod, h1, h2, h3, h4, h.1, h.2]

theorem card_mulAut_prod_le : Nat.card (MulAut (AFive × AFive)) ≤ 28800 := by
  have : Finite InjEnd := Nat.finite_of_card_ne_zero (by rw [card_injEnd]; norm_num)
  calc Nat.card (MulAut (AFive × AFive)) ≤ Nat.card (Bool × InjEnd × InjEnd) :=
        Nat.card_le_card_of_injective _ codeAut_injective
    _ = 28800 := by
        rw [Nat.card_prod, Nat.card_prod, card_injEnd, Nat.card_eq_fintype_card (α := Bool),
          Fintype.card_bool]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
