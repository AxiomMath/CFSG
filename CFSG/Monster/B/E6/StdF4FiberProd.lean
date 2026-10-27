module

public import CFSG.Monster.B.E6.StdF4FiberCent

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical

instance finite_GStar :
    Finite GStar := Finite.of_equiv _ SemidirectProduct.equivProd.symm

abbrev fibCent
    (d : Fin 5) : Subgroup GStar :=
  parStar firstJ ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)}

abbrev fibOrbit
    (d : Fin 5) : Set GStar :=
  conjOrbit (parStar firstJ) (SemidirectProduct.inl (fibT d))

theorem ncard_fibOrbit
    (d : Fin 5) : (fibOrbit d).ncard = repSize d :=
  ncard_conjOrbit_parStar_tW (level_fibWord d)

theorem repSize_mul_card_fibCent
    (d : Fin 5) :
    repSize d * Nat.card (fibCent d) = 3 * 2 ^ 36 * 93555 * 2 := by
  rw [← ncard_fibOrbit, ← card_eq_ncard_conjOrbit_mul, card_parStar]

theorem fib_arith : ∀ d : Fin 5,
    repSize d * (2 ^ fibExp d * (fibLeviCard d * 2)) = 3 * 2 ^ 36 * 93555 * 2 := by
  decide

theorem card_fibCent
    (d : Fin 5) : Nat.card (fibCent d) = 2 ^ fibExp d * (fibLeviCard d * 2) := by
  have h1 := repSize_mul_card_fibCent d
  rw [← fib_arith d] at h1
  have hpos : 0 < repSize d := by fin_cases d <;> decide
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem fibV_inf_fibLevi
    (d : Fin 5) : fibV d ⊓ fibLevi d = ⊥ :=
  eq_bot_iff.2 fun _ hg => (stdRadical_inf_stdLevi firstJ).le
    ⟨fibV_le_stdRadical d hg.1, leviParabolic_le_stdLevi two_mem_firstJ (fibIF_subset d) hg.2⟩

theorem eq_one_of_mem_fibVStar_of_mem_fibLStar
    {d : Fin 5} {γ : GStar} (h1 : γ ∈ fibVStar d)
    (h2 : γ ∈ fibLStar d) : γ = 1 := by
  obtain ⟨hv, hr⟩ := mem_fibVStar.1 h1
  have hl : (γ.left : ModGL Tag.E6 K) ∈ fibV d ⊓ fibLevi d := ⟨hv, h2⟩
  rw [fibV_inf_fibLevi, Subgroup.mem_bot] at hl
  exact SemidirectProduct.ext (Subtype.ext hl) hr

theorem fibVStar_inf_fibLStar
    (d : Fin 5) : fibVStar d ⊓ fibLStar d = ⊥ :=
  eq_bot_iff.2 fun _ hγ => eq_one_of_mem_fibVStar_of_mem_fibLStar hγ.1 hγ.2

@[expose] def fibProd
    (d : Fin 5) (p : fibVStar d × fibLStar d) : fibCent d :=
  ⟨p.1 * p.2, mul_mem (fibVStar_le d p.1.2) (fibLStar_le d p.2.2)⟩

theorem fibProd_injective
    (d : Fin 5) : Function.Injective (fibProd d) := by
  rintro ⟨v, l⟩ ⟨v', l'⟩ h
  have e : (v : GStar) * l = v' * l' := congrArg Subtype.val h
  have hm : (v' : GStar)⁻¹ * v = l' * (l : GStar)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
  have h1 : (v' : GStar)⁻¹ * v = 1 :=
    eq_one_of_mem_fibVStar_of_mem_fibLStar (mul_mem (inv_mem v'.2) v.2)
      (hm ▸ mul_mem l'.2 (inv_mem l.2))
  rw [inv_mul_eq_one] at h1
  have h2 : (l : GStar) = l' := by
    rw [h1] at e
    exact mul_left_cancel e
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2)

theorem fibProd_bijective
    (d : Fin 5) : Function.Bijective (fibProd d) := by
  refine (fibProd_injective d).bijective_of_nat_card_le ?_
  rw [Nat.card_prod, card_fibVStar, card_fibLStar, card_fibCent]

theorem existsUnique_mul_of_mem_fibCent
    {d : Fin 5} {γ : GStar} (hγ : γ ∈ fibCent d) :
    ∃! p : fibVStar d × fibLStar d, (p.1 : GStar) * p.2 = γ := by
  obtain ⟨p, hp⟩ := (fibProd_bijective d).2 ⟨γ, hγ⟩
  refine ⟨p, congrArg Subtype.val hp, fun p' hp' => (fibProd_bijective d).1 ?_⟩
  rw [hp]
  exact Subtype.ext hp'

theorem exists_mul_of_mem_fibCent
    {d : Fin 5} {γ : GStar} (hγ : γ ∈ fibCent d) :
    ∃ v ∈ fibVStar d, ∃ l ∈ fibLStar d, γ = v * l := by
  obtain ⟨⟨v, l⟩, hp, -⟩ := existsUnique_mul_of_mem_fibCent hγ
  exact ⟨v, v.2, l, l.2, hp.symm⟩

theorem fibCent_eq_sup
    (d : Fin 5) : fibCent d = fibVStar d ⊔ fibLStar d := by
  refine le_antisymm (fun γ hγ => ?_) (sup_le (fibVStar_le d) (fibLStar_le d))
  obtain ⟨v, hv, l, hl, rfl⟩ := exists_mul_of_mem_fibCent hγ
  exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hl)

theorem conj_mem_stdRadical
    {g q : ModGL Tag.E6 K} (hg : g ∈ nativeParabolic firstJ)
    (hq : q ∈ stdRadical firstJ) : g * q * g⁻¹ ∈ stdRadical firstJ :=
  (stdRadical_normal firstJ).conj_mem ⟨q, stdRadical_le_nativeParabolic' firstJ hq⟩ hq ⟨g, hg⟩

theorem radStar_le_parStar :
    radStar ≤ parStar firstJ := fun _ hγ =>
  stdRadical_le_nativeParabolic' firstJ (mem_radStar.1 hγ).1

theorem conj_mem_radStar
    {γ u : GStar} (hγ : γ ∈ parStar firstJ) (hu : u ∈ radStar) :
    γ * u * γ⁻¹ ∈ radStar := by
  obtain ⟨hu1, hu2⟩ := mem_radStar.1 hu
  have hu' : u = SemidirectProduct.inl u.left := SemidirectProduct.ext rfl hu2
  rw [hu', conj_inl]
  refine mem_radStar.2 ⟨?_, rfl⟩
  have hb := apply_mem_of_betaGL_mem (fun _ hg => betaGL_mem_stdRadical hg) γ.right hu1
  rw [SemidirectProduct.left_inl, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact conj_mem_stdRadical hγ hb

theorem fibVStar_le_radStar
    (d : Fin 5) : fibVStar d ≤ radStar := fun _ hγ =>
  mem_radStar.2 ⟨fibV_le_stdRadical d (mem_fibVStar.1 hγ).1, (mem_fibVStar.1 hγ).2⟩

theorem eq_one_of_mem_radStar_of_mem_fibLStar
    {d : Fin 5} {γ : GStar} (h1 : γ ∈ radStar)
    (h2 : γ ∈ fibLStar d) : γ = 1 := by
  obtain ⟨hq, hr⟩ := mem_radStar.1 h1
  have hl : (γ.left : ModGL Tag.E6 K) ∈ stdRadical firstJ ⊓ stdLevi firstJ :=
    ⟨hq, leviParabolic_le_stdLevi two_mem_firstJ (fibIF_subset d) h2⟩
  rw [stdRadical_inf_stdLevi, Subgroup.mem_bot] at hl
  exact SemidirectProduct.ext (Subtype.ext hl) hr

theorem radStar_inf_fibCent
    (d : Fin 5) : radStar ⊓ fibCent d = fibVStar d := by
  refine le_antisymm (fun γ hγ => ?_) (le_inf (fibVStar_le_radStar d) (fibVStar_le d))
  obtain ⟨v, hv, l, hl, rfl⟩ := exists_mul_of_mem_fibCent hγ.2
  have hlU : l ∈ radStar := by
    have := mul_mem (inv_mem (fibVStar_le_radStar d hv)) hγ.1
    rwa [inv_mul_cancel_left] at this
  rw [eq_one_of_mem_radStar_of_mem_fibLStar hlU hl, mul_one]
  exact hv

theorem radStar_inf_centralizer
    (d : Fin 5) :
    radStar ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} = fibVStar d := by
  rw [← radStar_inf_fibCent]
  ext γ
  exact ⟨fun h => ⟨h.1, radStar_le_parStar h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem fibCent_le_normalizer
    (d : Fin 5) :
    fibCent d ≤ Subgroup.normalizer (fibVStar d : Set GStar) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro v
  rw [← radStar_inf_fibCent]
  constructor
  · intro hv
    exact Subgroup.mem_inf.2 ⟨conj_mem_radStar hc.1 hv.1, mul_mem (mul_mem hc hv.2) (inv_mem hc)⟩
  · intro hv
    have h1 := conj_mem_radStar (inv_mem hc.1) hv.1
    have h2 := mul_mem (mul_mem (inv_mem hc) hv.2) (inv_inv c ▸ hc)
    rw [inv_inv] at h1 h2
    have e : c⁻¹ * (c * v * c⁻¹) * c = v := by group
    rw [e] at h1 h2
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩

@[expose] def inlLevi
    (d : Fin 5) : Subgroup GStar :=
  ((fibLevi d).subgroupOf stdGroup).map SemidirectProduct.inl

@[expose] def betaSub :
    Subgroup GStar := (SemidirectProduct.inr : betaGroup →* GStar).range

theorem mem_inlLevi
    {d : Fin 5} {γ : GStar} :
    γ ∈ inlLevi d ↔ (γ.left : ModGL Tag.E6 K) ∈ fibLevi d ∧ γ.right = 1 :=
  mem_map_inl_iff

theorem mem_betaSub
    {γ : GStar} : γ ∈ betaSub ↔ γ.left = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    rfl
  · intro h
    exact ⟨γ.right, SemidirectProduct.ext h.symm rfl⟩

theorem fibLStar_eq_sup
    (d : Fin 5) : fibLStar d = inlLevi d ⊔ betaSub := by
  refine le_antisymm (fun γ hγ => ?_) (sup_le (fun _ hγ => (mem_inlLevi.1 hγ).1) ?_)
  · have e : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
      (SemidirectProduct.inl_left_mul_inr_right γ).symm
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mem_inlLevi.2 ⟨hγ, rfl⟩))
      (Subgroup.mem_sup_right ⟨γ.right, rfl⟩)
  · intro γ hγ
    change (γ.left : ModGL Tag.E6 K) ∈ fibLevi d
    rw [mem_betaSub.1 hγ]
    exact one_mem _

theorem inlLevi_inf_betaSub
    (d : Fin 5) : inlLevi d ⊓ betaSub = ⊥ :=
  eq_bot_iff.2 fun _ hγ => SemidirectProduct.ext (mem_betaSub.1 hγ.2) (mem_inlLevi.1 hγ.1).2

theorem fibLStar_le_normalizer
    (d : Fin 5) :
    fibLStar d ≤ Subgroup.normalizer (inlLevi d : Set GStar) := by
  have key : ∀ γ ∈ fibLStar d, ∀ x ∈ inlLevi d, γ * x * γ⁻¹ ∈ inlLevi d := by
    intro γ hγ x hx
    obtain ⟨hx1, hx2⟩ := mem_inlLevi.1 hx
    have hx' : x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl hx2
    rw [hx', conj_inl]
    refine mem_inlLevi.2 ⟨?_, rfl⟩
    rw [SemidirectProduct.left_inl, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem hγ (apply_mem_of_betaGL_mem (fun _ => betaGL_mem_leviParabolic)
      γ.right hx1)) (inv_mem hγ)
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key γ hγ x, fun hx => ?_⟩
  have := key γ⁻¹ (inv_mem hγ) _ hx
  rwa [inv_inv, show γ⁻¹ * (γ * x * γ⁻¹) * γ = x by group] at this

@[expose] def fibUSize : Fin 5 → ℕ := ![1, 2, 64, 2048, 2097152]

theorem fibUSize_mul : ∀ d : Fin 5, fibUSize d * 2 ^ fibExp d = 2 ^ 21 := by decide

theorem card_inf_centralizer_conj {M : Type*} [Group M] (H : Subgroup M) {g : M}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (x : M) :
    Nat.card ↥(H ⊓ Subgroup.centralizer {g * x * g⁻¹}) =
      Nat.card ↥(H ⊓ Subgroup.centralizer {x}) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨g⁻¹ * h * g, Subgroup.mem_inf.2 ⟨hg' _ (Subgroup.mem_inf.1 h.2).1, ?_⟩⟩
      invFun := fun h => ⟨g * h * g⁻¹, Subgroup.mem_inf.2 ⟨hg _ (Subgroup.mem_inf.1 h.2).1, ?_⟩⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  · have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h.2).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * h * g * x = g⁻¹ * (h * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * h) * g := by rw [hc]
      _ = x * (g⁻¹ * h * g) := by group
  · have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h.2).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * h * g⁻¹ * (g * x * g⁻¹) = g * (h * x) * g⁻¹ := by group
      _ = g * (x * h) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * h * g⁻¹) := by group

theorem ncard_conjOrbit_radStar
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    (conjOrbit radStar x).ncard = fibUSize d := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  have h := card_eq_ncard_conjOrbit_mul radStar (γ * SemidirectProduct.inl (fibT d) * γ⁻¹)
  rw [card_inf_centralizer_conj radStar (fun u hu => conj_mem_radStar hγ hu)
      (fun u hu => by simpa using conj_mem_radStar (inv_mem hγ) hu),
    radStar_inf_centralizer, card_fibVStar, card_radStar, ← fibUSize_mul d] at h
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm

end CFSG.Monster.B.E6.StdF4
