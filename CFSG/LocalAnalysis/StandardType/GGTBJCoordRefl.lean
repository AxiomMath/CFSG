module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

open Multiplicative

variable {p m : ℕ} {α : Type*}

theorem ggTBJSpC_card_coord (p m : ℕ) :
    Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]

theorem ggTBJSpC_card_subtype_notMem (I : Finset (Fin m)) :
    Nat.card {i : Fin m // i ∉ I} = m - I.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : Finset.filter (fun i : Fin m => i ∉ I) Finset.univ = Iᶜ := by
    ext i
    rw [Finset.mem_filter, Finset.mem_compl]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  rw [h, Finset.card_compl, Fintype.card_fin]

@[expose] noncomputable def ggTBJSpC_invSwapAut (p m : ℕ) (u w : Fin m) :
    MulAut (Fin m → Multiplicative (ZMod p)) :=
  SpCoord.sgnAut u * SpCoord.sgnAut w * SpCoord.permAut (Equiv.swap u w)

theorem ggTBJSpC_invSwapAut_eq_sgnAut_conj (u w : Fin m) :
    ggTBJSpC_invSwapAut p m u w =
      SpCoord.sgnAut u * SpCoord.permAut (Equiv.swap u w) * (SpCoord.sgnAut u)⁻¹ := by
  have hinv : (SpCoord.sgnAut u : MulAut (Fin m → Multiplicative (ZMod p)))⁻¹ =
      SpCoord.sgnAut u := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using SpCoord.sgnAut_sq (p := p) u
  have hcov := SpCoord.IsSignedPerm.mul_sgnAut (p := p)
    (u := SpCoord.permAut (Equiv.swap u w)) (π := Equiv.swap u w) (ε := fun _ => 1)
    (fun f i => by simp [SpCoord.permAut_apply]) u
  rw [Equiv.swap_apply_left] at hcov
  change SpCoord.sgnAut u * SpCoord.sgnAut w * SpCoord.permAut (Equiv.swap u w) = _
  rw [hinv, mul_assoc, mul_assoc, hcov]

theorem ggTBJSpC_invSwapAut_apply {u w : Fin m} (huw : u ≠ w)
    (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    ggTBJSpC_invSwapAut p m u w f i =
      if i = u then (f w)⁻¹ else if i = w then (f u)⁻¹ else f i := by
  rw [ggTBJSpC_invSwapAut, MulAut.mul_apply, MulAut.mul_apply, SpCoord.sgnAut_apply,
    SpCoord.sgnAut_apply, SpCoord.permAut_apply]
  simp only [Function.update_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hiu : i = u
  · simp only [ite_eq_left hiu, ite_eq_right huw, Equiv.swap_apply_left]
  · by_cases hiw : i = w
    · simp only [ite_eq_right hiu, ite_eq_left hiw, Equiv.swap_apply_right]
    · simp only [ite_eq_right hiu, ite_eq_right hiw, Equiv.swap_apply_of_ne_of_ne hiu hiw]

theorem ggTBJSpC_invSwapAut_eq_self_iff {u w : Fin m} (huw : u ≠ w)
    (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_invSwapAut p m u w f = f ↔ f u = (f w)⁻¹ := by
  constructor
  · intro h
    have h1 := congrFun h u
    rw [ggTBJSpC_invSwapAut_apply huw, ite_eq_left rfl] at h1
    exact h1.symm
  · intro h
    funext i
    rw [ggTBJSpC_invSwapAut_apply huw]
    by_cases hiu : i = u
    · subst hiu
      rw [ite_eq_left rfl, h]
    · by_cases hiw : i = w
      · subst hiw
        rw [ite_eq_right hiu, ite_eq_left rfl, h, inv_inv]
      · rw [ite_eq_right hiu, ite_eq_right hiw]

theorem ggTBJSpC_invSwapAut_sq {u w : Fin m} (huw : u ≠ w) :
    (ggTBJSpC_invSwapAut p m u w) ^ 2 = 1 := by
  refine MulEquiv.ext fun f => funext fun i => ?_
  change ggTBJSpC_invSwapAut p m u w (ggTBJSpC_invSwapAut p m u w f) i = f i
  rw [ggTBJSpC_invSwapAut_apply huw]
  by_cases hiu : i = u
  · rw [ite_eq_left hiu, ggTBJSpC_invSwapAut_apply huw, ite_eq_right (Ne.symm huw),
      ite_eq_left rfl, inv_inv, hiu]
  · rw [ite_eq_right hiu]
    by_cases hiw : i = w
    · rw [ite_eq_left hiw, ggTBJSpC_invSwapAut_apply huw, ite_eq_left rfl, inv_inv, hiw]
    · rw [ite_eq_right hiw, ggTBJSpC_invSwapAut_apply huw, ite_eq_right hiu, ite_eq_right hiw]

theorem ggTBJSpC_permAut_swap_eq_self_iff {u w : Fin m} (huw : u ≠ w)
    (f : Fin m → Multiplicative (ZMod p)) :
    SpCoord.permAut (Equiv.swap u w) f = f ↔ f u = f w := by
  constructor
  · intro h
    have h1 := congrFun h u
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext i
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
    by_cases hiu : i = u
    · rw [hiu, Equiv.swap_apply_left]
      exact h.symm
    · by_cases hiw : i = w
      · rw [hiw, Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hiu hiw]

theorem ggTBJSpC_card_fix_invSwapAut (hp : p.Prime) (hp2 : p ≠ 2) {u w : Fin m} (huw : u ≠ w) :
    Nat.card {f : Fin m → Multiplicative (ZMod p) // ggTBJSpC_invSwapAut p m u w f = f} * p =
      p ^ m := by
  have hcard := SpCoord.card_fix_permAut_swap (p := p) (k := m) hp hp2 huw
  rw [ggTBJSpC_card_coord] at hcard
  rw [← hcard]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (SpCoord.sgnAut w).toEquiv ?_)
  intro f
  rw [ggTBJSpC_invSwapAut_eq_self_iff huw, ggTBJSpC_permAut_swap_eq_self_iff huw]
  change f u = (f w)⁻¹ ↔ SpCoord.sgnAut w f u = SpCoord.sgnAut w f w
  rw [SpCoord.sgnAut_apply, Function.update_of_ne huw, Function.update_self]

theorem ggTBJSpC_ofAdd_one_ne_one (hp : p.Prime) :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := by
  intro h
  exact (SpCoord.coord_zero_ne_one hp).symm (by simpa using congrArg Multiplicative.toAdd h)

theorem ggTBJSpC_ofAdd_one_inv_ne_one (hp : p.Prime) :
    ((Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)))⁻¹ ≠ 1 := by
  intro h
  exact ggTBJSpC_ofAdd_one_ne_one hp (inv_eq_one.mp h)

theorem ggTBJSpC_ofAdd_one_inv_ne_self (hp : p.Prime) (hp2 : p ≠ 2) :
    ((Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)))⁻¹ ≠
      Multiplicative.ofAdd (1 : ZMod p) := by
  intro h
  have h3 : (-1 : ZMod p) = 1 := by simpa using congrArg Multiplicative.toAdd h
  have h2 : (2 : ZMod p) = 0 := by linear_combination -h3
  exact SpCoord.coord_two_ne_zero hp hp2 h2

@[expose] noncomputable def ggTBJSpC_reflAut (p m : ℕ) {α : Type*}
    (t : Fin m → α) (u w : Fin m) : MulAut (Fin m → Multiplicative (ZMod p)) := by
  classical
  exact if t u = t w then SpCoord.permAut (Equiv.swap u w)
    else ggTBJSpC_invSwapAut p m u w

theorem ggTBJSpC_reflAut_apply_same {t : Fin m → α} {u w : Fin m} (h : t u = t w)
    (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f = SpCoord.permAut (Equiv.swap u w) f := by
  rw [ggTBJSpC_reflAut]
  simp only [ite_eq_left h]

theorem ggTBJSpC_reflAut_apply_mixed {t : Fin m → α} {u w : Fin m} (h : t u ≠ t w)
    (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f = ggTBJSpC_invSwapAut p m u w f := by
  rw [ggTBJSpC_reflAut]
  simp only [ite_eq_right h]

theorem ggTBJSpC_reflAut_sq {t : Fin m → α} {u w : Fin m} (huw : u ≠ w) :
    (ggTBJSpC_reflAut p m t u w) ^ 2 = 1 := by
  classical
  by_cases h : t u = t w
  · rw [show ggTBJSpC_reflAut p m t u w = SpCoord.permAut (Equiv.swap u w) from by
      rw [ggTBJSpC_reflAut]; simp only [ite_eq_left h]]
    exact SpCoord.permAut_swap_sq u w
  · rw [show ggTBJSpC_reflAut p m t u w = ggTBJSpC_invSwapAut p m u w from by
      rw [ggTBJSpC_reflAut]; simp only [ite_eq_right h]]
    exact ggTBJSpC_invSwapAut_sq huw

theorem ggTBJSpC_reflAut_card_fix (hp : p.Prime) (hp2 : p ≠ 2) {t : Fin m → α} {u w : Fin m}
    (huw : u ≠ w) :
    Nat.card {f : Fin m → Multiplicative (ZMod p) // ggTBJSpC_reflAut p m t u w f = f} * p =
      p ^ m := by
  classical
  by_cases h : t u = t w
  · rw [show ggTBJSpC_reflAut p m t u w = SpCoord.permAut (Equiv.swap u w) from by
      rw [ggTBJSpC_reflAut]; simp only [ite_eq_left h]]
    have hcard := SpCoord.card_fix_permAut_swap (p := p) (k := m) hp hp2 huw
    rwa [ggTBJSpC_card_coord] at hcard
  · rw [show ggTBJSpC_reflAut p m t u w = ggTBJSpC_invSwapAut p m u w from by
      rw [ggTBJSpC_reflAut]; simp only [ite_eq_right h]]
    exact ggTBJSpC_card_fix_invSwapAut hp hp2 huw

theorem ggTBJSpC_reflAut_apply_of_ne {t : Fin m → α} {u w x : Fin m} (huw : u ≠ w)
    (hux : x ≠ u) (hwx : x ≠ w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f x = f x := by
  classical
  by_cases h : t u = t w
  · rw [ggTBJSpC_reflAut_apply_same h, SpCoord.permAut_apply, Function.comp_apply,
      Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hux hwx]
  · rw [ggTBJSpC_reflAut_apply_mixed h, ggTBJSpC_invSwapAut_apply huw, ite_eq_right hux,
      ite_eq_right hwx]

theorem ggTBJSpC_reflAut_apply_right_same {t : Fin m → α} {u w : Fin m} (huw : u ≠ w)
    (h : t u = t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f w = f u := by
  rw [ggTBJSpC_reflAut_apply_same h, SpCoord.permAut_apply, Function.comp_apply,
    Equiv.swap_inv, Equiv.swap_apply_right]

theorem ggTBJSpC_reflAut_apply_right_mixed {t : Fin m → α} {u w : Fin m} (huw : u ≠ w)
    (h : t u ≠ t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f w = (f u)⁻¹ := by
  rw [ggTBJSpC_reflAut_apply_mixed h, ggTBJSpC_invSwapAut_apply huw, ite_eq_right (Ne.symm huw),
    ite_eq_left rfl]

theorem ggTBJSpC_reflAut_apply_left_same {t : Fin m → α} {u w : Fin m} (huw : u ≠ w)
    (h : t u = t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f u = f w := by
  rw [ggTBJSpC_reflAut_apply_same h, SpCoord.permAut_apply, Function.comp_apply,
    Equiv.swap_inv, Equiv.swap_apply_left]

theorem ggTBJSpC_reflAut_apply_left_mixed {t : Fin m → α} {u w : Fin m} (huw : u ≠ w)
    (h : t u ≠ t w) (f : Fin m → Multiplicative (ZMod p)) :
    ggTBJSpC_reflAut p m t u w f u = (f w)⁻¹ := by
  rw [ggTBJSpC_reflAut_apply_mixed h, ggTBJSpC_invSwapAut_apply huw, ite_eq_left rfl]

theorem ggTBJSpC_reflAut_noncomm (hp : p.Prime) {t : Fin m → α}
    {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ggTBJSpC_reflAut p m t a b * ggTBJSpC_reflAut p m t b c ≠
      ggTBJSpC_reflAut p m t b c * ggTBJSpC_reflAut p m t a b := by
  classical
  intro hconj
  let f₀ : Fin m → Multiplicative (ZMod p) :=
    Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p))
  have h := congrFun (congrArg (fun s : MulAut (Fin m → Multiplicative (ZMod p)) => s f₀)
    hconj) c
  simp only [MulAut.mul_apply] at h
  have hR : (ggTBJSpC_reflAut p m t a b (ggTBJSpC_reflAut p m t b c f₀)) c =
      (ggTBJSpC_reflAut p m t b c f₀) c :=
    ggTBJSpC_reflAut_apply_of_ne hab hac.symm hbc.symm _
  have hfa : f₀ a = 1 := by
    rw [show f₀ = Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p)) from rfl,
      Pi.mulSingle_apply, ite_eq_right hab]
  have hL : (ggTBJSpC_reflAut p m t b c (ggTBJSpC_reflAut p m t a b f₀)) c = 1 := by
    by_cases h2 : t b = t c
    · rw [ggTBJSpC_reflAut_apply_right_same hbc h2]
      by_cases h1 : t a = t b
      · rw [ggTBJSpC_reflAut_apply_right_same hab h1, hfa]
      · rw [ggTBJSpC_reflAut_apply_right_mixed hab h1, hfa, inv_one]
    · rw [ggTBJSpC_reflAut_apply_right_mixed hbc h2]
      by_cases h1 : t a = t b
      · rw [ggTBJSpC_reflAut_apply_right_same hab h1, hfa, inv_one]
      · rw [ggTBJSpC_reflAut_apply_right_mixed hab h1, hfa, inv_one, inv_one]
  have hval : (ggTBJSpC_reflAut p m t b c f₀) c =
      if t b = t c then Multiplicative.ofAdd (1 : ZMod p)
        else (Multiplicative.ofAdd (1 : ZMod p))⁻¹ := by
    by_cases h2 : t b = t c
    · rw [ggTBJSpC_reflAut_apply_right_same hbc h2, ite_eq_left h2,
        show f₀ = Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p)) from rfl,
        Pi.mulSingle_eq_same]
    · rw [ggTBJSpC_reflAut_apply_right_mixed hbc h2, ite_eq_right h2,
        show f₀ = Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p)) from rfl,
        Pi.mulSingle_eq_same]
  rw [hR, hL, hval] at h
  by_cases h2 : t b = t c
  · rw [ite_eq_left h2] at h
    exact ggTBJSpC_ofAdd_one_ne_one hp h
  · rw [ite_eq_right h2] at h
    exact ggTBJSpC_ofAdd_one_inv_ne_one hp h

end CFSG.StandardType

end
