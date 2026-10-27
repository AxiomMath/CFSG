module

public import CFSG.Quasithin.Background.F918Q1

public section

namespace CFSG.Quasithin

section Aux

variable {Y : Type} [CommGroup Y]

private theorem ya_mem_iff_of_map_eq {J J' : Subgroup Y} {g : MulAut Y}
    (h : J.map g.toMonoidHom = J') (x : Y) : g x ∈ J' ↔ x ∈ J := by
  rw [← h]
  exact Subgroup.mem_map_iff_mem g.injective

private theorem ya_quad_apply {A : Subgroup (MulAut Y)} (hAq : commSeries A 2 = ⊥)
    {a c : MulAut Y} (ha : a ∈ A) (hc : c ∈ A) (w : Y) : c (a w * w⁻¹) = a w * w⁻¹ := by
  have h3 : a w * w⁻¹ ∈ commSub (⊤ : Subgroup Y) A :=
    Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩
  have h4 : c (a w * w⁻¹) * (a w * w⁻¹)⁻¹ ∈ commSub (commSub (⊤ : Subgroup Y) A) A :=
    Subgroup.subset_closure ⟨c, hc, _, h3, rfl⟩
  have h5 : commSub (commSub (⊤ : Subgroup Y) A) A = ⊥ := hAq
  rw [h5, Subgroup.mem_bot] at h4
  exact mul_inv_eq_one.1 h4

private theorem ya_stab_eq_one {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hUU' : U ≠ U') (hAX : A ≤ X) (hAq : commSeries A 2 = ⊥)
    {τ : MulAut Y} (hτA : τ ∈ A) (hτ1 : U.map τ.toMonoidHom = U')
    (hτ2 : U'.map τ.toMonoidHom = U) {b : MulAut Y} (hb : b ∈ A) (hbU : b ∈ stabSub U) :
    b = 1 := by
  have hbU' : b ∈ stabSub U' := by
    rcases hP.perm b (hAX hb) with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd ((mem_stabSub_iff_map_eq.mp hbU).symm.trans h1) hUU'
  have key : ∀ y : Y, b y * y⁻¹ = b (τ y) * (τ y)⁻¹ := by
    intro y
    have h := ya_quad_apply hAq hτA hb y
    rw [map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact (mul_comm _ _).trans h.symm
  refine hP.faithful b (hAX hb) fun y => ?_
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (hP.sup_eq ▸ Subgroup.mem_top y)
  have e : b (u * u') * (u * u')⁻¹ = (b u * u⁻¹) * (b u' * u'⁻¹) := by
    rw [map_mul, mul_inv_rev, mul_comm u'⁻¹ u⁻¹]
    exact mul_mul_mul_comm _ _ _ _
  have h1 : b u * u⁻¹ ∈ U ⊓ U' := by
    refine ⟨U.mul_mem ((hbU u).mpr hu) (U.inv_mem hu), ?_⟩
    rw [key u]
    have hτu : τ u ∈ U' := (ya_mem_iff_of_map_eq hτ1 u).mpr hu
    exact U'.mul_mem ((hbU' _).mpr hτu) (U'.inv_mem hτu)
  have h2 : b u' * u'⁻¹ ∈ U ⊓ U' := by
    refine ⟨?_, U'.mul_mem ((hbU' u').mpr hu') (U'.inv_mem hu')⟩
    rw [key u']
    have hτu : τ u' ∈ U := (ya_mem_iff_of_map_eq hτ2 u').mpr hu'
    exact U.mul_mem ((hbU _).mpr hτu) (U.inv_mem hτu)
  rw [e]
  exact (U ⊓ U').mul_mem h1 h2

private theorem ya_card_le [Finite Y] {U U' : Subgroup Y} {τ : MulAut Y}
    (hτ1 : U.map τ.toMonoidHom = U') :
    Nat.card ↥U ≤ Nat.card ↥(U ⊓ U') * Nat.card ↥(commV (Subgroup.zpowers τ)) := by
  let φ : ↥U →* Y := (commHom τ).comp U.subtype
  have hker : φ.ker ≤ (U ⊓ U').subgroupOf U := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : τ (u : Y) = u := mul_inv_eq_one.1 hu
    have h2 : τ (u : Y) ∈ U' := (ya_mem_iff_of_map_eq hτ1 u).mpr u.2
    exact Subgroup.mem_subgroupOf.2 ⟨u.2, h1 ▸ h2⟩
  have hrange : φ.range ≤ commV (Subgroup.zpowers τ) := by
    rintro _ ⟨u, rfl⟩
    exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, u, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ U') := by
    have := Subgroup.card_le_of_le hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ U' ≤ U)).toEquiv]
      at this
  calc Nat.card ↥U = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ _ := Nat.mul_le_mul h2 (Subgroup.card_le_of_le hrange)

private theorem ya_rkIdx_ge [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1) {g : MulAut Y}
    (h : 8 ≤ Nat.card ↥(commV (Subgroup.zpowers g))) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers g)) := by
  rw [rkIdx_fixV_zpowers]
  by_contra hlt
  push Not at hlt
  have h1 := card_eq_two_pow hY (commV (Subgroup.zpowers g))
  have h2 : 2 ^ rk ↥(commV (Subgroup.zpowers g)) ≤ 2 ^ 2 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Aux

theorem glued_quad_offender_stab {Y : Type} [CommGroup Y] [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1)
    {X : Subgroup (MulAut Y)} {U U' : Subgroup Y} (hP : GluedPair X U U')
    (hrank : rk ↥(U ⊓ U') + 2 < rk ↥U)
    {A : Subgroup (MulAut Y)} (hAX : A ≤ X) (hAne : A ≠ ⊥) (hAel : IsElemAbelian2 A)
    (hAq : commSeries A 2 = ⊥) (hAr : rAV A ≤ 2) : A ≤ stabSub U := by
  by_contra hAU
  obtain ⟨τ, hτA, hτU⟩ : ∃ τ ∈ A, τ ∉ stabSub U := by
    by_contra hcon
    push Not at hcon
    exact hAU fun g hg => hcon g hg
  obtain ⟨hτ1, hτ2⟩ : U.map τ.toMonoidHom = U' ∧ U'.map τ.toMonoidHom = U :=
    (hP.perm τ (hAX hτA)).resolve_left fun h => hτU h.1
  have hUU' : U ≠ U' := by
    intro h
    rw [← h, inf_idem] at hrank
    omega
  have hτsq : τ ^ 2 = 1 := hAel.2 τ hτA
  have hτne : τ ≠ 1 := by
    rintro rfl
    exact hτU (stabSub U).one_mem
  have hAeq : A = Subgroup.zpowers τ := by
    refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.mpr hτA)
    by_cases hgU : g ∈ stabSub U
    · rw [ya_stab_eq_one hP hUU' hAX hAq hτA hτ1 hτ2 hg hgU]
      exact Subgroup.one_mem _
    · obtain ⟨-, hg2⟩ := (hP.perm g (hAX hg)).resolve_left fun h => hgU h.1
      have hgτ : g * τ ∈ stabSub U := fun x => by
        rw [MulAut.mul_apply, ya_mem_iff_of_map_eq hg2, ya_mem_iff_of_map_eq hτ1]
      have h1 := ya_stab_eq_one hP hUU' hAX hAq hτA hτ1 hτ2 (A.mul_mem hg hτA) hgτ
      rw [mul_eq_one_iff_eq_inv.mp h1,
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hτsq)]
      exact Subgroup.mem_zpowers τ
  have hcardA : Nat.card ↥A = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hAeq, Nat.card_zpowers, orderOf_eq_prime hτsq hτne]
  have hrkA : rk ↥A = 1 := by
    unfold rk
    rw [hcardA]
    simp
  have hfix : fixV A = fixV (Subgroup.zpowers τ) := by rw [hAeq]
  have hcomm : 8 ≤ Nat.card ↥(commV (Subgroup.zpowers τ)) := by
    have h1 := ya_card_le hτ1
    rw [card_eq_two_pow hY U, card_eq_two_pow hY (U ⊓ U')] at h1
    have h2 : 2 ^ (rk ↥(U ⊓ U') + 3) ≤ 2 ^ rk ↥U :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at h2
    have h3 := Nat.le_of_mul_le_mul_left (h2.trans h1) (by positivity)
    omega
  have hA2 : IsA2 X A := ⟨hAX, hAne, hAel⟩
  have hmul := hA2.rAV_mul
  rw [hrkA, hfix, Nat.cast_one, mul_one] at hmul
  have h3 : (3 : ℚ) ≤ rkIdx (fixV (Subgroup.zpowers τ)) := by
    exact_mod_cast ya_rkIdx_ge hY hcomm
  linarith

end CFSG.Quasithin
