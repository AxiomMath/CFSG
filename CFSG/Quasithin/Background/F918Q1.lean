module

public import CFSG.Quasithin.Background.D36Support
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.B1More8

public section

namespace CFSG.Quasithin

structure GluedPair {Y : Type} [CommGroup Y] (X : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop where
  sup_eq : U ⊔ U' = ⊤
  perm : ∀ g ∈ X, (g ∈ stabSub U ∧ g ∈ stabSub U') ∨
    (U.map g.toMonoidHom = U' ∧ U'.map g.toMonoidHom = U)
  swap : ∃ s ∈ X, U.map s.toMonoidHom = U' ∧ U'.map s.toMonoidHom = U
  faithful : ∀ g ∈ X, (∀ y : Y, g y * y⁻¹ ∈ U ⊓ U') → g = 1

section Aux

variable {Y : Type} [CommGroup Y] [Finite Y]

private theorem exists_rat_of_qhatOf_leQ1 {X : Subgroup (MulAut Y)} {c : ℚ}
    (h : qhatOf X ≤ (c : WithTop ℚ)) : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ c :=
  D36.exists_rat_of_qhatOf_le h

private theorem qhatOf_autSub_le_of_offenderQ1 (hY : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)}
    {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {U : Subgroup Y}
    (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) : qhatOf (autSub X U) ≤ (r : WithTop ℚ) :=
  D36.qhatOf_autSub_le_of_offender hY hr hA hU hUA

omit [Finite Y] in
theorem apply_mem_map_iffQ1 {J : Subgroup Y} (g : MulAut Y) (x : Y) :
    g x ∈ J.map g.toMonoidHom ↔ x ∈ J := by
  rw [Subgroup.mem_map_equiv]; simp

theorem case_stabQ1 (hY : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hUU' : U ≠ U') {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) (hA : A ∈ QhatStar X) (hA2 : IsA2 X A) (hAU : A ≤ stabSub U) :
    qhatOf (autSub X U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hAU' : A ≤ stabSub U' := by
    intro g hg
    rcases hP.perm g (hA2.1 hg) with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exfalso
      have := mem_stabSub_iff_map_eq.mp (hAU hg)
      exact hUU' (this.symm.trans h1)
  by_cases hne : commSub U A = ⊥
  · obtain ⟨s, hsX, hs1, hs2⟩ := hP.swap
    have hA' : conjBy s A ∈ QhatStar X := conjBy_mem_QhatStar hA hsX
    obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a₀ ∈ A, a₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hA2.2.1 (eq_bot_iff.mpr fun g hg => hcon g hg)
    obtain ⟨y, hy⟩ : ∃ y : Y, a₀ y ≠ y := by
      by_contra hcon
      push Not at hcon
      exact ha₀ (MulEquiv.ext hcon)
    obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (hP.sup_eq ▸ Subgroup.mem_top y)
    have hfixU : a₀ u = u := (commSub_eq_bot_iff.mp hne) hu a₀ ha₀A
    have hu'ne : a₀ u' ≠ u' := by
      intro h
      apply hy
      rw [map_mul, hfixU, h]
    have f1 : ∀ z, s z ∈ U ↔ z ∈ U' := fun z => by
      rw [← hs2]; exact apply_mem_map_iffQ1 s z
    have f2 : ∀ z, s⁻¹ z ∈ U' ↔ z ∈ U := fun z => by
      rw [← f1 (s⁻¹ z)]; simp
    have hstab' : conjBy s A ≤ stabSub U := by
      intro g hg x
      rw [mem_conjBy_iff] at hg
      have haU' := hAU' hg
      have hg_eq : g = s * (s⁻¹ * g * s) * s⁻¹ := by group
      have hgx : g x = s ((s⁻¹ * g * s) (s⁻¹ x)) := by
        conv_lhs => rw [hg_eq]
        simp [MulAut.mul_apply]
      rw [hgx, f1, haU', f2]
    have hne' : commSub U (conjBy s A) ≠ ⊥ := by
      intro h
      have hg₀ : s * a₀ * s⁻¹ ∈ conjBy s A := by
        rw [mem_conjBy_iff]; simpa [mul_assoc] using ha₀A
      have hx₀ : s u' ∈ U := (f1 u').mpr hu'
      have := (commSub_eq_bot_iff.mp h) hx₀ _ hg₀
      apply hu'ne
      have h2 : s (a₀ u') = s u' := by simpa [MulAut.mul_apply] using this
      exact s.injective h2
    exact (qhatOf_autSub_le_of_offenderQ1 hY hr hA' hstab' hne').trans (WithTop.coe_le_coe.mpr hr2)
  · exact (qhatOf_autSub_le_of_offenderQ1 hY hr hA hAU hne).trans (WithTop.coe_le_coe.mpr hr2)

private theorem case_swapQ1 (hY : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hUU' : U ≠ U') (hD : rk ↥(U ⊓ U') ≤ 1)
    (h3 : rk ↥(U ⊓ U') + 2 < rk ↥U) {r : ℚ} (hr2 : r ≤ 2) (hA2 : IsA2 X A)
    (hAr : rAV A ≤ r) (hAk3 : commSeries A 3 = ⊥) (hAU : ¬ A ≤ stabSub U) :
    qhatOf (autSub X U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ stabSub U := by
    by_contra hcon
    push Not at hcon
    exact hAU fun g hg => hcon g hg
  obtain ⟨ha1, ha2⟩ : U.map a.toMonoidHom = U' ∧ U'.map a.toMonoidHom = U :=
    (hP.perm a (hA2.1 haA)).resolve_left fun h => haU h.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup (MulAut Y), A₀ = A ⊓ stabSub U := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ A₀ ↔ g ∈ A ∧ g ∈ stabSub U := fun g => by rw [hA₀]; exact Subgroup.mem_inf
  have hA₀le : A₀ ≤ A := fun g hg => ((hmem g).mp hg).1
  have hA₀X : A₀ ≤ X := hA₀le.trans hA2.1
  have hstab : A₀ ≤ stabSub U := fun g hg => ((hmem g).mp hg).2
  have hA₀el : IsElemAbelian2 A₀ := ⟨fun g hg h hh => hAel.1 g (hA₀le hg) h (hA₀le hh),
    fun g hg => hAel.2 g (hA₀le hg)⟩
  have haa : a * a = 1 := by simpa [pow_two] using hAel.2 a haA
  have hcomm : ∀ g ∈ A₀, g * a = a * g := fun g hg => hAel.1 g (hA₀le hg) a haA
  have hsum' : U ⊔ U.map a.toMonoidHom = ⊤ := by rw [ha1]; exact hP.sup_eq
  have hDeq : U ⊓ U.map a.toMonoidHom = U ⊓ U' := by rw [ha1]
  have fa1 : ∀ x, a x ∈ U' ↔ x ∈ U := fun x => by rw [← ha1]; exact apply_mem_map_iffQ1 a x
  have fa2 : ∀ x, a x ∈ U ↔ x ∈ U' := fun x => by rw [← ha2]; exact apply_mem_map_iffQ1 a x
  have hDa : ∀ d ∈ U ⊓ U', a d ∈ U ⊓ U' := fun d hd => ⟨(fa2 d).mpr hd.2, (fa1 d).mpr hd.1⟩
  have hfaith' : ∀ g ∈ A₀, (∀ u ∈ U, g u * u⁻¹ ∈ U ⊓ U.map a.toMonoidHom) → g = 1 := by
    intro g hg h
    rw [hDeq] at h
    refine hP.faithful g (hA₀X hg) fun y => ?_
    obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (hP.sup_eq ▸ Subgroup.mem_top y)
    have e : g (u * u') * (u * u')⁻¹ = (g u * u⁻¹) * (g u' * u'⁻¹) := by
      rw [map_mul, mul_inv_rev, mul_comm u'⁻¹ u⁻¹]
      exact mul_mul_mul_comm _ _ _ _
    rw [e]
    refine (U ⊓ U').mul_mem (h u hu) ?_
    obtain ⟨w, hw, hwu⟩ : u' ∈ U.map a.toMonoidHom := ha1 ▸ hu'
    have hwu' : a w = u' := hwu
    subst hwu'
    have hc : g (a w) = a (g w) := by
      have := congrArg (fun φ : MulAut Y => φ w) (hcomm g hg)
      simpa [MulAut.mul_apply] using this
    have : g (a w) * (a w)⁻¹ = a (g w * w⁻¹) := by rw [hc, map_mul, map_inv]
    rw [this]
    exact hDa _ (h w hw)
  have hAeq : A = A₀ ⊔ Subgroup.zpowers a := by
    apply le_antisymm
    · intro g hg
      by_cases hgU : g ∈ stabSub U
      · exact Subgroup.mem_sup_left ((hmem g).mpr ⟨hg, hgU⟩)
      · rcases hP.perm g (hA2.1 hg) with ⟨h, -⟩ | ⟨hg1, hg2⟩
        · exact absurd h hgU
        · have hg1' : ∀ x, g x ∈ U' ↔ x ∈ U := fun x => by
            rw [← hg1]; exact apply_mem_map_iffQ1 g x
          have hainv : ∀ z, a⁻¹ z ∈ U ↔ z ∈ U' := fun z => by
            rw [← fa1 (a⁻¹ z)]; simp
          have hstab2 : a⁻¹ * g ∈ stabSub U := by
            intro x
            rw [MulAut.mul_apply, hainv, hg1']
          have hmem2 : a⁻¹ * g ∈ A₀ := (hmem _).mpr ⟨A.mul_mem (A.inv_mem haA) hg, hstab2⟩
          have : g = a * (a⁻¹ * g) := by group
          rw [this, sup_comm]
          exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) hmem2
    · exact sup_le hA₀le (Subgroup.zpowers_le.mpr haA)
  have hrkA : rk ↥A = rk ↥A₀ + 1 := by
    have hidx : (A₀.subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a, haA⟩, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmem, hmem]
      by_cases hbU : (b : MulAut Y) ∈ stabSub U
      · right
        refine ⟨⟨b.2, hbU⟩, fun hba => ?_⟩
        apply hUU'
        ext x
        have h1 := hba.2 x
        rw [MulAut.mul_apply] at h1
        have := (hbU (a x)).trans (fa2 x)
        exact (this.symm.trans h1).symm
      · left
        refine ⟨⟨A.mul_mem b.2 haA, ?_⟩, fun hb => hbU hb.2⟩
        rcases hP.perm (b : MulAut Y) (hA2.1 b.2) with ⟨h, -⟩ | ⟨hb1, hb2⟩
        · exact absurd h hbU
        · intro x
          rw [MulAut.mul_apply]
          have hb2' : ∀ z, (b : MulAut Y) z ∈ U ↔ z ∈ U' := fun z => by
            rw [← hb2]; exact apply_mem_map_iffQ1 (b : MulAut Y) z
          rw [hb2', fa1]
    have hc := Subgroup.card_mul_index (A₀.subgroupOf A)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀le).toEquiv] at hc
    unfold rk
    rw [← hc, padicValNat.mul Nat.card_pos.ne' (by norm_num), padicValNat_self]
  have hFeq : fixV A = fixV A₀ ⊓ fixV (Subgroup.zpowers a) := by
    rw [hAeq, fixV_sup_eq_inf_fixV]
  have hrA : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h1 := hA2.rAV_mul
    have h2 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_right (hAr.trans hr2) (Nat.cast_nonneg _)
    exact_mod_cast h2
  have hY1 : rk Y ≤ rk ↥(fixV A₀ ⊓ fixV (Subgroup.zpowers a)) + 2 * (rk ↥A₀ + 1) := by
    have h := rk_add_rkIdx (fixV A)
    rw [hFeq] at h hrA
    rw [hrkA] at hrA
    omega
  obtain ⟨hA₀ne, hbound⟩ := swap_rank_bound hY hA₀el haa hcomm hstab hsum' hfaith'
    (hDeq ▸ hD) (hDeq ▸ h3) hY1
  have hbot : autSub A₀ U ≠ ⊥ := by
    intro h
    apply hA₀ne
    have h0 := (autSub_eq_bot_iff hstab).mp h
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine hfaith' g hg fun u hu => ?_
    have := (commSub_eq_bot_iff.mp h0) hu g hg
    rw [this]
    simp
  have hAk3' : commSeries A₀ 3 = ⊥ :=
    le_bot_iff.mp (hAk3 ▸ commSeries_mono hA₀le 3)
  refine kq_le_iff.mpr ⟨autSub A₀ U, ⟨autSub_mono hA₀X U, hbot, isElemAbelian2_autSub U hA₀el⟩,
    commSeries_autSub_eq_bot hstab hAk3', ?_⟩
  have hker : A₀ ⊓ centSub U = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine hfaith' g hg.1 fun u hu => ?_
    rw [hg.2 u hu]
    simp
  have hcardB : rk ↥(autSub A₀ U) = rk ↥A₀ := by
    have h := card_autSub_mul hstab
    rw [hker] at h
    have h1 : Nat.card ↥(⊥ : Subgroup (MulAut Y)) = 1 := by simp
    rw [h1, mul_one] at h
    unfold rk
    rw [h]
  have hidxB : rkIdx (fixV (autSub A₀ U)) ≤ 2 * rk ↥A₀ := by
    have h := rk_add_rkIdx (fixV (autSub A₀ U))
    rw [rk_fixV_autSub hstab] at h
    omega
  have hrkpos : 0 < rk ↥A₀ := hA₀el.rk_pos hA₀ne
  unfold rAV
  rw [hcardB, div_le_iff₀ (by exact_mod_cast hrkpos)]
  exact_mod_cast (by omega : rkIdx (fixV (autSub A₀ U)) ≤ 2 * rk ↥A₀)

theorem glued_qhat_le (hY : ∀ y : Y, y ^ 2 = 1) {X : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hD : rk ↥(U ⊓ U') ≤ 1) (h3 : rk ↥(U ⊓ U') + 2 < rk ↥U)
    (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) :
    qhatOf (autSub X U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨r, hr, hr2⟩ := exists_rat_of_qhatOf_leQ1 hq
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  obtain ⟨r', hr', -, hAk, -⟩ := QhatStar_spec hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  obtain ⟨⟨hA2, hAr⟩, hAk3⟩ := hAk
  have hUU' : U ≠ U' := by
    intro h
    subst h
    rw [inf_idem] at hD h3
    omega
  by_cases hAU : A ≤ stabSub U
  · exact case_stabQ1 hY hP hUU' hr hr2 hA hA2 hAU
  · exact case_swapQ1 hY hP hUU' hD h3 hr2 hA2 hAr.le hAk3 hAU

end Aux

end CFSG.Quasithin
