module

public import CFSG.Quasithin.Background.F918N0
import CFSG.Quasithin.Background.B1More8
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

section Transport

variable {U U' : Type*} [CommGroup U] [CommGroup U']

private theorem n8_fixV_map_congr (e : U' ≃* U) (B : Subgroup (MulAut U')) :
    fixV (B.map (MulAut.congr e).toMonoidHom) = (fixV B).map e.toMonoidHom :=
  CFSG.Quasithin.fixV_map_congr_equiv e B

private theorem n8_isStrongFFModule_of_map_le [Finite U] [Finite U'] (e : U' ≃* U)
    {G : Subgroup (MulAut U)} {G' : Subgroup (MulAut U')}
    (hG : G'.map (MulAut.congr e).toMonoidHom ≤ G) (h : IsStrongFFModule G') :
    IsStrongFFModule G := by
  obtain ⟨B, hBG, hB0, hBe, hlt⟩ := h
  refine ⟨B.map (MulAut.congr e).toMonoidHom, (Subgroup.map_mono hBG).trans hG, ?_, ?_, ?_⟩
  · intro hb
    exact hB0 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr e).injective).mp hb)
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBe.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hBe.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, n8_fixV_map_congr,
      Subgroup.card_map_of_injective e.injective, ← Nat.card_congr e.toEquiv]
    exact hlt

end Transport

section Conj

variable {X : Type} [CommGroup X]

private theorem n8_mem_stabSub_map {g a : MulAut X} {U : Subgroup X} :
    a ∈ stabSub (U.map g.toMonoidHom) ↔ g⁻¹ * a * g ∈ stabSub U := by
  simp only [mem_stabSub, Subgroup.mem_map_equiv, MulAut.mul_apply]
  constructor
  · intro h u
    have := h (g u)
    simpa [MulAut.inv_apply] using this
  · intro h w
    have := h (g.symm w)
    simpa [MulAut.inv_apply] using this

private def n8Res (g : MulAut X) (U : Subgroup X) : ↥U ≃* ↥(U.map g.toMonoidHom) where
  toFun u := ⟨g u, Subgroup.mem_map_of_mem _ u.2⟩
  invFun w := ⟨g.symm w, Subgroup.mem_map_equiv.mp w.2⟩
  left_inv u := Subtype.ext (g.symm_apply_apply (u : X))
  right_inv w := Subtype.ext (g.apply_symm_apply (w : X))
  map_mul' a b := Subtype.ext (map_mul g (a : X) (b : X))

private theorem n8_map_autSub_conj_le (g : MulAut X) (D : Subgroup (MulAut X)) (U : Subgroup X) :
    (autSub (conjAutSub g D) (U.map g.toMonoidHom)).map
      (MulAut.congr (n8Res g U).symm).toMonoidHom ≤ autSub D U := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨k, hk, rfl⟩ := mem_autSub.mp hφ
  obtain ⟨d, hd, hdk⟩ := hk
  have hdU : d ∈ stabSub U := by
    have := n8_mem_stabSub_map.mp k.2
    rw [← hdk] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  refine mem_autSub.mpr ⟨⟨d, hdU⟩, hd, ?_⟩
  ext u
  show d u = g.symm ((k : MulAut X) (g u))
  rw [← hdk]
  simp [MulAut.conj_apply]

private theorem n8_not_isStrongFFModule_conj [Finite X] {D D' : Subgroup (MulAut X)} {U : Subgroup X}
    (g : MulAut X) (hD : D' ≤ conjAutSub g D) (h : ¬ IsStrongFFModule (autSub D U)) :
    ¬ IsStrongFFModule (autSub D' (U.map g.toMonoidHom)) := fun hs =>
  h (n8_isStrongFFModule_of_map_le (n8Res g U).symm
    ((Subgroup.map_mono (autSub_mono hD _)).trans (n8_map_autSub_conj_le g D U)) hs)

end Conj

section Rank

variable {V : Type*} [CommGroup V]

private theorem n8_fixV_eq_sup_of_direct {A : Subgroup (MulAut V)} {U W : Subgroup V}
    (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) (hAU : A ≤ stabSub U) (hAW : A ≤ stabSub W) :
    fixV A = (U ⊓ fixV A) ⊔ (W ⊓ fixV A) := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_right inf_le_right)
  have hvt : v ∈ U ⊔ W := by rw [hD]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hvt
  have key : ∀ a ∈ A, a y = y ∧ a z = z := by
    intro a ha
    have h1 : a (y * z) = y * z := hv a ha
    rw [map_mul] at h1
    have hay : a y ∈ U := (hAU ha y).2 hy
    have haz : a z ∈ W := (hAW ha z).2 hz
    have h2 : a y / y = z / a z := by
      rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
    have h3 : a y / y ∈ U ⊓ W := ⟨U.div_mem hay hy, h2 ▸ W.div_mem hz haz⟩
    rw [hI, Subgroup.mem_bot, div_eq_one] at h3
    refine ⟨h3, ?_⟩
    rw [h3] at h1
    exact mul_left_cancel h1
  exact Subgroup.mul_mem_sup ⟨hy, fun a ha => (key a ha).1⟩ ⟨hz, fun a ha => (key a ha).2⟩

private theorem n8_isA2_autSub {D A : Subgroup (MulAut V)} {U : Subgroup V} (hA : IsA2 D A)
    (hAU : A ≤ stabSub U) (hf : A ⊓ centSub U = ⊥) : IsA2 (autSub D U) (autSub A U) := by
  refine hA.autSub hAU fun hc => hA.2.1 ((Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_)
  have : a ∈ A ⊓ centSub U := ⟨ha, fun u hu => commSub_eq_bot_iff.mp hc hu a ha⟩
  rwa [hf] at this

variable [Finite V]

private theorem n8_rk_fixV_of_direct {A : Subgroup (MulAut V)} {U W : Subgroup V}
    (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) (hAU : A ≤ stabSub U) (hAW : A ≤ stabSub W) :
    rk ↥(fixV A) = rk ↥(U ⊓ fixV A) + rk ↥(W ⊓ fixV A) := by
  have h := rk_sup_add_rk_inf (U ⊓ fixV A) (W ⊓ fixV A)
  have hbot : (U ⊓ fixV A) ⊓ (W ⊓ fixV A) = ⊥ := by
    rw [eq_bot_iff, ← hI]
    exact inf_le_inf inf_le_left inf_le_left
  rw [hbot, rk_bot, add_zero, ← n8_fixV_eq_sup_of_direct hD hI hAU hAW] at h
  exact h

private theorem n8_rk_le_rkIdx (hV : ∀ v : V, v ^ 2 = 1) {G B : Subgroup (MulAut V)}
    (hG : ¬ IsStrongFFModule G) (hB : IsA2 G B) : rk B ≤ rkIdx (fixV B) :=
  not_lt.1 fun hlt => hG ⟨B, hB.1, hB.2.1, hB.2.2, (B1.card_lt_iff hV hB.2.2).2 hlt⟩

private theorem n8_isFFStarOffender (hV : ∀ v : V, v ^ 2 = 1) {G B : Subgroup (MulAut V)}
    (hG : ¬ IsStrongFFModule G) (hB : IsA2 G B) (hr : rkIdx (fixV B) ≤ rk B) :
    IsFFStarOffender G B := by
  have h1 : rAV B = 1 :=
    le_antisymm ((rAV_le_one_iff hV hB).2 ((B1.card_le_iff hV hB.2.2).2 hr))
      (not_lt.1 fun hlt => hG ((isStrongFFModule_iff hV).2 ⟨B, hB, hlt⟩))
  have hmem : B ∈ {A | IsA2 G A ∧ rAV A = 1} := ⟨hB, h1⟩
  rw [← B1_4_6 hV hG] at hmem
  exact hmem

private theorem n8_isFFStarOffender_pair (hV : ∀ v : V, v ^ 2 = 1) {A D₁ D₂ : Subgroup (MulAut V)}
    {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥) (hA₁ : A ≤ stabSub V₁)
    (hA₂ : A ≤ stabSub V₂) (hf₁ : A ⊓ centSub V₁ = ⊥) (hf₂ : A ⊓ centSub V₂ = ⊥) (hD₁ : IsA2 D₁ A)
    (hD₂ : IsA2 D₂ A) (hrk : rkIdx (fixV A) ≤ 2 * rk A) (hns₁ : ¬ IsStrongFFModule (autSub D₁ V₁))
    (hns₂ : ¬ IsStrongFFModule (autSub D₂ V₂)) :
    IsFFStarOffender (autSub D₁ V₁) (autSub A V₁) ∧ IsFFStarOffender (autSub D₂ V₂) (autSub A V₂) := by
  have hV₁ : ∀ v : ↥V₁, v ^ 2 = 1 := B1.sq_eq_one_sub hV V₁
  have hV₂ : ∀ v : ↥V₂, v ^ 2 = 1 := B1.sq_eq_one_sub hV V₂
  have hB₁ := n8_isA2_autSub hD₁ hA₁ hf₁
  have hB₂ := n8_isA2_autSub hD₂ hA₂ hf₂
  have e1 := rk_autSub_eq_of_faithful hA₁ hf₁
  have e2 := rk_autSub_eq_of_faithful hA₂ hf₂
  have e3 := rkIdx_autSub_add hA₁
  have e4 := rkIdx_autSub_add hA₂
  have e5 := rk_add_rkIdx (fixV A)
  have e6 := n8_rk_fixV_of_direct hsup hinf hA₁ hA₂
  have e7 : rk V = rk ↥V₁ + rk ↥V₂ := by
    have := rk_sup_add_rk_inf V₁ V₂
    rw [hsup, hinf, rk_bot, add_zero, rk_top] at this
    exact this
  have l1 := n8_rk_le_rkIdx hV₁ hns₁ hB₁
  have l2 := n8_rk_le_rkIdx hV₂ hns₂ hB₂
  exact ⟨n8_isFFStarOffender hV₁ hns₁ hB₁ (by omega), n8_isFFStarOffender hV₂ hns₂ hB₂ (by omega)⟩

end Rank

section Final

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

theorem z35_elim (i3 : D35InspUniq) (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {A : Subgroup (MulAut X)}
    (hAQ : A ∈ QhatStar (Mb ⊔ Tb)) (hAT : A ≤ Tb) (hAV : A ≤ stabSub Vb)
    (hidx : (Tb ⊓ stabSub Vb).relIndex Tb ≤ 2)
    (hfaith : ∀ t ∈ Tb, ∀ a ∈ A, (∀ w ∈ orbSup A (Vb.map t.toMonoidHom), a w = w) → a = 1)
    (hcase : ∃ A₀ : Subgroup (MulAut X),
      B42Case8 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A₀ Vb) ∨
      B42Case11 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A₀ Vb)) : False := by
  have hnot : ¬ Tb ≤ stabSub Vb := fun hle => by
    have h1 : orbSup Tb Vb = Vb := orbSup_eq_of_stab fun s hs => hle hs
    rw [h.gen] at h1
    exact h.lt.ne h1.symm
  obtain ⟨t, ht, htV⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hidx2 : ((Tb ⊓ stabSub Vb).subgroupOf Tb).index = 2 := by
    have h0 : ((Tb ⊓ stabSub Vb).subgroupOf Tb).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : ((Tb ⊓ stabSub Vb).subgroupOf Tb).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      apply htV
      have : (⟨t, ht⟩ : Tb) ∈ (Tb ⊓ stabSub Vb).subgroupOf Tb := h1 ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    have h2 : ((Tb ⊓ stabSub Vb).subgroupOf Tb).index ≤ 2 := hidx
    omega
  have hnorm : ((Tb ⊓ stabSub Vb).subgroupOf Tb).Normal := Subgroup.normal_of_index_eq_two hidx2
  have hconj : ∀ a ∈ Tb ⊓ stabSub Vb, t⁻¹ * a * t ∈ Tb ⊓ stabSub Vb := by
    intro a haN
    have hmem : (⟨a, haN.1⟩ : Tb) ∈ (Tb ⊓ stabSub Vb).subgroupOf Tb :=
      Subgroup.mem_subgroupOf.mpr haN
    have := hnorm.conj_mem _ hmem (⟨t, ht⟩ : Tb)⁻¹
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hcos : ∀ s ∈ Tb, s ∈ stabSub Vb ∨ t⁻¹ * s ∈ stabSub Vb := by
    intro s hs
    by_cases hsV : s ∈ stabSub Vb
    · exact Or.inl hsV
    · right
      have h1 : (⟨t, ht⟩ : Tb)⁻¹ ∉ (Tb ⊓ stabSub Vb).subgroupOf Tb := fun hm => htV (by
        have := (Subgroup.mem_subgroupOf.mp hm).2
        simpa using (stabSub Vb).inv_mem this)
      have h2 : (⟨s, hs⟩ : Tb) ∉ (Tb ⊓ stabSub Vb).subgroupOf Tb := fun hm =>
        hsV (Subgroup.mem_subgroupOf.mp hm).2
      have key := (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false h1 h2)
      have := (Subgroup.mem_subgroupOf.mp key).2
      simpa using this
  have hAV₂ : A ≤ stabSub (Vb.map t.toMonoidHom) := fun a ha =>
    n8_mem_stabSub_map.mpr (hconj a ⟨hAT ha, hAV ha⟩).2
  have hmap1 : Vb.map (1 : MulAut X).toMonoidHom = Vb := by
    ext v
    simp
  have hsup : Vb ⊔ Vb.map t.toMonoidHom = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h.gen]
    refine orbSup_le fun s hs => ?_
    rcases hcos s hs with hsV | hsV
    · rw [mem_stabSub_iff_map_eq.mp hsV]
      exact le_sup_left
    · have e : Vb.map s.toMonoidHom = Vb.map t.toMonoidHom := by
        rw [← mul_inv_cancel_left t s, map_mul_aut', mem_stabSub_iff_map_eq.mp hsV]
      rw [e]
      exact le_sup_right
  have hinf : Vb ⊓ Vb.map t.toMonoidHom = ⊥ := by
    have h1 : Vb ∈ {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} :=
      ⟨1, Tb.one_mem, hmap1.symm⟩
    have h2 : Vb.map t.toMonoidHom ∈ {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} :=
      ⟨t, ht, rfl⟩
    have hne : Vb ≠ Vb.map t.toMonoidHom := fun he => htV (mem_stabSub_iff_map_eq.mpr he.symm)
    exact disjoint_iff.mp (h.indep.pairwiseDisjoint h1 h2 hne)
  have hf₁ : A ⊓ centSub Vb = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
    refine hfaith 1 Tb.one_mem a ha.1 fun w hw => ?_
    rw [hmap1, orbSup_eq_of_stab fun b hb => hAV hb] at hw
    exact ha.2 w hw
  have hf₂ : A ⊓ centSub (Vb.map t.toMonoidHom) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
    refine hfaith t ht a ha.1 fun w hw => ?_
    rw [orbSup_eq_of_stab fun b hb => hAV₂ hb] at hw
    exact ha.2 w hw
  have hq₁ : qOf (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) = ((1 : ℚ) : WithTop ℚ) := by
    obtain ⟨A₀, h8 | h11⟩ := hcase
    · exact h8.2.2.1
    · exact h11.2.2.2.1
  have hns₁ : ¬ IsStrongFFModule (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) :=
    not_isStrongFFModule_of_one_le_qOf (B1.sq_eq_one_sub h.exp Vb) (by rw [hq₁, WithTop.coe_one])
  have hLt : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb := by
    intro l hl
    have hn := le_normalizer_conjClosure Lb Tb (Tb.inv_mem ht)
    rw [← h.Mp_eq, hML] at hn
    have := (Subgroup.mem_normalizer_iff.mp hn l).mp hl
    simpa using this
  have hD₂ : Lb ⊔ (Tb ⊓ stabSub (Vb.map t.toMonoidHom)) ≤
      conjAutSub t (Lb ⊔ (Tb ⊓ stabSub Vb)) := by
    have hmem : ∀ x, t⁻¹ * x * t ∈ Lb ⊔ (Tb ⊓ stabSub Vb) →
        x ∈ conjAutSub t (Lb ⊔ (Tb ⊓ stabSub Vb)) := fun x hx =>
      ⟨t⁻¹ * x * t, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine sup_le (fun l hl => hmem l (le_sup_left (a := Lb) (hLt l hl)))
      (fun x hx => hmem x (le_sup_right (a := Lb) ⟨?_, ?_⟩))
    · exact Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) hx.1) ht
    · exact n8_mem_stabSub_map.mp hx.2
  have hns₂ := n8_not_isStrongFFModule_conj t hD₂ hns₁
  obtain ⟨r, -, hr2, ⟨⟨hA2, hAr⟩, -⟩, -⟩ := QhatStar_spec hAQ
  have hrk : rkIdx (fixV A) ≤ 2 * rk A := by
    have h2 : (rkIdx (fixV A) : ℚ) ≤ 2 * rk A := by
      rw [← hA2.rAV_mul, hAr]
      exact mul_le_mul_of_nonneg_right hr2 (by positivity)
    exact_mod_cast h2
  obtain ⟨hoff₁, hoff₂⟩ := n8_isFFStarOffender_pair h.exp hsup hinf hAV hAV₂ hf₁ hf₂
    ⟨le_sup_of_le_right (le_inf hAT hAV), hA2.2.1, hA2.2.2⟩
    ⟨le_sup_of_le_right (le_inf hAT hAV₂), hA2.2.1, hA2.2.2⟩ hrk hns₁ hns₂
  exact i3 X Mb Tb Lb Vb A t h hML ht htV (le_inf hAT hAV) hAV₂ hcase hoff₁ hoff₂

end Final

end CFSG.Quasithin
