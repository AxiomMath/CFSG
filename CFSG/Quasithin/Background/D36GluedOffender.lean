module

public import CFSG.Quasithin.Background.D36GluedShape
import CFSG.Quasithin.Background.F918V5A

public section

namespace CFSG.Quasithin

section Abstract

variable {Y : Type} [CommGroup Y] [Finite Y]

structure GluedSwap (X A : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop where
  pair : GluedPair X U U'
  ne : U ≠ U'
  gap : rk ↥(U ⊓ U') + 2 < rk ↥U
  mem : A ∈ QhatStar X
  swaps : ¬ A ≤ stabSub U

theorem triple_comm_eq_one {A : Subgroup (MulAut Y)} (h3 : commSeries A 3 = ⊥)
    {g₁ g₂ g₃ : MulAut Y} (h₁ : g₁ ∈ A) (h₂ : g₂ ∈ A) (h₃ : g₃ ∈ A) (y : Y) :
    g₃ (g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹) = g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹ := by
  have e1 : g₁ y * y⁻¹ ∈ commSeries A 1 :=
    Subgroup.subset_closure ⟨g₁, h₁, y, Subgroup.mem_top y, rfl⟩
  have e2 : g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹ ∈ commSeries A 2 :=
    Subgroup.subset_closure ⟨g₂, h₂, _, e1, rfl⟩
  have e3 : g₃ (g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹) *
      (g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹)⁻¹ ∈ commSeries A 3 :=
    Subgroup.subset_closure ⟨g₃, h₃, _, e2, rfl⟩
  rw [h3, Subgroup.mem_bot, mul_inv_eq_one] at e3
  exact e3

theorem commSeries_three_eq_bot_of_forall {R : Subgroup (MulAut Y)}
    (h : ∀ g₁ ∈ R, ∀ g₂ ∈ R, ∀ g₃ ∈ R, ∀ y : Y,
      g₃ (g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹) = g₂ (g₁ y * y⁻¹) * (g₁ y * y⁻¹)⁻¹) :
    commSeries R 3 = ⊥ := by
  have e3 : commSeries R 3 = commSub (commSeries R 2) R := rfl
  have e2 : commSeries R 2 = commSub (commSeries R 1) R := rfl
  have e1 : commSeries R 1 = commSub ⊤ R := rfl
  rw [e3, commSub_eq_bot_iff, e2, commSub, Subgroup.closure_le]
  rintro _ ⟨g₂, hg₂, x, hx, rfl⟩ g₃ hg₃
  rw [e1] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g₁, hg₁, y, -, rfl⟩ := hz
    exact h g₁ hg₁ g₂ hg₂ g₃ hg₃ y
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g₂ (a * b) * (a * b)⁻¹ = (g₂ a * a⁻¹) * (g₂ b * b⁻¹) := by
      rw [map_mul]
      simp only [mul_inv_rev]
      ac_rfl
    rw [e, map_mul, ha, hb]
  | inv a _ ha =>
    have e : g₂ a⁻¹ * (a⁻¹)⁻¹ = (g₂ a * a⁻¹)⁻¹ := by
      rw [map_inv]
      simp only [inv_inv, mul_inv_rev]
      ac_rfl
    rw [e, map_inv, ha]

theorem mulAut_eq_of_eqOn_sup {U U' : Subgroup Y} (hsup : U ⊔ U' = ⊤) {g h : MulAut Y}
    (h1 : ∀ u ∈ U, g u = h u) (h2 : ∀ u ∈ U', g u = h u) : g = h := by
  ext y
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top y)
  rw [map_mul, map_mul, h1 u hu, h2 u' hu']

namespace GluedSwap

variable {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}

theorem le_X (h : GluedSwap X A U U') : A ≤ X := by
  obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec h.mem
  exact hAk.1.1.1

theorem isPGroup (h : GluedSwap X A U U') : IsPGroup 2 A :=
  D36.isPGroup_of_mem_QhatStar h.mem

theorem cubic (h : GluedSwap X A U U') : commSeries A 3 = ⊥ := by
  obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec h.mem
  exact hAk.2

theorem quad (h : GluedSwap X A U U') {b₁ b₂ : MulAut Y} (hb₁ : b₁ ∈ A ⊓ stabSub U)
    (hb₂ : b₂ ∈ A ⊓ stabSub U) {u : Y} (hu : u ∈ U) :
    b₂ (b₁ u * u⁻¹) * (b₁ u * u⁻¹)⁻¹ ∈ U ⊓ U' := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  have hc : ∀ g ∈ A ⊓ stabSub U, ∀ y, g (a y) = a (g y) := fun g hg y => by
    have := congrArg (fun φ : MulAut Y => φ y) (hcomm g hg)
    simpa [MulAut.mul_apply] using this
  have hε : ∀ g ∈ A ⊓ stabSub U, ∀ y,
      g (a y * y⁻¹) * (a y * y⁻¹)⁻¹ = a (g y * y⁻¹) * (g y * y⁻¹)⁻¹ := by
    intro g hg y
    rw [map_mul, map_inv, hc g hg y]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    ac_rfl
  have fa1 : ∀ x, a x ∈ U' ↔ x ∈ U := fun x => by
    rw [← ha1]; exact apply_mem_map_iffQ1 a x
  have key := triple_comm_eq_one h.cubic haA hb₁.1 hb₂.1 u
  have e1 := hε b₁ hb₁ u
  rw [e1] at key
  have e2 := hε b₂ hb₂ (b₁ u * u⁻¹)
  rw [key, mul_inv_cancel] at e2
  have hv₁ : b₁ u * u⁻¹ ∈ U := U.mul_mem ((hb₁.2 u).mpr hu) (U.inv_mem hu)
  have hv₂ : b₂ (b₁ u * u⁻¹) * (b₁ u * u⁻¹)⁻¹ ∈ U :=
    U.mul_mem ((hb₂.2 _).mpr hv₁) (U.inv_mem hv₁)
  refine ⟨hv₂, ?_⟩
  have hfix : a (b₂ (b₁ u * u⁻¹) * (b₁ u * u⁻¹)⁻¹) = b₂ (b₁ u * u⁻¹) * (b₁ u * u⁻¹)⁻¹ :=
    (mul_inv_eq_one.mp e2.symm)
  have := (fa1 _).mpr hv₂
  rwa [hfix] at this

theorem faithful_mod (h : GluedSwap X A U U') {b : MulAut Y} (hb : b ∈ A ⊓ stabSub U)
    (hbU : ∀ u ∈ U, b u * u⁻¹ ∈ U ⊓ U') : b = 1 := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  have fa1 : ∀ x, a x ∈ U' ↔ x ∈ U := fun x => by
    rw [← ha1]; exact apply_mem_map_iffQ1 a x
  have haax : ∀ x, a (a x) = x := fun x => by
    have := congrArg (fun φ : MulAut Y => φ x) haa
    simpa [MulAut.mul_apply] using this
  have fa2 : ∀ x, a x ∈ U ↔ x ∈ U' := fun x => by
    have := fa1 (a x)
    rw [haax x] at this
    exact this.symm
  have hDa : ∀ d ∈ U ⊓ U', a d ∈ U ⊓ U' := fun d hd => ⟨(fa2 d).mpr hd.2, (fa1 d).mpr hd.1⟩
  refine h.pair.faithful b (h.le_X hb.1) fun y => ?_
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (h.pair.sup_eq ▸ Subgroup.mem_top y)
  have e : b (u * u') * (u * u')⁻¹ = (b u * u⁻¹) * (b u' * u'⁻¹) := by
    rw [map_mul, mul_inv_rev, mul_comm u'⁻¹ u⁻¹]
    exact mul_mul_mul_comm _ _ _ _
  rw [e]
  refine (U ⊓ U').mul_mem (hbU u hu) ?_
  obtain ⟨w, hw, hwu⟩ : u' ∈ U.map a.toMonoidHom := ha1 ▸ hu'
  have hwu' : a w = u' := hwu
  subst hwu'
  have hc : b (a w) = a (b w) := by
    have := congrArg (fun φ : MulAut Y => φ w) (hcomm b hb)
    simpa [MulAut.mul_apply] using this
  have : b (a w) * (a w)⁻¹ = a (b w * w⁻¹) := by rw [hc, map_mul, map_inv]
  rw [this]
  exact hDa _ (hbU w hw)

theorem lt_commModSub (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    rk ↥(U ⊓ U') < rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  have hBP : IsPGroup 2 ↥(A ⊓ stabSub U) := h.isPGroup.to_le inf_le_left
  have hBU : ∀ p ∈ A ⊓ stabSub U, ∀ x ∈ U, p • x ∈ U := fun p hp x hx => (hp.2 x).mpr hx
  have hBU' : ∀ p ∈ A ⊓ stabSub U, ∀ x ∈ U', p • x ∈ U' := by
    intro p hp x hx
    have hx' : x ∈ U.map a.toMonoidHom := ha1 ▸ hx
    have := map_mem_map_of_comm (hcomm p hp) (fun u hu => (hp.2 u).mpr hu) x hx'
    rwa [ha1] at this
  have hBD : ∀ p ∈ A ⊓ stabSub U, ∀ x ∈ U ⊓ U', p • x ∈ U ⊓ U' := fun p hp x hx =>
    ⟨hBU p hp x hx.1, hBU' p hp x hx.2⟩
  have hne : U ⊓ U' ≠ U := by
    intro heq
    have := h.gap
    rw [heq] at this
    omega
  obtain ⟨x, hxU, hxD, hx⟩ := core3_exists_fixed_coset_sub hY hBP hBU hBD inf_le_left hne
  have hxÛ : x ∈ commModSub U (A ⊓ stabSub U) (U ⊓ U') := ⟨hxU, fun g hg => hx g hg⟩
  have hDÛ : U ⊓ U' ≤ commModSub U (A ⊓ stabSub U) (U ⊓ U') := fun d hd =>
    ⟨hd.1, fun g hg => (U ⊓ U').mul_mem (hBD g hg d hd) ((U ⊓ U').inv_mem hd)⟩
  by_contra hcon
  push Not at hcon
  exact hxD (eq_of_le_of_rk_le hY hDÛ hcon ▸ hxÛ)

theorem offender (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    rk ↥U ≤ rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) + rk ↥(A ⊓ stabSub U) := by
  obtain ⟨-, hb, -⟩ := glued_swap_shape h.pair h.ne h.gap h.mem h.swaps
  have h1 := h.lt_commModSub hY
  have h2 : rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) ≤ rk ↥(U ⊓ U') := rk_mono inf_le_left
  omega

theorem ne_bot (h : GluedSwap X A U U') : A ⊓ stabSub U ≠ ⊥ :=
  (glued_swap_shape h.pair h.ne h.gap h.mem h.swaps).1

theorem rkIdx_fixV_ge (h : GluedSwap X A U U') :
    2 * rk ↥U ≤ rkIdx (fixV A) + rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) +
      rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  have hstab : A ⊓ stabSub U ≤ stabSub U := inf_le_right
  have hsum' : U ⊔ U.map a.toMonoidHom = ⊤ := by rw [ha1]; exact h.pair.sup_eq
  have hDeq : U ⊓ U.map a.toMonoidHom = U ⊓ U' := by rw [ha1]
  have hFeq : fixV A = fixV (A ⊓ stabSub U) ⊓ fixV (Subgroup.zpowers a) := by
    rw [← fixV_sup_eq_inf_fixV, ← hAeq]
  have h1 := rk_fixV_swap_le haa hcomm hstab hsum'
  have h2 := rk_sup_swap_add_rk_inf hsum'
  rw [hDeq] at h1 h2
  have h4 := rk_add_rkIdx (fixV A)
  have hrk : rk ↥(fixV A) = rk ↥(fixV (A ⊓ stabSub U) ⊓ fixV (Subgroup.zpowers a)) := by
    rw [hFeq]
  omega

theorem rAV_le (h : GluedSwap X A U U') {R : Subgroup (MulAut Y)} (hR : IsA2 X R)
    (hR3 : commSeries R 3 = ⊥) : rAV A ≤ rAV R := by
  obtain ⟨r, hr, -, hAk, -⟩ := QhatStar_spec h.mem
  have h1 : (r : WithTop ℚ) ≤ kq X 3 := hr.ge
  rw [hAk.1.2]
  exact le_kq_iff.mp h1 R hR hR3

end GluedSwap

@[expose] def glueDiagSub (L₀ A : Subgroup (MulAut Y)) (U : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {l | l ∈ L₀ ∧ ∃ b ∈ A ⊓ stabSub U, ∀ u ∈ U, b u = l u}
  one_mem' := ⟨L₀.one_mem, 1, (A ⊓ stabSub U).one_mem, fun u _ => rfl⟩
  mul_mem' := by
    rintro l₁ l₂ ⟨hl₁, b₁, hb₁, h₁⟩ ⟨hl₂, b₂, hb₂, h₂⟩
    refine ⟨L₀.mul_mem hl₁ hl₂, b₁ * b₂, (A ⊓ stabSub U).mul_mem hb₁ hb₂, fun u hu => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, ← h₂ u hu]
    exact h₁ _ ((hb₂.2 u).mpr hu)
  inv_mem' := by
    rintro l ⟨hl, b, hb, h⟩
    refine ⟨L₀.inv_mem hl, b⁻¹, (A ⊓ stabSub U).inv_mem hb, fun u hu => ?_⟩
    have hw : b⁻¹ u ∈ U := ((stabSub U).inv_mem hb.2 u).mpr hu
    have h1 : l (b⁻¹ u) = u := by rw [← h _ hw]; simp [MulAut.mul_apply]
    calc b⁻¹ u = l⁻¹ (l (b⁻¹ u)) := by simp [MulAut.mul_apply]
      _ = l⁻¹ u := by rw [h1]

theorem glueDiagSub_le {L₀ A : Subgroup (MulAut Y)} {U : Subgroup Y} : glueDiagSub L₀ A U ≤ L₀ :=
  fun _ hl => hl.1

namespace GluedSwap

variable {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}

theorem commModSub_lt (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) < rk ↥U := by
  by_contra hcon
  push Not at hcon
  have heq : commModSub U (A ⊓ stabSub U) (U ⊓ U') = U :=
    eq_of_le_of_rk_le hY (commModSub_le _ _ _) hcon
  apply h.ne_bot
  rw [eq_bot_iff]
  intro b hb
  have hb1 : b = 1 := by
    refine h.faithful_mod hb fun u hu => ?_
    have : u ∈ commModSub U (A ⊓ stabSub U) (U ⊓ U') := by rw [heq]; exact hu
    exact this.2 b hb
  rw [hb1]
  exact Subgroup.one_mem _

variable {L₀ : Subgroup (MulAut Y)}

theorem diag_comm (h : GluedSwap X A U U') (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    {l₁ l₂ : MulAut Y} (h₁ : l₁ ∈ glueDiagSub L₀ A U) (h₂ : l₂ ∈ glueDiagSub L₀ A U) :
    l₁ * l₂ = l₂ * l₁ := by
  obtain ⟨hl₁, b₁, hb₁, e₁⟩ := h₁
  obtain ⟨hl₂, b₂, hb₂, e₂⟩ := h₂
  have hel : IsElemAbelian2 A := by
    obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec h.mem
    exact hAk.1.1.2.2
  refine mulAut_eq_of_eqOn_sup h.pair.sup_eq (fun u hu => ?_) (fun u hu => ?_)
  · rw [MulAut.mul_apply, MulAut.mul_apply, ← e₂ u hu, ← e₁ u hu, ← e₁ _ ((hb₂.2 u).mpr hu),
      ← e₂ _ ((hb₁.2 u).mpr hu)]
    have := hel.1 b₁ hb₁.1 b₂ hb₂.1
    exact congrArg (fun φ : MulAut Y => φ u) this
  · simp only [MulAut.mul_apply, hL₀ l₂ hl₂ u hu, hL₀ l₁ hl₁ u hu]

theorem diag_sq (h : GluedSwap X A U U') (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    {l : MulAut Y} (hl : l ∈ glueDiagSub L₀ A U) : l ^ 2 = 1 := by
  obtain ⟨hlL, b, hb, e⟩ := hl
  have hel : IsElemAbelian2 A := by
    obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec h.mem
    exact hAk.1.1.2.2
  have hbb : b * b = 1 := by simpa [pow_two] using hel.2 b hb.1
  rw [pow_two]
  refine mulAut_eq_of_eqOn_sup h.pair.sup_eq (fun u hu => ?_) (fun u hu => ?_)
  · rw [MulAut.mul_apply, ← e u hu, ← e _ ((hb.2 u).mpr hu)]
    have := congrArg (fun φ : MulAut Y => φ u) hbb
    simpa [MulAut.mul_apply] using this
  · simp only [MulAut.mul_apply, hL₀ l hlL u hu, MulAut.one_apply]

theorem diag_ne_bot (h : GluedSwap X A U U')
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) : glueDiagSub L₀ A U ≠ ⊥ := by
  intro hbot
  apply h.ne_bot
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨l, hlL, hl⟩ := hdiag b hb
  have hlR : l ∈ glueDiagSub L₀ A U := ⟨hlL, b, hb, hl⟩
  rw [hbot, Subgroup.mem_bot] at hlR
  have hb1 : b = 1 := h.faithful_mod hb fun u hu => by
    rw [hl u hu, hlR]
    simp
  rw [hb1]
  exact Subgroup.one_mem _

theorem shape_B (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) :
    1 ≤ rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ∧
    rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥(A ⊓ stabSub U) ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤
      2 * rk ↥(A ⊓ stabSub U) + 2 := by
  obtain ⟨-, hb, -⟩ := glued_swap_shape h.pair h.ne h.gap h.mem h.swaps
  have h1 := h.lt_commModSub hY
  have h2 := h.commModSub_lt hY
  have h3 := h.offender hY
  have h4 : rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) ≤ rk ↥(U ⊓ U') := rk_mono inf_le_left
  refine ⟨by omega, by omega, by omega⟩

theorem rk_le_diagSub (h : GluedSwap X A U U')
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hRel : IsElemAbelian2 (glueDiagSub L₀ A U)) :
    rk ↥(A ⊓ stabSub U) ≤ rk ↥(glueDiagSub L₀ A U) := by
  classical
  choose! φ hφ1 hφ2 using hdiag
  let f : ↥(A ⊓ stabSub U) → ↥(glueDiagSub L₀ A U) :=
    fun b => ⟨φ b, hφ1 b b.2, b, b.2, hφ2 b b.2⟩
  have hinj : Function.Injective f := by
    intro b b' hbb
    have hφeq : φ b = φ b' := congrArg (fun x : ↥(glueDiagSub L₀ A U) => (x : MulAut Y)) hbb
    have hmem : (b : MulAut Y)⁻¹ * b' ∈ A ⊓ stabSub U :=
      (A ⊓ stabSub U).mul_mem ((A ⊓ stabSub U).inv_mem b.2) b'.2
    have h1' : (b : MulAut Y)⁻¹ * b' = 1 := by
      refine h.faithful_mod hmem fun u hu => ?_
      have hbu : (b : MulAut Y) u = (b' : MulAut Y) u := by
        rw [hφ2 b b.2 u hu, hφ2 b' b'.2 u hu, hφeq]
      have : ((b : MulAut Y)⁻¹ * b') u = u := by
        rw [MulAut.mul_apply, ← hbu]
        simp [MulAut.mul_apply]
      rw [this, mul_inv_cancel]
      exact (U ⊓ U').one_mem
    exact Subtype.ext (inv_mul_eq_one.mp h1')
  have hcard := Nat.card_le_card_of_injective f hinj
  have hBP : IsPGroup 2 ↥(A ⊓ stabSub U) := h.isPGroup.to_le inf_le_left
  rw [card_eq_two_pow_of_isPGroup hBP, card_eq_two_pow_of_isPGroup hRel.isPGroup] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard

theorem diag_isElemAbelian2 (h : GluedSwap X A U U') (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) :
    IsElemAbelian2 (glueDiagSub L₀ A U) :=
  ⟨fun _ h₁ _ h₂ => h.diag_comm hL₀ hdiag h₁ h₂, fun _ hl => h.diag_sq hL₀ hl⟩

theorem diag_arith {u uh d g k k₀ N I₀ : ℕ} (hd1 : d ≤ g) (hg : g ≤ uh) (hdu : d < uh)
    (huh : uh < u) (hk : 0 < k) (hkk : k ≤ k₀) (hlow : 2 * u ≤ N + d + uh)
    (hN : N ≤ 2 * (k + 1)) (hI : I₀ + g ≤ u) (hcmp : N * k₀ ≤ I₀ * (k + 1)) :
    k * (u - uh) + (k + 1) * (g - d) ≤ u - d ∧ (u - uh) + (u - d) ≤ 2 * k + 2 ∧
      (u - uh) + (g - d) ≤ 2 ∧ g < uh := by
  obtain ⟨s, hs⟩ : ∃ s, u = uh + s := ⟨u - uh, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, uh = d + c := ⟨uh - d, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f, g = d + f := ⟨g - d, by omega⟩
  have e1 : u - uh = s := by omega
  have e2 : g - d = f := by omega
  have e3 : u - d = s + c := by omega
  rw [e1, e2, e3]
  have hNge : 2 * s + c ≤ N := by omega
  have hI' : I₀ + f ≤ c + s := by omega
  have hk0 : k * N ≤ N * k₀ := (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ hkk)
  have hmain : k * (2 * s + c) ≤ I₀ * (k + 1) :=
    (Nat.mul_le_mul_left _ hNge).trans (hk0.trans hcmp)
  have hprod : (k + 1) * (I₀ + f) ≤ (k + 1) * (c + s) := Nat.mul_le_mul_left _ hI'
  have hA : k * s + (k + 1) * f ≤ s + c := by nlinarith [hmain, hprod]
  have hB : s + (s + c) ≤ 2 * k + 2 := by omega
  have hC : s + f ≤ 2 := by
    have : (k + 1) * (s + f) ≤ (k + 1) * 2 := by nlinarith [hA, hB]
    exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos k)
  have hs1 : 1 ≤ s := by omega
  have hc1 : 1 ≤ c := by omega
  refine ⟨hA, hB, hC, ?_⟩
  have : f < c := by nlinarith [hA]
  omega

theorem diag_bound (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀X : L₀ ≤ X) (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) :
    rk ↥(U ⊓ U') ≤ rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) ∧
    rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) ≤ rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ∧
    rk ↥(A ⊓ stabSub U) * (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
      (rk ↥(A ⊓ stabSub U) + 1) *
        (rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) - rk ↥(U ⊓ U')) ≤ rk ↥U - rk ↥(U ⊓ U') ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤
      2 * rk ↥(A ⊓ stabSub U) + 2 ∧
    (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
      (rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) - rk ↥(U ⊓ U')) ≤ 2 ∧
    rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) < rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  obtain ⟨r, hr, hr2, hAk, hmin⟩ := QhatStar_spec h.mem
  have hA2 : IsA2 X A := hAk.1.1
  have hAr : rAV A = r := hAk.1.2
  have hDU : U ⊓ U' ≤ U := inf_le_left
  have hDU' : U ⊓ U' ≤ U' := inf_le_right
  have hRfixU' : U' ≤ fixV (glueDiagSub L₀ A U) := fun u hu ρ hρ => hL₀ ρ (glueDiagSub_le hρ) u hu
  have hDfixR : U ⊓ U' ≤ fixV (glueDiagSub L₀ A U) := hDU'.trans hRfixU'
  have h1 : U ⊓ U' ≤ U ⊓ fixV (glueDiagSub L₀ A U) := le_inf hDU hDfixR
  have h2 : U ⊓ fixV (glueDiagSub L₀ A U) ≤ commModSub U (A ⊓ stabSub U) (U ⊓ U') := by
    intro x hx
    refine ⟨hx.1, fun g hg => ?_⟩
    obtain ⟨l, hlL, hl⟩ := hdiag g hg
    have hlR : l ∈ glueDiagSub L₀ A U := ⟨hlL, g, hg, hl⟩
    have hgx : g x = x := by rw [hl x hx.1]; exact hx.2 l hlR
    rw [hgx, mul_inv_cancel]
    exact (U ⊓ U').one_mem
  have hrk1 := rk_mono h1
  have hrk2 := rk_mono h2
  have hlt1 := h.lt_commModSub hY
  have hlt2 := h.commModSub_lt hY
  have hDB : U ⊓ U' ≤ fixV (A ⊓ stabSub U) := by
    intro d hd b hb
    obtain ⟨l, hlL, hl⟩ := hdiag b hb
    rw [hl d hd.1]
    exact (hDfixR hd) l ⟨hlL, b, hb, hl⟩
  have hĉ : rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) = rk ↥(U ⊓ U') := by
    rw [inf_eq_left.mpr hDB]
  have hRel : IsElemAbelian2 (glueDiagSub L₀ A U) :=
    ⟨fun l₁ h₁ l₂ h₂ => h.diag_comm hL₀ hdiag h₁ h₂, fun l hl => h.diag_sq hL₀ hl⟩
  have hBne : A ⊓ stabSub U ≠ ⊥ := h.ne_bot
  have hRne : glueDiagSub L₀ A U ≠ ⊥ := by
    intro hbot
    apply hBne
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨l, hlL, hl⟩ := hdiag b hb
    have hlR : l ∈ glueDiagSub L₀ A U := ⟨hlL, b, hb, hl⟩
    rw [hbot, Subgroup.mem_bot] at hlR
    have hb1 : b = 1 := h.faithful_mod hb fun u hu => by
      rw [hl u hu, hlR]
      simp
    rw [hb1]
    exact Subgroup.one_mem _
  have hR2 : IsA2 X (glueDiagSub L₀ A U) := ⟨glueDiagSub_le.trans hL₀X, hRne, hRel⟩
  have hR3 : commSeries (glueDiagSub L₀ A U) 3 = ⊥ := by
    refine commSeries_three_eq_bot_of_forall fun ρ₁ h₁ ρ₂ h₂ ρ₃ h₃ y => ?_
    obtain ⟨hρ₁, b₁, hb₁, e₁⟩ := h₁
    obtain ⟨hρ₂, b₂, hb₂, e₂⟩ := h₂
    obtain ⟨hρ₃, b₃, hb₃, e₃⟩ := h₃
    obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (h.pair.sup_eq ▸ Subgroup.mem_top y)
    have hx₁ : ρ₁ (u * u') * (u * u')⁻¹ = b₁ u * u⁻¹ := by
      rw [map_mul, hL₀ ρ₁ hρ₁ u' hu', ← e₁ u hu]
      group
    have hv₁ : b₁ u * u⁻¹ ∈ U := U.mul_mem ((hb₁.2 u).mpr hu) (U.inv_mem hu)
    rw [hx₁, ← e₂ _ hv₁]
    exact hL₀ ρ₃ hρ₃ _ (h.quad hb₁ hb₂ hu).2
  have hBR : rk ↥(A ⊓ stabSub U) ≤ rk ↥(glueDiagSub L₀ A U) := by
    classical
    choose! φ hφ1 hφ2 using hdiag
    let f : ↥(A ⊓ stabSub U) → ↥(glueDiagSub L₀ A U) :=
      fun b => ⟨φ b, hφ1 b b.2, b, b.2, hφ2 b b.2⟩
    have hinj : Function.Injective f := by
      intro b b' hbb
      have hφeq : φ b = φ b' := congrArg (fun x : ↥(glueDiagSub L₀ A U) => (x : MulAut Y)) hbb
      have hmem : (b : MulAut Y)⁻¹ * b' ∈ A ⊓ stabSub U :=
        (A ⊓ stabSub U).mul_mem ((A ⊓ stabSub U).inv_mem b.2) b'.2
      have h1' : (b : MulAut Y)⁻¹ * b' = 1 := by
        refine h.faithful_mod hmem fun u hu => ?_
        have hbu : (b : MulAut Y) u = (b' : MulAut Y) u := by
          rw [hφ2 b b.2 u hu, hφ2 b' b'.2 u hu, hφeq]
        have : ((b : MulAut Y)⁻¹ * b') u = u := by
          rw [MulAut.mul_apply, ← hbu]
          simp [MulAut.mul_apply]
        rw [this, mul_inv_cancel]
        exact (U ⊓ U').one_mem
      exact Subtype.ext (inv_mul_eq_one.mp h1')
    have hcard := Nat.card_le_card_of_injective f hinj
    have hBP : IsPGroup 2 ↥(A ⊓ stabSub U) := h.isPGroup.to_le inf_le_left
    rw [card_eq_two_pow_of_isPGroup hBP, card_eq_two_pow_of_isPGroup hRel.isPGroup] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hZ : (U ⊓ fixV (glueDiagSub L₀ A U)) ⊔ U' ≤ fixV (glueDiagSub L₀ A U) :=
    sup_le inf_le_right hRfixU'
  have hI0 := rkIdx_anti hZ
  have hZ' : (U ⊓ fixV (glueDiagSub L₀ A U)) ⊓ U' = U ⊓ U' := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2⟩
    · exact fun x hx => ⟨⟨hx.1, hDfixR hx⟩, hx.2⟩
  have hs1 := rk_sup_add_rk_inf (U ⊓ fixV (glueDiagSub L₀ A U)) U'
  rw [hZ'] at hs1
  obtain ⟨s₀, hs₀X, hs₀1, -⟩ := h.pair.swap
  have hrkU' : rk ↥U' = rk ↥U := by rw [← hs₀1]; exact rk_map_aut_eq U s₀
  have hs2 := rk_sup_add_rk_inf U U'
  rw [h.pair.sup_eq, rk_top, hrkU'] at hs2
  have hs3 := rk_add_rkIdx ((U ⊓ fixV (glueDiagSub L₀ A U)) ⊔ U')
  have hI : rkIdx (fixV (glueDiagSub L₀ A U)) + rk ↥(U ⊓ fixV (glueDiagSub L₀ A U)) ≤ rk ↥U := by
    omega
  have hlow := h.rkIdx_fixV_ge
  rw [hĉ] at hlow
  have hN2 : rkIdx (fixV A) ≤ 2 * (rk ↥(A ⊓ stabSub U) + 1) := by
    have h1' := hA2.rAV_mul
    have h2' : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
      rw [← h1', hAr]
      exact mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg _)
    have h3' : rkIdx (fixV A) ≤ 2 * rk ↥A := by exact_mod_cast h2'
    rw [hrkA] at h3'
    exact h3'
  have hAk' : 0 < rk ↥A := hA2.rk_pos
  have hRk' : 0 < rk ↥(glueDiagSub L₀ A U) := hR2.rk_pos
  have hcmp : rkIdx (fixV A) * rk ↥(glueDiagSub L₀ A U) ≤
      rkIdx (fixV (glueDiagSub L₀ A U)) * (rk ↥(A ⊓ stabSub U) + 1) := by
    have := h.rAV_le hR2 hR3
    unfold rAV at this
    rw [div_le_div_iff₀ (by exact_mod_cast hAk') (by exact_mod_cast hRk')] at this
    have h3 : rkIdx (fixV A) * rk ↥(glueDiagSub L₀ A U) ≤
        rkIdx (fixV (glueDiagSub L₀ A U)) * rk ↥A := by exact_mod_cast this
    rw [hrkA] at h3
    exact h3
  have hBpos : 0 < rk ↥(A ⊓ stabSub U) := (hA2.mono inf_le_left hBne).rk_pos
  obtain ⟨hA, hB, hC, hD⟩ := diag_arith hrk1 hrk2 hlt1 hlt2 hBpos hBR hlow hN2 hI hcmp
  exact ⟨hrk1, hrk2, hA, hB, hC, hD⟩

theorem compare_cubic (h : GluedSwap X A U U') {E : Subgroup (MulAut Y)} (hE : IsA2 X E)
    (hE3 : commSeries E 3 = ⊥) (hEU' : ∀ e ∈ E, ∀ u ∈ U', e u = u) :
    ((rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U'))) * rk ↥E ≤
      (rk ↥(A ⊓ stabSub U) + 1) * (rk ↥U - rk ↥(U ⊓ fixV E)) := by
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ :=
    glued_swap_decomp h.pair h.ne h.mem h.swaps
  have hA2 : IsA2 X A := by
    obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec h.mem
    exact hAk.1.1
  have hEfixU' : U' ≤ fixV E := fun u hu e he => hEU' e he u hu
  have hDfixE : U ⊓ U' ≤ fixV E := inf_le_right.trans hEfixU'
  have hZ : (U ⊓ fixV E) ⊔ U' ≤ fixV E := sup_le inf_le_right hEfixU'
  have hI0 := rkIdx_anti hZ
  have hZ' : (U ⊓ fixV E) ⊓ U' = U ⊓ U' := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2⟩
    · exact fun x hx => ⟨⟨hx.1, hDfixE hx⟩, hx.2⟩
  have hs1 := rk_sup_add_rk_inf (U ⊓ fixV E) U'
  rw [hZ'] at hs1
  obtain ⟨s₀, hs₀X, hs₀1, -⟩ := h.pair.swap
  have hrkU' : rk ↥U' = rk ↥U := by rw [← hs₀1]; exact rk_map_aut_eq U s₀
  have hs2 := rk_sup_add_rk_inf U U'
  rw [h.pair.sup_eq, rk_top, hrkU'] at hs2
  have hs3 := rk_add_rkIdx ((U ⊓ fixV E) ⊔ U')
  have hI : rkIdx (fixV E) + rk ↥(U ⊓ fixV E) ≤ rk ↥U := by omega
  have hlow := h.rkIdx_fixV_ge
  have hĉ : rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) ≤ rk ↥(U ⊓ U') := rk_mono inf_le_left
  have hAk' : 0 < rk ↥A := hA2.rk_pos
  have hEk' : 0 < rk ↥E := hE.rk_pos
  have hcmp : rkIdx (fixV A) * rk ↥E ≤ rkIdx (fixV E) * (rk ↥(A ⊓ stabSub U) + 1) := by
    have := h.rAV_le hE hE3
    unfold rAV at this
    rw [div_le_div_iff₀ (by exact_mod_cast hAk') (by exact_mod_cast hEk')] at this
    have h3 : rkIdx (fixV A) * rk ↥E ≤ rkIdx (fixV E) * rk ↥A := by exact_mod_cast this
    rw [hrkA] at h3
    exact h3
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (commModSub_le _ _ _)
  have hD : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
  have hres : (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤
      rkIdx (fixV A) := by omega
  calc ((rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U'))) *
        rk ↥E ≤ rkIdx (fixV A) * rk ↥E := Nat.mul_le_mul_right _ hres
    _ ≤ rkIdx (fixV E) * (rk ↥(A ⊓ stabSub U) + 1) := hcmp
    _ ≤ (rk ↥U - rk ↥(U ⊓ fixV E)) * (rk ↥(A ⊓ stabSub U) + 1) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (rk ↥(A ⊓ stabSub U) + 1) * (rk ↥U - rk ↥(U ⊓ fixV E)) := Nat.mul_comm _ _

theorem rk_le_of_cubic (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    {E : Subgroup (MulAut Y)} (hE : IsA2 X E) (hE3 : commSeries E 3 = ⊥)
    (hEU' : ∀ e ∈ E, ∀ u ∈ U', e u = u) : rk ↥E ≤ rk ↥(A ⊓ stabSub U) := by
  have h1 := h.compare_cubic hE hE3 hEU'
  obtain ⟨hs1, -, -⟩ := h.shape_B hY
  have hEfixU' : U' ≤ fixV E := fun u hu e he => hEU' e he u hu
  have hDfixE : U ⊓ U' ≤ fixV E := inf_le_right.trans hEfixU'
  have hg : rk ↥(U ⊓ U') ≤ rk ↥(U ⊓ fixV E) := rk_mono (le_inf inf_le_left hDfixE)
  by_contra hcon
  push Not at hcon
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (commModSub_le _ _ _)
  have hDU : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
  generalize hs : rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) = s at h1 hs1
  generalize hubar : rk ↥U - rk ↥(U ⊓ U') = ubar at h1
  generalize rk ↥(A ⊓ stabSub U) = k at h1 hcon
  generalize rk ↥E = e at h1 hcon
  have hle : rk ↥U - rk ↥(U ⊓ fixV E) ≤ ubar := by omega
  have h2 : (s + ubar) * e ≤ (k + 1) * ubar := h1.trans (Nat.mul_le_mul_left _ hle)
  have h3 : (s + ubar) * (k + 1) ≤ (s + ubar) * e := Nat.mul_le_mul_left _ hcon
  nlinarith

end GluedSwap

end Abstract

end CFSG.Quasithin
