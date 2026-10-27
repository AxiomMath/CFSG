module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModRefl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModFree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModSylA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2b

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

omit [Finite W] in
theorem mem_W₁_of_mem_A₁ {x : MulAut W} (hx : x ∈ S.A₁) {w : W} (hw : w ∈ S.W₁) : x w ∈ S.W₁ :=
  (six_module151b S.comm S.winf).1 x hx w hw

omit [Finite W] in
theorem fix_W₂_of_mem_A₁ {x : MulAut W} (hx : x ∈ S.A₁) {w : W} (hw : w ∈ S.W₂) : x w = w :=
  (six_module151b S.comm S.winf).2.2.1 x hx w hw

theorem exists_ne_one_fix_reflection₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {x₁ : MulAut W} (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) :
    ∃ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), z ≠ 1 := by
  by_contra hcon
  have hbot : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
  have h1 := Subgroup.card_eq_one.mpr hbot
  have h4 := S.card_fix_reflection₁ hW hcard hx₁ hx₁2
  omega

theorem eq_refl_of_inv (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {x₁ : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) {g : MulAut W}
    (hgfix : ∀ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), g z = z)
    (hinv : g * S.a₁ * g⁻¹ = S.a₁⁻¹) : ∀ w ∈ S.W₁, g w = x₁ w := by
  have hxinv := S.reflection_inv_a₁ hx₁ hx₁2
  have hy : g * x₁ * S.a₁ * (g * x₁)⁻¹ = S.a₁ := by
    calc g * x₁ * S.a₁ * (g * x₁)⁻¹ = g * (x₁ * S.a₁ * x₁⁻¹) * g⁻¹ := by group
      _ = g * S.a₁⁻¹ * g⁻¹ := by rw [hxinv]
      _ = (g * S.a₁ * g⁻¹)⁻¹ := by group
      _ = S.a₁ := by rw [hinv, inv_inv]
  have hyc : g * x₁ * S.a₁ = S.a₁ * (g * x₁) := mul_inv_eq_iff_eq_mul.mp hy
  obtain ⟨z, hzL, hz1⟩ := S.exists_ne_one_fix_reflection₁ hW hcard hx₁ hx₁2
  have hyfix : (g * x₁) z = z := by
    show g (x₁ z) = z
    rw [mem_fixV_zpowers_iff.mp hzL.2, hgfix z hzL]
  have hyW₁ := S.fix_W₁_of_commute hW hcard hyc hzL.1 hz1 hyfix
  intro w hw
  have h1 := hyW₁ (x₁ w) (S.mem_W₁_of_mem_A₁ hx₁ hw)
  have hxx : x₁ * x₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one x₁
    rwa [hx₁2] at this
  have hx₁₁ : x₁ (x₁ w) = w := by
    have : (x₁ * x₁) w = w := by rw [hxx]; rfl
    exact this
  have h2 : g (x₁ (x₁ w)) = x₁ w := h1
  rwa [hx₁₁] at h2

theorem false_of_sq_eq_refl (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {x₁ : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) {g : MulAut W} (hgst : S.Stab₁ g)
    (hgfix : ∀ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), g z = z)
    (hg2 : ∀ w ∈ S.W₁, g (g w) = x₁ w) : False := by
  have hx₁sq : x₁ ^ 2 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [hx₁2] at this
  have hL₁4 : Nat.card ↥(S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) = 4 :=
    S.card_fix_reflection₁ hW hcard hx₁ hx₁2
  have hrkL : rk ↥(S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) = 2 := by
    have h := card_eq_two_pow hW (S.W₁ ⊓ fixV (Subgroup.zpowers x₁))
    rw [hL₁4] at h
    have : (2 : ℕ) ^ 2 = 2 ^ rk ↥(S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  have hrkW : rk S.W₁ = 4 := rk_eq_four_of_card_sixteen151b hW (S.card_W₁ hcard)
  have hinvx : ∀ y ∈ Subgroup.zpowers x₁, ∀ w ∈ S.W₁, y w ∈ S.W₁ :=
    invariant_zpowers151b (fun w hw => S.mem_W₁_of_mem_A₁ hx₁ hw)
  have hinvg : ∀ y ∈ Subgroup.zpowers g, ∀ w ∈ S.W₁, y w ∈ S.W₁ :=
    invariant_zpowers151b (fun w hw => (hgst w).mp hw)
  have h1 := rk_commSub_add_rk_inf_fixV (g := x₁) (W := S.W₁) hinvx
  have h2 := rk_commSub_add_rk_inf_fixV (g := g) (W := S.W₁) hinvg
  have hL₁g : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) ≤ S.W₁ ⊓ fixV (Subgroup.zpowers g) :=
    le_inf inf_le_left (fun z hz => mem_fixV_zpowers_iff.mpr (hgfix z hz))
  have h3 := rk_mono hL₁g
  have hBxB : commSub S.W₁ (Subgroup.zpowers x₁) ≤ commSub S.W₁ (Subgroup.zpowers g) := by
    unfold commSub
    rw [Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    rcases mem_zpowers_of_sq151b hx₁sq hy with h | h
    · rw [h]
      have : (1 : MulAut W) w * w⁻¹ = 1 := by simp
      rw [this]
      exact Subgroup.one_mem _
    · rw [h]
      have hgw : g w ∈ S.W₁ := (hgst w).mp hw
      have e : x₁ w * w⁻¹ = (g (g w) * (g w)⁻¹) * (g w * w⁻¹) := by
        rw [← hg2 w hw]
        group
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, g w, hgw, rfl⟩)
        (Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hw, rfl⟩)
  have hBeq : commSub S.W₁ (Subgroup.zpowers x₁) = commSub S.W₁ (Subgroup.zpowers g) :=
    eq_of_le_of_rk_le hW hBxB (by omega)
  have hBxL : commSub S.W₁ (Subgroup.zpowers x₁) ≤ S.W₁ ⊓ fixV (Subgroup.zpowers x₁) :=
    commSub_le_fixV_of_sq151b hW hx₁sq (fun w hw => S.mem_W₁_of_mem_A₁ hx₁ hw)
  have hBL : commSub S.W₁ (Subgroup.zpowers g) ≤ S.W₁ ⊓ fixV (Subgroup.zpowers x₁) := hBeq ▸ hBxL
  have hsq : ∀ w ∈ S.W₁, g (g w) = w := by
    intro w hw
    have hmem : g w * w⁻¹ ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁) :=
      hBL (Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hw, rfl⟩)
    have hfix := hgfix _ hmem
    rw [map_mul, map_inv] at hfix
    calc g (g w) = (g (g w) * (g w)⁻¹) * g w := by group
      _ = (g w * w⁻¹) * g w := by rw [hfix]
      _ = (g w * g w) * w⁻¹ := by ac_rfl
      _ = w⁻¹ := by rw [← pow_two, hW (g w), one_mul]
      _ = w := inv_eq_self_of_sq151b hW w
  have hx1 : x₁ = 1 :=
    S.eq_one_of_fix_W₁_W₂ (fun w hw => (hg2 w hw).symm.trans (hsq w hw))
      (fun w hw => S.fix_W₂_of_mem_A₁ hx₁ hw)
  rw [hx1, orderOf_one] at hx₁2
  omega

theorem ptFix_dichotomy (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) {h : MulAut W}
    (hh : h ∈ ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) :
    (∀ w ∈ S.W₁, h w = w) ∨ (∀ w ∈ S.W₁, h w = x₁ w) := by
  obtain ⟨z, hzL, hz1⟩ := S.exists_ne_one_fix_reflection₁ hW hcard hx₁ hx₁2
  have hs := S.stab_of_mem_of_fix₁ hW hnorm hh.1 ⟨z, hzL.1, hz1, hh.2 z hzL⟩
  have hconj := S.mem_zpowers_a₁_conj hW hcard (hnorm h hh.1) hs
  rcases conj_cases_five S.orderOf_a₁_five hconj with h1 | h2 | h3
  · left
    exact S.fix_W₁_of_commute hW hcard (mul_inv_eq_iff_eq_mul.mp h1) hzL.1 hz1 (hh.2 z hzL)
  · right
    exact S.eq_refl_of_inv hW hcard hx₁ hx₁2 hh.2 h2
  · exfalso
    have hgfix : ∀ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), (h * h) z = z := by
      intro z hz
      show h (h z) = z
      rw [hh.2 z hz, hh.2 z hz]
    have hg2 := S.eq_refl_of_inv hW hcard hx₁ hx₁2 hgfix h3
    exact S.false_of_sq_eq_refl hW hcard hx₁ hx₁2 hs.1 hh.2 (fun w hw => hg2 w hw)

end CFSG.Quasithin.SixData151b
