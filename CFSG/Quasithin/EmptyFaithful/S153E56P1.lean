module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace S153E56p

section Abstract

variable {Q : Type*} [Group Q]

structure Split (β : Q → Q → ZMod 2) (E₁ E₂ : Subgroup Q) : Prop where
  comm : ∀ x y : Q, x * y = y * x
  sq : ∀ x : Q, x * x = 1
  add_left : ∀ x y z : Q, β (x * y) z = β x z + β y z
  add_right : ∀ x y z : Q, β x (y * z) = β x y + β x z
  symm : ∀ x y : Q, β x y = β y x
  nondeg : ∀ x : Q, (∀ y, β x y = 0) → x = 1
  iso₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, β x y = 0
  iso₂ : ∀ x ∈ E₂, ∀ y ∈ E₂, β x y = 0
  disj : ∀ x ∈ E₁, x ∈ E₂ → x = 1
  dec : ∀ w : Q, ∃ e ∈ E₁, ∃ e' ∈ E₂, w = e * e'

theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

variable {β : Q → Q → ZMod 2} {E₁ E₂ : Subgroup Q}

namespace Split

theorem swap (S : Split β E₁ E₂) : Split β E₂ E₁ where
  comm := S.comm
  sq := S.sq
  add_left := S.add_left
  add_right := S.add_right
  symm := S.symm
  nondeg := S.nondeg
  iso₁ := S.iso₂
  iso₂ := S.iso₁
  disj := fun x hx hx' => S.disj x hx' hx
  dec := fun w => by
    obtain ⟨e, he, e', he', rfl⟩ := S.dec w
    exact ⟨e', he', e, he, S.comm _ _⟩

theorem inv_eq (S : Split β E₁ E₂) (x : Q) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (S.sq x)

theorem one_left (S : Split β E₁ E₂) (y : Q) : β 1 y = 0 := by
  have h := S.add_left 1 1 y
  rw [mul_one] at h
  have h2 : β 1 y + β 1 y = β 1 y + 0 := by rw [← h, add_zero]
  exact add_left_cancel h2

theorem inv_left (S : Split β E₁ E₂) (x y : Q) : β x⁻¹ y = β x y := by rw [S.inv_eq]

theorem mul_inv_left (S : Split β E₁ E₂) (x y z : Q) : β (x * y⁻¹) z = β x z + β y z := by
  rw [S.add_left, S.inv_left]

theorem pair_inj (S : Split β E₁ E₂) {x : Q} (hx : x ∈ E₂) (h : ∀ e ∈ E₁, β x e = 0) : x = 1 := by
  refine S.nondeg x fun w => ?_
  obtain ⟨e, he, e', he', rfl⟩ := S.dec w
  rw [S.add_right, h e he, S.iso₂ x hx e' he', add_zero]

theorem pair_inj' (S : Split β E₁ E₂) {x : Q} (hx : x ∈ E₁) (h : ∀ e ∈ E₂, β x e = 0) : x = 1 :=
  S.swap.pair_inj hx h

theorem pair_ext (S : Split β E₁ E₂) {x y : Q} (hx : x ∈ E₂) (hy : y ∈ E₂)
    (h : ∀ e ∈ E₁, β x e = β y e) : x = y := by
  have h1 : x * y⁻¹ = 1 := S.pair_inj (E₂.mul_mem hx (E₂.inv_mem hy)) fun e he => by
    rw [S.mul_inv_left, h e he, zmod_two_add_self]
  exact mul_inv_eq_one.1 h1

end Split

structure IsOO (β : Q → Q → ZMod 2) (E₁ E₂ : Subgroup Q) (g : MulAut Q) : Prop where
  iso : ∀ x y, β (g x) (g y) = β x y
  map₁ : ∀ e ∈ E₁, g e ∈ E₁
  map₂ : ∀ e ∈ E₂, g e ∈ E₂

theorem exists_preimage_of_map_le [Finite Q] {E : Subgroup Q} {g : MulAut Q}
    (h : ∀ e ∈ E, g e ∈ E) {e : Q} (he : e ∈ E) : ∃ e₀ ∈ E, g e₀ = e := by
  have hinj : Function.Injective (fun x : E => (⟨g x, h x x.2⟩ : E)) := fun x y hxy =>
    Subtype.ext (g.injective (congrArg Subtype.val hxy))
  obtain ⟨⟨e₀, he₀⟩, h'⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨e, he⟩
  exact ⟨e₀, he₀, congrArg Subtype.val h'⟩

namespace IsOO

theorem one : IsOO β E₁ E₂ 1 := ⟨fun _ _ => rfl, fun _ h => h, fun _ h => h⟩

theorem mul {g₁ g₂ : MulAut Q} (h₁ : IsOO β E₁ E₂ g₁) (h₂ : IsOO β E₁ E₂ g₂) :
    IsOO β E₁ E₂ (g₁ * g₂) :=
  ⟨fun x y => by rw [MulAut.mul_apply, MulAut.mul_apply, h₁.iso, h₂.iso],
    fun e he => h₁.map₁ _ (h₂.map₁ e he), fun e he => h₁.map₂ _ (h₂.map₂ e he)⟩

theorem swap {g : MulAut Q} (h : IsOO β E₁ E₂ g) : IsOO β E₂ E₁ g := ⟨h.iso, h.map₂, h.map₁⟩

end IsOO

@[expose] def sm (b : ZMod 2) (c : Q) : Q := if b = 0 then 1 else c

theorem sm_zero (c : Q) : sm 0 c = 1 := by simp [sm]

theorem sm_one (c : Q) : sm 1 c = c := by simp [sm]

theorem sm_of_ne {b : ZMod 2} (h : b ≠ 0) (c : Q) : sm b c = c := by simp [sm, h]

theorem sm_mem {E : Subgroup Q} {b : ZMod 2} {c : Q} (hc : c ∈ E) : sm b c ∈ E := by
  unfold sm
  split_ifs
  · exact E.one_mem
  · exact hc

open scoped Classical in
@[expose] noncomputable def phi (g : MulAut Q) (e : Q) : ZMod 2 := if g e = e then 0 else 1

theorem phi_eq_zero_iff {g : MulAut Q} {e : Q} : phi g e = 0 ↔ g e = e := by
  unfold phi
  split_ifs with h <;> simp [h]

theorem phi_eq_one_iff {g : MulAut Q} {e : Q} : phi g e = 1 ↔ g e ≠ e := by
  unfold phi
  split_ifs with h <;> simp [h]

theorem zmod_two_eq_one {b : ZMod 2} (h : b ≠ 0) : b = 1 := by
  revert b; decide

theorem zmod_two_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by revert b; decide

theorem zmod_two_eq_zero_of_ne_one {b : ZMod 2} (h : b ≠ 1) : b = 0 := by revert b; decide

theorem sm_one_right (b : ZMod 2) : sm b (1 : Q) = 1 := by simp [sm]

theorem sm_mul_dist (b : ZMod 2) (u v : Q) : sm b (u * v) = sm b u * sm b v := by
  rcases zmod_two_cases b with rfl | rfl <;> simp [sm_zero, sm_one]

theorem map_sm (g : MulAut Q) (b : ZMod 2) (c : Q) : g (sm b c) = sm b (g c) := by
  rcases zmod_two_cases b with rfl | rfl <;> simp [sm_zero, sm_one]

theorem sm_sm (x z : ZMod 2) (c : Q) : sm x (sm z c) = sm (x * z) c := by
  rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases z with rfl | rfl <;>
    simp [sm_zero, sm_one, sm_one_right]

theorem sm_self (hsq : ∀ x : Q, x * x = 1) (b : ZMod 2) (c : Q) : sm b c * sm b c = 1 := by
  rcases zmod_two_cases b with rfl | rfl <;> simp [sm_zero, sm_one, hsq c]

theorem sm_add (hsq : ∀ x : Q, x * x = 1) (b₁ b₂ : ZMod 2) (c : Q) :
    sm (b₁ + b₂) c = sm b₁ c * sm b₂ c := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod_two_cases b₁ with rfl | rfl <;> rcases zmod_two_cases b₂ with rfl | rfl <;>
    simp [sm_zero, sm_one, h11, hsq c]

theorem sm_inj {a' : Q} (ha : a' ≠ 1) {b b' : ZMod 2} (h : sm b a' = sm b' a') : b = b' := by
  rcases zmod_two_cases b with rfl | rfl <;> rcases zmod_two_cases b' with rfl | rfl <;>
    simp_all [sm_zero, sm_one, eq_comm]

theorem sm_eq_one_iff {a' : Q} (ha : a' ≠ 1) {b : ZMod 2} : sm b a' = 1 ↔ b = 0 := by
  constructor
  · intro h
    exact sm_inj ha (by rw [h, sm_zero])
  · rintro rfl
    exact sm_zero a'

open scoped Classical in
theorem tr_eq_sm {h : MulAut Q} {a' : Q} {E : Subgroup Q} (htr : ∀ e ∈ E, h e = e ∨ h e = e * a')
    {u : Q} (hu : u ∈ E) : h u = u * sm (phi h u) a' := by
  by_cases hh : h u = u
  · rw [phi_eq_zero_iff.2 hh, sm_zero, mul_one, hh]
  · rw [phi_eq_one_iff.2 hh, sm_one]
    exact (htr u hu).resolve_left hh

theorem phi_add (hcomm : ∀ x y : Q, x * y = y * x) (hsq : ∀ x : Q, x * x = 1) {h : MulAut Q}
    {a' : Q} (ha1 : a' ≠ 1) (htr : ∀ e : Q, h e = e ∨ h e = e * a') (u v : Q) :
    phi h (u * v) = phi h u + phi h v := by
  have e1 := tr_eq_sm (E := ⊤) (fun e _ => htr e) (Subgroup.mem_top u)
  have e2 := tr_eq_sm (E := ⊤) (fun e _ => htr e) (Subgroup.mem_top v)
  have e3 := tr_eq_sm (E := ⊤) (fun e _ => htr e) (Subgroup.mem_top (u * v))
  rw [map_mul, e1, e2] at e3
  have e4 : u * sm (phi h u) a' * (v * sm (phi h v) a') =
      u * v * (sm (phi h u) a' * sm (phi h v) a') := by
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    ac_rfl
  rw [e4] at e3
  have e5 := mul_left_cancel e3
  rw [← sm_add hsq] at e5
  exact (sm_inj ha1 e5).symm

theorem phi_add_on (hcomm : ∀ x y : Q, x * y = y * x) (hsq : ∀ x : Q, x * x = 1) {E : Subgroup Q}
    {h : MulAut Q} {a' : Q} (ha1 : a' ≠ 1) (htr : ∀ e ∈ E, h e = e ∨ h e = e * a') {u v : Q}
    (hu : u ∈ E) (hv : v ∈ E) : phi h (u * v) = phi h u + phi h v := by
  have e1 := tr_eq_sm htr hu
  have e2 := tr_eq_sm htr hv
  have e3 := tr_eq_sm htr (E.mul_mem hu hv)
  rw [map_mul, e1, e2] at e3
  have e4 : u * sm (phi h u) a' * (v * sm (phi h v) a') =
      u * v * (sm (phi h u) a' * sm (phi h v) a') := by
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    ac_rfl
  rw [e4] at e3
  have e5 := mul_left_cancel e3
  rw [← sm_add hsq] at e5
  exact (sm_inj ha1 e5).symm

theorem theta (hcomm : ∀ x y : Q, x * y = y * x) (hsq : ∀ x : Q, x * x = 1) {g h : MulAut Q} {w c a' : Q} {x y z : ZMod 2}
    (hgw : g w = w * sm x c) (hga' : g a' = a') (hgc : g c = c)
    (hhw : h w = w * sm y a') (hhc : h c = c * sm z a') (hha' : h a' = a') :
    h (g (h (g w))) = w * sm (x * z) a' := by
  have hgp : g (sm y a') = sm y a' := by rw [map_sm, hga']
  have hgq : g (sm x c) = sm x c := by rw [map_sm, hgc]
  have hgr : g (sm x (sm z a')) = sm x (sm z a') := by rw [map_sm, map_sm, hga']
  have hhp : h (sm y a') = sm y a' := by rw [map_sm, hha']
  have hhr : h (sm x (sm z a')) = sm x (sm z a') := by rw [map_sm, map_sm, hha']
  have hhq : h (sm x c) = sm x c * sm x (sm z a') := by rw [map_sm, hhc, sm_mul_dist]
  have step1 : h (g w) = w * sm y a' * (sm x c * sm x (sm z a')) := by
    rw [hgw, map_mul, hhw, hhq]
  have step2 : g (h (g w)) = w * sm x c * sm y a' * (sm x c * sm x (sm z a')) := by
    rw [step1, map_mul, map_mul, map_mul, hgw, hgp, hgq, hgr]
  have step3 : h (g (h (g w))) = (w * sm y a') * (sm x c * sm x (sm z a')) * sm y a' *
      ((sm x c * sm x (sm z a')) * sm x (sm z a')) := by
    rw [step2, map_mul, map_mul, map_mul, map_mul, hhw, hhq, hhp, hhr]
  rw [step3, ← sm_sm]
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  calc _ = w * (sm y a' * sm y a') * (sm x c * sm x c) * (sm x (sm z a') * sm x (sm z a')) *
        sm x (sm z a') := by ac_rfl
    _ = w * sm x (sm z a') := by rw [sm_self hsq, sm_self hsq, sm_self hsq]; simp

namespace Split

theorem determ₁ [Finite Q] (S : Split β E₁ E₂) {g₁ g₂ : MulAut Q} (h₁ : IsOO β E₁ E₂ g₁)
    (h₂ : IsOO β E₁ E₂ g₂) (h : ∀ e ∈ E₁, g₁ e = g₂ e) : g₁ = g₂ := by
  have hE₂ : ∀ w ∈ E₂, g₁ w = g₂ w := fun w hw => by
    refine S.pair_ext (h₁.map₂ w hw) (h₂.map₂ w hw) fun e he => ?_
    obtain ⟨e₀, he₀, rfl⟩ := exists_preimage_of_map_le h₁.map₁ he
    rw [h₁.iso, h e₀ he₀, h₂.iso]
  ext w
  obtain ⟨e, he, e', he', rfl⟩ := S.dec w
  rw [map_mul, map_mul, h e he, hE₂ e' he']

theorem determ₂ [Finite Q] (S : Split β E₁ E₂) {g₁ g₂ : MulAut Q}
    (h₁ : IsOO β E₂ E₁ g₁) (h₂ : IsOO β E₂ E₁ g₂) (h : ∀ e ∈ E₂, g₁ e = g₂ e) : g₁ = g₂ :=
  S.swap.determ₁ h₁ h₂ h

theorem contra_pair (S : Split β E₁ E₂) {g : MulAut Q} (hg : IsOO β E₁ E₂ g) {a : Q}
    (hga : g a = a) (htr : ∀ e ∈ E₁, g e = e ∨ g e = e * a) {w : Q} (e : Q) (he : e ∈ E₁) :
    β (g w * w⁻¹) e = phi g e * β w a := by
  by_cases h : g e = e
  · have h1 : β (g w) e = β w e := by
      have := hg.iso w e
      rwa [h] at this
    rw [S.mul_inv_left, h1, zmod_two_add_self, phi_eq_zero_iff.2 h, zero_mul]
  · have hge : g e = e * a := (htr e he).resolve_left h
    have h1 : β (g w) a = β w a := by
      have := hg.iso w a
      rwa [hga] at this
    have h2 : β (g w) e + β w a = β w e := by
      have := hg.iso w e
      rwa [hge, S.add_right, h1] at this
    rw [S.mul_inv_left, phi_eq_one_iff.2 h, one_mul]
    have h3 : β (g w) e = β w e + β w a := by
      rw [← h2]
      have : ∀ x y : ZMod 2, x + y + y = x := by decide
      rw [this]
    rw [h3]
    have : ∀ x y : ZMod 2, x + y + x = y := by decide
    exact this _ _

theorem contra (S : Split β E₁ E₂) {g : MulAut Q} (hg : IsOO β E₁ E₂ g) {a : Q}
    (hga : g a = a) (htr : ∀ e ∈ E₁, g e = e ∨ g e = e * a) {w₀ : Q} (hw₀ : w₀ ∈ E₂)
    (hw₀a : β w₀ a = 1) {w : Q} (hw : w ∈ E₂) :
    g w = w * sm (β w a) (g w₀ * w₀⁻¹) := by
  have hc : g w₀ * w₀⁻¹ ∈ E₂ := E₂.mul_mem (hg.map₂ w₀ hw₀) (E₂.inv_mem hw₀)
  have hu : g w * w⁻¹ ∈ E₂ := E₂.mul_mem (hg.map₂ w hw) (E₂.inv_mem hw)
  have key : g w * w⁻¹ = sm (β w a) (g w₀ * w₀⁻¹) := by
    refine S.pair_ext hu (sm_mem hc) fun e he => ?_
    rw [S.contra_pair hg hga htr e he]
    by_cases hwa : β w a = 0
    · rw [hwa, sm_zero, S.one_left, mul_zero]
    · rw [sm_of_ne hwa, S.contra_pair hg hga htr e he, hw₀a, zmod_two_eq_one hwa]
  calc g w = (g w * w⁻¹) * w := by rw [inv_mul_cancel_right]
    _ = w * (g w * w⁻¹) := S.comm _ _
    _ = w * sm (β w a) (g w₀ * w₀⁻¹) := by rw [key]

theorem contra_perp (S : Split β E₁ E₂) {g : MulAut Q} (hg : IsOO β E₁ E₂ g) {a : Q}
    (hga : g a = a) {w₀ : Q} : β (g w₀ * w₀⁻¹) a = 0 := by
  have h1 : β (g w₀) a = β w₀ a := by
    have := hg.iso w₀ a
    rwa [hga] at this
  rw [S.mul_inv_left, h1, zmod_two_add_self]

theorem eq_one_or_eq_of_tr (S : Split β E₁ E₂) {g : MulAut Q} {a w₀ : Q}
    (htr : g w₀ = w₀ ∨ g w₀ = w₀ * a) : g w₀ * w₀⁻¹ = 1 ∨ g w₀ * w₀⁻¹ = a := by
  rcases htr with h | h
  · left; rw [h, mul_inv_cancel]
  · right; rw [h, S.comm w₀ a, mul_assoc, mul_inv_cancel, mul_one]

theorem nu_formula [Finite Q] (S : Split β E₁ E₂) {ν : MulAut Q} (hν : IsOO β E₁ E₂ ν) {a a' w₀ : Q}
    (hνa : ν a = a) (htr₁ : ∀ e ∈ E₁, ν e = e ∨ ν e = e * a)
    (htr₂ : ∀ e ∈ E₂, ν e = e ∨ ν e = e * a') (hw₀ : w₀ ∈ E₂) (hw₀a : β w₀ a = 1) (hν1 : ν ≠ 1)
    {w : Q} (hw : w ∈ E₂) : ν w = w * sm (β w a) a' := by
  rcases S.eq_one_or_eq_of_tr (htr₂ w₀ hw₀) with hc | hc
  · exfalso
    apply hν1
    refine S.determ₂ hν.swap IsOO.one.swap fun w hw => ?_
    rw [S.contra hν hνa htr₁ hw₀ hw₀a hw, hc, sm_one_right, mul_one, MulAut.one_apply]
  · rw [S.contra hν hνa htr₁ hw₀ hw₀a hw, hc]

theorem inter_abs [Finite Q] (S : Split β E₁ E₂) {g ν : MulAut Q} (hg : IsOO β E₁ E₂ g)
    {a a' w₀ : Q} (hga : g a = a) (htr₁ : ∀ e ∈ E₁, g e = e ∨ g e = e * a)
    (htr₂ : ∀ e ∈ E₂, g e = e ∨ g e = e * a') (hw₀ : w₀ ∈ E₂) (hw₀a : β w₀ a = 1)
    (hν' : IsOO β E₁ E₂ ν) (hν : ∀ w ∈ E₂, ν w = w * sm (β w a) a') : g = 1 ∨ g = ν := by
  rcases S.eq_one_or_eq_of_tr (htr₂ w₀ hw₀) with hc | hc
  · left
    refine S.determ₂ hg.swap IsOO.one.swap fun w hw => ?_
    rw [S.contra hg hga htr₁ hw₀ hw₀a hw, hc, sm_one_right, mul_one, MulAut.one_apply]
  · right
    refine S.determ₂ hg.swap hν'.swap fun w hw => ?_
    rw [S.contra hg hga htr₁ hw₀ hw₀a hw, hc, hν w hw]

theorem rad_abs [Finite Q] (S : Split β E₁ E₂) {h ν : MulAut Q} (hh : IsOO β E₁ E₂ h)
    {a a' w₀ : Q} (htr₂ : ∀ e ∈ E₂, h e = e ∨ h e = e * a') (hw₀ : w₀ ∈ E₂)
    (hw₀a : β w₀ a = 1) (hν' : IsOO β E₁ E₂ ν) (hν : ∀ w ∈ E₂, ν w = w * sm (β w a) a')
    (hfix : ∀ c ∈ E₂, β c a = 0 → h c = c) : h = 1 ∨ h = ν := by
  have key : ∀ w ∈ E₂, h w = w * sm (β w a) (h w₀ * w₀⁻¹) := by
    intro w hw
    by_cases hwa : β w a = 0
    · rw [hwa, sm_zero, mul_one]
      exact hfix w hw hwa
    · have h1 : β w a = 1 := zmod_two_eq_one hwa
      have hc : w * w₀⁻¹ ∈ E₂ := E₂.mul_mem hw (E₂.inv_mem hw₀)
      have hc0 : β (w * w₀⁻¹) a = 0 := by
        rw [S.mul_inv_left, h1, hw₀a]; decide
      have := hfix _ hc hc0
      rw [map_mul, map_inv] at this
      rw [h1, sm_one]
      calc h w = (h w * (h w₀)⁻¹) * h w₀ := by rw [inv_mul_cancel_right]
        _ = (w * w₀⁻¹) * h w₀ := by rw [this]
        _ = w * (h w₀ * w₀⁻¹) := by rw [mul_assoc, S.comm w₀⁻¹, ← mul_assoc]
  rcases S.eq_one_or_eq_of_tr (htr₂ w₀ hw₀) with hc | hc
  · left
    refine S.determ₂ hh.swap IsOO.one.swap fun w hw => ?_
    rw [key w hw, hc, sm_one_right, mul_one, MulAut.one_apply]
  · right
    refine S.determ₂ hh.swap hν'.swap fun w hw => ?_
    rw [key w hw, hc, hν w hw]

theorem fix_of_comm (hQc : ∀ x y : Q, x * y = y * x) (hsq : ∀ x : Q, x * x = 1) {g h : MulAut Q} {w₀ c a' : Q} {y z : ZMod 2}
    (hgw : g w₀ = w₀ * c) (hga' : g a' = a') (hgc : g c = c)
    (hhw : h w₀ = w₀ * sm y a') (hhc : h c = c * sm z a') (hha' : h a' = a') (ha1 : a' ≠ 1)
    (hgg : g * g = 1) (hhh : h * h = 1) (hcomm : h * g = g * h) : h c = c := by
  have h1 := theta hQc hsq (g := g) (h := h) (w := w₀) (c := c) (a' := a') (x := 1) (y := y) (z := z)
    (by rw [hgw, sm_one]) hga' hgc hhw hhc hha'
  have h2 : h (g (h (g w₀))) = w₀ := by
    have e : h * g * (h * g) = 1 := by
      calc h * g * (h * g) = h * (g * h) * g := by group
        _ = h * (h * g) * g := by rw [hcomm]
        _ = (h * h) * (g * g) := by group
        _ = 1 := by rw [hgg, hhh, mul_one]
    have := congrArg (fun k : MulAut Q => k w₀) e
    simpa using this
  rw [h2] at h1
  have h3 : sm (1 * z) a' = 1 := by
    have : w₀ * sm (1 * z) a' = w₀ * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel this
  rw [sm_eq_one_iff ha1, one_mul] at h3
  rw [hhc, h3, sm_zero, mul_one]

theorem dec_unique (S : Split β E₁ E₂) {a a' b b' : Q} (ha : a ∈ E₁) (ha' : a' ∈ E₁)
    (hb : b ∈ E₂) (hb' : b' ∈ E₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a = 1 := S.disj _ (E₁.mul_mem (E₁.inv_mem ha') ha)
    (h1 ▸ E₂.mul_mem hb' (E₂.inv_mem hb))
  have h3 : a = a' := (inv_mul_eq_one.1 h2).symm
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

theorem exists_w₀ (S : Split β E₁ E₂) {a : Q} (ha : a ∈ E₁) (ha1 : a ≠ 1) :
    ∃ w₀ ∈ E₂, β w₀ a = 1 := by
  by_contra hcon
  push Not at hcon
  apply ha1
  refine S.pair_inj' ha fun e he => ?_
  rw [S.symm]
  exact zmod_two_eq_zero_of_ne_one (hcon e he)

theorem comm_abs [Finite Q] (S : Split β E₁ E₂) {g h ν : MulAut Q} {a a' w₀ : Q}
    (hg : IsOO β E₁ E₂ g) (hga : g a = a) (htr₁ : ∀ e ∈ E₁, g e = e ∨ g e = e * a)
    (hgg : g * g = 1) (hh : IsOO β E₁ E₂ h) (hha' : h a' = a')
    (htr₂ : ∀ e ∈ E₂, h e = e ∨ h e = e * a') (hhh : h * h = 1) (ha' : a' ∈ E₂)
    (haa' : β a' a = 0) (hw₀ : w₀ ∈ E₂) (hw₀a : β w₀ a = 1)
    (hν' : IsOO β E₁ E₂ ν) (hν : ∀ w ∈ E₂, ν w = w * sm (β w a) a') :
    h * g * h⁻¹ * g⁻¹ = 1 ∨ h * g * h⁻¹ * g⁻¹ = ν := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hhh
  rw [hginv, hhinv]
  have hΘ : IsOO β E₁ E₂ (h * g * h * g) := ((hh.mul hg).mul hh).mul hg
  have hc : g w₀ * w₀⁻¹ ∈ E₂ := E₂.mul_mem (hg.map₂ w₀ hw₀) (E₂.inv_mem hw₀)
  have hca : β (g w₀ * w₀⁻¹) a = 0 := S.contra_perp hg hga
  have hgform := fun w hw => S.contra hg hga htr₁ hw₀ hw₀a (w := w) hw
  have hga' : g a' = a' := by
    rw [hgform a' ha', haa', sm_zero, mul_one]
  have hgc : g (g w₀ * w₀⁻¹) = g w₀ * w₀⁻¹ := by
    rw [hgform _ hc, hca, sm_zero, mul_one]
  have key : ∀ w ∈ E₂, (h * g * h * g) w = w * sm (β w a * phi h (g w₀ * w₀⁻¹)) a' := by
    intro w hw
    have := theta S.comm S.sq (g := g) (h := h) (w := w) (c := g w₀ * w₀⁻¹) (a' := a')
      (x := β w a) (y := phi h w) (z := phi h (g w₀ * w₀⁻¹)) (hgform w hw) hga' hgc
      (tr_eq_sm htr₂ hw) (tr_eq_sm htr₂ hc) hha'
    simpa [MulAut.mul_apply] using this
  rcases zmod_two_cases (phi h (g w₀ * w₀⁻¹)) with hz | hz
  · left
    refine S.determ₂ hΘ.swap IsOO.one.swap fun w hw => ?_
    rw [key w hw, hz, mul_zero, sm_zero, mul_one, MulAut.one_apply]
  · right
    refine S.determ₂ hΘ.swap hν'.swap fun w hw => ?_
    rw [key w hw, hz, mul_one, hν w hw]

theorem rad_full [Finite Q] (S : Split β E₁ E₂) {h ν : MulAut Q} {a a' w₀ : Q}
    (hh : IsOO β E₁ E₂ h) (hha' : h a' = a') (htr₂ : ∀ e ∈ E₂, h e = e ∨ h e = e * a')
    (hhh : h * h = 1) (ha' : a' ∈ E₂) (ha1' : a' ≠ 1) (haa' : β a' a = 0) (hw₀ : w₀ ∈ E₂)
    (hw₀a : β w₀ a = 1) (hν' : IsOO β E₁ E₂ ν) (hν : ∀ w ∈ E₂, ν w = w * sm (β w a) a')
    (hP : ∀ c ∈ E₂, β c a = 0 → ∃ g : MulAut Q, IsOO β E₁ E₂ g ∧ g a = a ∧
      (∀ e ∈ E₁, g e = e ∨ g e = e * a) ∧ g * g = 1 ∧ g w₀ * w₀⁻¹ = c ∧ h * g = g * h) :
    h = 1 ∨ h = ν := by
  refine S.rad_abs hh htr₂ hw₀ hw₀a hν' hν fun c hc hca => ?_
  obtain ⟨g, hg, hga, htr₁, hgg, hgc, hcomm⟩ := hP c hc hca
  have hgform := fun w hw => S.contra hg hga htr₁ hw₀ hw₀a (w := w) hw
  have hga' : g a' = a' := by
    rw [hgform a' ha', haa', sm_zero, mul_one]
  have hgc' : g c = c := by
    rw [hgform c hc, hca, sm_zero, mul_one]
  have hgw : g w₀ = w₀ * c := by
    calc g w₀ = (g w₀ * w₀⁻¹) * w₀ := by rw [inv_mul_cancel_right]
      _ = c * w₀ := by rw [hgc]
      _ = w₀ * c := S.comm _ _
  exact fix_of_comm S.comm S.sq hgw hga' hgc' (tr_eq_sm htr₂ hw₀) (tr_eq_sm htr₂ hc) hha' ha1'
    hgg hhh hcomm

end Split

end Abstract

end S153E56p

end CFSG.Quasithin
