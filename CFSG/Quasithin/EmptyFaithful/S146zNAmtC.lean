module

public import CFSG.Quasithin.EmptyFaithful.S146zNAmtA
public import CFSG.Quasithin.EmptyFaithful.S146zNAmtB

public section

namespace CFSG.Quasithin.A6Amt

section Twist

variable {V : Type} [CommGroup V]

@[expose] def tw (γ : MulAut V) (W : Subgroup V) : Subgroup V where
  carrier := {v | γ⁻¹ v ∈ W}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show γ⁻¹ (a * b) ∈ W
    rw [map_mul]
    exact W.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show γ⁻¹ a⁻¹ ∈ W
    rw [map_inv]
    exact W.inv_mem ha

theorem mem_tw {γ : MulAut V} {W : Subgroup V} {v : V} : v ∈ tw γ W ↔ γ⁻¹ v ∈ W := Iff.rfl

theorem tw_one (W : Subgroup V) : tw 1 W = W := by
  ext v
  simp [mem_tw]

theorem tw_mul (γ δ : MulAut V) (W : Subgroup V) : tw (γ * δ) W = tw γ (tw δ W) := by
  ext v
  simp [mem_tw, MulAut.mul_apply]

theorem tw_inj {γ : MulAut V} {A B : Subgroup V} (h : tw γ A = tw γ B) : A = B := by
  have h1 : ∀ C : Subgroup V, tw γ⁻¹ (tw γ C) = C := fun C => by
    rw [← tw_mul, inv_mul_cancel, tw_one]
  rw [← h1 A, h, h1 B]

theorem rk_tw [Finite V] (γ : MulAut V) (W : Subgroup V) : rk (tw γ W) = rk W :=
  rk_eq_of_iff γ⁻¹ fun _ => Iff.rfl

end Twist

section Context

variable {V : Type} [CommGroup V]

structure Ctx (Γ L : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V) (s : MulAut V) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  hLΓ : L ≤ Γ
  hnorm : ∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L
  hs : s ∈ Γ
  hsup : W₁ ⊔ W₂ = ⊤
  hW₁ : ∀ l ∈ L, ∀ w ∈ W₁, l w ∈ W₁
  hW₂ : ∀ l ∈ L, ∀ w ∈ W₂, l w ∈ W₂
  hW₂s : ∀ w : V, w ∈ W₂ ↔ s⁻¹ w ∈ W₁
  hrk : rk W₁ = 4
  hirr : ∀ S : Subgroup V, S ≤ W₁ → (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = W₁
  hiso : Nonempty (L ≃* alternatingGroup (Fin 6))
  hfuse : ∃ x ∈ L, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l ∈ L, l * x * l⁻¹ ≠ s * x * s⁻¹

variable {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V} {s : MulAut V}

theorem Ctx.mem_W₁_iff (c : Ctx Γ L W₁ W₂ s) {l : MulAut V} (hl : l ∈ L) (u : V) :
    l u ∈ W₁ ↔ u ∈ W₁ := by
  refine ⟨fun h => ?_, c.hW₁ l hl u⟩
  have := c.hW₁ l⁻¹ (L.inv_mem hl) (l u) h
  simpa [MulAut.inv_apply] using this

theorem Ctx.le_stab (c : Ctx Γ L W₁ W₂ s) : L ≤ stabSub W₁ := fun _ hl u => c.mem_W₁_iff hl u

theorem Ctx.W₂_eq_tw (c : Ctx Γ L W₁ W₂ s) : W₂ = tw s W₁ := Subgroup.ext fun v => c.hW₂s v

theorem Ctx.card_W₁ [Finite V] (c : Ctx Γ L W₁ W₂ s) : Nat.card W₁ = 16 := by
  rw [card_eq_two_pow c.hV W₁, c.hrk]
  norm_num

theorem Ctx.rk_W₂ [Finite V] (c : Ctx Γ L W₁ W₂ s) : rk W₂ = 4 :=
  (rk_eq_of_iff (s⁻¹ : MulAut V) c.hW₂s).trans c.hrk

theorem Ctx.card_W₂ [Finite V] (c : Ctx Γ L W₁ W₂ s) : Nat.card W₂ = 16 := by
  rw [card_eq_two_pow c.hV W₂, c.rk_W₂]
  norm_num

theorem Ctx.rk_V [Finite V] (c : Ctx Γ L W₁ W₂ s) (hinf : W₁ ⊓ W₂ = ⊥) : rk V = 8 := by
  have := rk_eq_add_of_decomp c.hsup hinf
  have h2 := c.rk_W₂
  have h1 := c.hrk
  omega

theorem Ctx.tw_stable (c : Ctx Γ L W₁ W₂ s) {γ : MulAut V} (hγ : γ ∈ Γ) {l : MulAut V}
    (hl : l ∈ L) {v : V} (hv : v ∈ tw γ W₁) : l v ∈ tw γ W₁ := by
  have h1 : γ⁻¹ * l * γ ∈ L := by
    simpa using c.hnorm γ⁻¹ (Γ.inv_mem hγ) l hl
  have h2 := c.hW₁ _ h1 _ hv
  rw [mem_tw]
  simpa [MulAut.mul_apply] using h2

theorem Ctx.tw_irred (c : Ctx Γ L W₁ W₂ s) {γ : MulAut V} (hγ : γ ∈ Γ) (S : Subgroup V)
    (hS₁ : S ≤ tw γ W₁) (hS₂ : ∀ l ∈ L, ∀ w ∈ S, l w ∈ S) : S = ⊥ ∨ S = tw γ W₁ := by
  have hS₀₁ : tw γ⁻¹ S ≤ W₁ := by
    intro v hv
    have := hS₁ (by simpa [mem_tw] using hv : γ v ∈ S)
    simpa [mem_tw] using this
  have hS₀₂ : ∀ l ∈ L, ∀ w ∈ tw γ⁻¹ S, l w ∈ tw γ⁻¹ S := by
    intro l hl w hw
    have hw' : γ w ∈ S := by simpa [mem_tw] using hw
    have h1 : γ * l * γ⁻¹ ∈ L := c.hnorm γ hγ l hl
    have := hS₂ _ h1 _ hw'
    simpa [mem_tw, MulAut.mul_apply] using this
  rcases c.hirr (tw γ⁻¹ S) hS₀₁ hS₀₂ with h0 | h0
  · left
    rw [eq_bot_iff]
    intro v hv
    have h1 : γ⁻¹ v ∈ tw γ⁻¹ S := by simpa [mem_tw] using hv
    rw [h0, Subgroup.mem_bot] at h1
    have : v = 1 := by simpa using congrArg γ h1
    exact Subgroup.mem_bot.mpr this
  · right
    refine le_antisymm hS₁ fun v hv => ?_
    have h1 : γ⁻¹ v ∈ tw γ⁻¹ S := by rw [h0]; exact hv
    simpa [mem_tw] using h1

end Context

section Restriction

variable {V : Type} [CommGroup V]

@[expose] def res {W : Subgroup V} {γ : MulAut V} (hγ : γ ∈ stabSub W) : MulAut ↥W :=
  resHom W ⟨γ, hγ⟩

theorem res_mul {W : Subgroup V} {γ δ : MulAut V} (hγ : γ ∈ stabSub W) (hδ : δ ∈ stabSub W) :
    res ((stabSub W).mul_mem hγ hδ) = res hγ * res hδ :=
  map_mul (resHom W) ⟨γ, hγ⟩ ⟨δ, hδ⟩

theorem res_inv {W : Subgroup V} {γ : MulAut V} (hγ : γ ∈ stabSub W) :
    res ((stabSub W).inv_mem hγ) = (res hγ)⁻¹ :=
  map_inv (resHom W) ⟨γ, hγ⟩

theorem res_eq_res_iff {W : Subgroup V} {γ δ : MulAut V} (hγ : γ ∈ stabSub W)
    (hδ : δ ∈ stabSub W) : res hγ = res hδ ↔ ∀ u ∈ W, γ u = δ u := by
  constructor
  · intro h u hu
    exact congrArg (fun φ : MulAut ↥W => ((φ ⟨u, hu⟩ : ↥W) : V)) h
  · intro h
    ext u
    exact h u u.2

theorem res_eq_one_iff {W : Subgroup V} {γ : MulAut V} (hγ : γ ∈ stabSub W) :
    res hγ = 1 ↔ ∀ u ∈ W, γ u = u := by
  have h1 : res ((stabSub W).one_mem) = (1 : MulAut ↥W) := map_one (resHom W)
  rw [← h1, res_eq_res_iff hγ ((stabSub W).one_mem)]
  rfl

end Restriction

section Representation

variable {V : Type} [CommGroup V] {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V} {s : MulAut V}

@[expose] def Ctx.rL (c : Ctx Γ L W₁ W₂ s) : ↥L →* MulAut ↥W₁ :=
  (resHom W₁).comp (Subgroup.inclusion c.le_stab)

theorem Ctx.rL_apply (c : Ctx Γ L W₁ W₂ s) (l : ↥L) (w : ↥W₁) :
    ((c.rL l w : ↥W₁) : V) = (l : MulAut V) w := rfl

theorem Ctx.rL_eq_res (c : Ctx Γ L W₁ W₂ s) {l : MulAut V} (hl : l ∈ L) :
    c.rL ⟨l, hl⟩ = res (c.le_stab hl) := rfl

@[expose] def Ctx.cL (c : Ctx Γ L W₁ W₂ s) : ↥L ≃* ↥L where
  toFun l := ⟨s * l * s⁻¹, c.hnorm s c.hs l l.2⟩
  invFun l := ⟨s⁻¹ * l * s, by simpa using c.hnorm s⁻¹ (Γ.inv_mem c.hs) l l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem Ctx.cL_apply (c : Ctx Γ L W₁ W₂ s) (l : ↥L) :
    ((c.cL l : ↥L) : MulAut V) = s * l * s⁻¹ := rfl

@[expose] def Ctx.sRes (c : Ctx Γ L W₁ W₂ s) : ↥W₁ ≃* ↥W₂ where
  toFun w := ⟨s w, (c.hW₂s _).2 (by simp)⟩
  invFun w := ⟨s⁻¹ w, (c.hW₂s _).1 w.2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem Ctx.sRes_apply (c : Ctx Γ L W₁ W₂ s) (w : ↥W₁) :
    ((c.sRes w : ↥W₂) : V) = s w := rfl

theorem Ctx.facts [Finite V] (c : Ctx Γ L W₁ W₂ s) (h : A6Fin) : A6Facts c.rL c.cL := by
  obtain ⟨e⟩ := c.hiso
  refine A6Facts.of_fin h (fun w => Subtype.ext (by simpa using c.hV w)) c.card_W₁ e c.rL ?_
    c.cL ?_
  · intro S hS
    have h1 := c.hirr (S.map W₁.subtype) (Subgroup.map_subtype_le S) (fun l hl x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨c.rL ⟨l, hl⟩ y, hS ⟨l, hl⟩ y hy, rfl⟩)
    rcases h1 with h1 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      have : (y : V) ∈ S.map W₁.subtype := ⟨y, hy, rfl⟩
      rw [h1, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    · right
      rw [eq_top_iff]
      intro y _
      have : (y : V) ∈ S.map W₁.subtype := by rw [h1]; exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
  · obtain ⟨x, hxL, hx3, hx1, hx⟩ := c.hfuse
    refine ⟨⟨x, hxL⟩, Subtype.ext (by simpa using hx3), fun h1 => hx1 (congrArg Subtype.val h1),
      fun l hl => ?_⟩
    exact hx l l.2 (congrArg Subtype.val hl)

end Representation

end CFSG.Quasithin.A6Amt
