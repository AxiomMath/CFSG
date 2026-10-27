module

public import CFSG.Quasithin.EmptyFaithful.S146zNAmtC

public section

namespace CFSG.Quasithin.A6Amt

section Graph

variable {V : Type} [CommGroup V] [Finite V] {W₁ W₂ X : Subgroup V}

theorem exists_graph_equiv (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥) (hX₁ : X ⊓ W₁ = ⊥)
    (hX₂ : X ⊓ W₂ = ⊥) (hc₁ : Nat.card X = Nat.card W₁) (hc₂ : Nat.card X = Nat.card W₂) :
    ∃ θ : ↥W₂ ≃* ↥W₁, ∀ l : MulAut V, (∀ w ∈ W₁, l w ∈ W₁) → (∀ w ∈ W₂, l w ∈ W₂) →
      (∀ x ∈ X, l x ∈ X) → ∀ w w' : ↥W₂, (w' : V) = l w →
        ((θ w' : ↥W₁) : V) = l ((θ w : ↥W₁) : V) := by
  have hsup' : W₂ ⊔ W₁ = ⊤ := by rwa [sup_comm]
  have hinf' : W₂ ⊓ W₁ = ⊥ := by rwa [inf_comm]
  obtain ⟨p₁, hp₁0, hp₁1, hp₁2⟩ := exists_proj hsup hinf
  obtain ⟨p₂, hp₂0, hp₂1, hp₂2⟩ := exists_proj hsup' hinf'
  have hp₂v : ∀ v, p₂ v = v * (p₁ v)⁻¹ := by
    intro v
    have h1 := proj_compl_mem hsup hp₁1 hp₁2 v
    have : v = p₁ v * (v * (p₁ v)⁻¹) := by rw [mul_left_comm, mul_inv_cancel, mul_one]
    conv_lhs => rw [this]
    rw [map_mul, hp₂2 _ (hp₁0 v), hp₂1 _ h1, one_mul]
  have hdec : ∀ v, p₁ v * p₂ v = v := fun v => by
    rw [hp₂v, mul_left_comm, mul_inv_cancel, mul_one]
  let g₁ : ↥X →* ↥W₁ := (p₁.comp X.subtype).codRestrict W₁ (fun x => hp₁0 x)
  let g₂ : ↥X →* ↥W₂ := (p₂.comp X.subtype).codRestrict W₂ (fun x => hp₂0 x)
  have hinj₁ : Function.Injective g₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : p₁ (x : V) = 1 := congrArg Subtype.val hx
    have h2 : (x : V) = p₂ x := by
      have := hdec x
      rw [h1, one_mul] at this
      exact this.symm
    have h3 : (x : V) ∈ X ⊓ W₂ := ⟨x.2, h2 ▸ hp₂0 x⟩
    rw [hX₂, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have hinj₂ : Function.Injective g₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : p₂ (x : V) = 1 := congrArg Subtype.val hx
    have h2 : (x : V) = p₁ x := by
      have := hdec x
      rw [h1, mul_one] at this
      exact this.symm
    have h3 : (x : V) ∈ X ⊓ W₁ := ⟨x.2, h2 ▸ hp₁0 x⟩
    rw [hX₁, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have hbij₁ : Function.Bijective g₁ := hinj₁.bijective_of_nat_card_le hc₁.ge
  have hbij₂ : Function.Bijective g₂ := hinj₂.bijective_of_nat_card_le hc₂.ge
  let E₁ : ↥X ≃* ↥W₁ := MulEquiv.ofBijective g₁ hbij₁
  let E₂ : ↥X ≃* ↥W₂ := MulEquiv.ofBijective g₂ hbij₂
  refine ⟨E₂.symm.trans E₁, ?_⟩
  intro l hl₁ hl₂ hlX w w' hw
  set x : ↥X := E₂.symm w with hx
  have hxw : p₂ (x : V) = (w : V) := congrArg Subtype.val (E₂.apply_symm_apply w)
  have hlx : l (x : V) ∈ X := hlX x x.2
  have h1 : E₂ ⟨l x, hlx⟩ = w' := by
    apply Subtype.ext
    show p₂ (l x) = w'
    rw [proj_comm hsup' hp₂0 hp₂1 hp₂2 hl₂ hl₁, hxw, hw]
  have h2 : E₂.symm w' = ⟨l x, hlx⟩ := (MulEquiv.symm_apply_eq E₂).mpr h1.symm
  show ((E₁ (E₂.symm w') : ↥W₁) : V) = l ((E₁ (E₂.symm w) : ↥W₁) : V)
  rw [h2]
  show p₁ (l x) = l (p₁ x)
  exact proj_comm hsup hp₁0 hp₁1 hp₁2 hl₁ hl₂ x

end Graph

section Dichotomy

variable {V : Type} [CommGroup V] {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V} {s : MulAut V}

theorem tw_eq_iff {γ : MulAut V} {A B : Subgroup V} :
    tw γ A = B ↔ ∀ u, γ u ∈ B ↔ u ∈ A := by
  constructor
  · rintro rfl u
    simp [mem_tw]
  · intro h
    ext v
    rw [mem_tw]
    simpa using (h (γ⁻¹ v)).symm

theorem Ctx.false_of_equiv (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) (θ : ↥W₂ ≃* ↥W₁)
    (hθ : ∀ l ∈ L, ∀ w w' : ↥W₂, (w' : V) = l w →
      ((θ w' : ↥W₁) : V) = l ((θ w : ↥W₁) : V)) : False := by
  refine F.a4 ⟨c.sRes.trans θ, fun l => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext w
  refine hθ _ (c.cL l).2 (c.sRes w) (c.sRes (c.rL l w)) ?_
  simp [Ctx.sRes_apply, Ctx.rL_apply, Ctx.cL_apply, MulAut.mul_apply]

variable [Finite V]

theorem Ctx.inf_eq_bot (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) : W₁ ⊓ W₂ = ⊥ := by
  by_contra hne
  rcases c.hirr (W₁ ⊓ W₂) inf_le_left
    (fun l hl w hw => ⟨c.hW₁ l hl w hw.1, c.hW₂ l hl w hw.2⟩) with h | h
  · exact hne h
  · have hle : W₁ ≤ W₂ := inf_eq_left.mp h
    have heq : W₁ = W₂ := eq_of_le_of_rk_le c.hV hle (by rw [c.rk_W₂, c.hrk])
    refine c.false_of_equiv F (MulEquiv.subgroupCongr heq.symm) ?_
    intro l hl w w' hw
    simp [hw]

theorem Ctx.ne (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) : W₁ ≠ W₂ := by
  intro h
  have := c.inf_eq_bot F
  rw [← h, inf_idem] at this
  have h0 := c.hrk
  rw [this, rk_bot] at h0
  omega

theorem Ctx.tw_eq (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V} (hγ : γ ∈ Γ) :
    tw γ W₁ = W₁ ∨ tw γ W₁ = W₂ := by
  have hinf := c.inf_eq_bot F
  have hrk : rk (tw γ W₁) = 4 := (rk_tw γ W₁).trans c.hrk
  have h1 : tw γ W₁ ⊓ W₁ = ⊥ ∨ tw γ W₁ ⊓ W₁ = W₁ :=
    c.hirr (tw γ W₁ ⊓ W₁) inf_le_right
      (fun l hl w hw => ⟨c.tw_stable hγ hl hw.1, c.hW₁ l hl w hw.2⟩)
  have h2 : tw γ W₁ ⊓ W₂ = ⊥ ∨ tw γ W₁ ⊓ W₂ = W₂ := by
    have := c.tw_irred c.hs (tw γ W₁ ⊓ W₂) (by rw [← c.W₂_eq_tw]; exact inf_le_right)
      (fun l hl w hw => ⟨c.tw_stable hγ hl hw.1, c.hW₂ l hl w hw.2⟩)
    rwa [← c.W₂_eq_tw] at this
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exfalso
      have hc : Nat.card (tw γ W₁) = 16 := by
        rw [card_eq_two_pow c.hV, hrk]; norm_num
      obtain ⟨θ, hθ⟩ := exists_graph_equiv c.hsup hinf h1 h2 (hc.trans c.card_W₁.symm)
        (hc.trans c.card_W₂.symm)
      exact c.false_of_equiv F θ fun l hl w w' hw =>
        hθ l (c.hW₁ l hl) (c.hW₂ l hl) (fun x hx => c.tw_stable hγ hl hx) w w' hw
    · right
      exact (eq_of_le_of_rk_le c.hV (inf_eq_right.mp h2) (by rw [hrk, c.rk_W₂])).symm
  · left
    exact (eq_of_le_of_rk_le c.hV (inf_eq_right.mp h1) (by rw [hrk, c.hrk])).symm

theorem Ctx.stab_or_swap (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) :
    (γ ∈ stabSub W₁ ∧ γ ∈ stabSub W₂) ∨
      ((∀ u, γ u ∈ W₂ ↔ u ∈ W₁) ∧ (∀ u, γ u ∈ W₁ ↔ u ∈ W₂)) := by
  have hne := c.ne F
  have hγs : tw γ W₂ = tw (γ * s) W₁ := by rw [tw_mul, ← c.W₂_eq_tw]
  have h2 := c.tw_eq F (Γ.mul_mem hγ c.hs)
  rw [← hγs] at h2
  rcases c.tw_eq F hγ with h1 | h1
  · left
    refine ⟨fun u => tw_eq_iff.mp h1 u, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (tw_inj (h2.trans h1.symm)) (Ne.symm hne)
    · exact fun u => tw_eq_iff.mp h2 u
  · right
    refine ⟨tw_eq_iff.mp h1, ?_⟩
    rcases h2 with h2 | h2
    · exact tw_eq_iff.mp h2
    · exact absurd (tw_inj (h1.trans h2.symm)) hne

end Dichotomy

end CFSG.Quasithin.A6Amt
