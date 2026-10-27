module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open

section DirectSum

variable {V : Type} [CommGroup V] {W₁ W₂ : Subgroup V}

theorem eq_of_mul_eq_mul (hinf : W₁ ⊓ W₂ = ⊥) {a b c d : V} (ha : a ∈ W₁) (hc : c ∈ W₁)
    (hb : b ∈ W₂) (hd : d ∈ W₂) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : a * c⁻¹ = d * b⁻¹ := by
    calc a * c⁻¹ = (a * b) * (b⁻¹ * c⁻¹) := by group
      _ = (c * d) * (b⁻¹ * c⁻¹) := by rw [h]
      _ = (d * c) * (c⁻¹ * b⁻¹) := by rw [mul_comm c d, mul_comm b⁻¹ c⁻¹]
      _ = d * b⁻¹ := by group
  have hmem : a * c⁻¹ ∈ W₁ ⊓ W₂ :=
    ⟨W₁.mul_mem ha (W₁.inv_mem hc), h1 ▸ W₂.mul_mem hd (W₂.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have hac : a = c := mul_inv_eq_one.1 hmem
  refine ⟨hac, ?_⟩
  rw [hac] at h
  exact mul_left_cancel h

variable (hsum : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)

@[expose] noncomputable def sumEquiv : ↥W₁ × ↥W₂ ≃* V :=
  MulEquiv.ofBijective (W₁.subtype.coprod W₂.subtype) ⟨by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [MonoidHom.coprod_apply, Subgroup.coe_subtype] at h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul hinf a.2 c.2 b.2 d.2 h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2), by
    intro v
    have hv : v ∈ W₁ ⊔ W₂ := by rw [hsum]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩

@[expose] noncomputable def proj₁ : V →* V :=
  W₁.subtype.comp ((MonoidHom.fst _ _).comp (sumEquiv hsum hinf).symm.toMonoidHom)

@[expose] noncomputable def proj₂ : V →* V :=
  W₂.subtype.comp ((MonoidHom.snd _ _).comp (sumEquiv hsum hinf).symm.toMonoidHom)

theorem proj₁_mem (v : V) : proj₁ hsum hinf v ∈ W₁ := ((sumEquiv hsum hinf).symm v).1.2

theorem proj₂_mem (v : V) : proj₂ hsum hinf v ∈ W₂ := ((sumEquiv hsum hinf).symm v).2.2

theorem proj₁_mul_proj₂ (v : V) : proj₁ hsum hinf v * proj₂ hsum hinf v = v :=
  (sumEquiv hsum hinf).apply_symm_apply v

theorem proj_eq_of_mul {a b : V} (ha : a ∈ W₁) (hb : b ∈ W₂) :
    proj₁ hsum hinf (a * b) = a ∧ proj₂ hsum hinf (a * b) = b :=
  eq_of_mul_eq_mul hinf (proj₁_mem hsum hinf _) ha (proj₂_mem hsum hinf _) hb
    (proj₁_mul_proj₂ hsum hinf (a * b))

theorem proj₁_of_mem₁ {a : V} (ha : a ∈ W₁) : proj₁ hsum hinf a = a := by
  simpa using (proj_eq_of_mul hsum hinf ha (W₂.one_mem)).1

theorem proj₂_of_mem₁ {a : V} (ha : a ∈ W₁) : proj₂ hsum hinf a = 1 := by
  simpa using (proj_eq_of_mul hsum hinf ha (W₂.one_mem)).2

theorem proj₁_of_mem₂ {b : V} (hb : b ∈ W₂) : proj₁ hsum hinf b = 1 := by
  simpa using (proj_eq_of_mul hsum hinf (W₁.one_mem) hb).1

theorem proj₂_of_mem₂ {b : V} (hb : b ∈ W₂) : proj₂ hsum hinf b = b := by
  simpa using (proj_eq_of_mul hsum hinf (W₁.one_mem) hb).2

theorem proj_apply_of_stab {g : MulAut V} (h₁ : ∀ w ∈ W₁, g w ∈ W₁) (h₂ : ∀ w ∈ W₂, g w ∈ W₂)
    (v : V) : proj₁ hsum hinf (g v) = g (proj₁ hsum hinf v) ∧
      proj₂ hsum hinf (g v) = g (proj₂ hsum hinf v) := by
  have e : g v = g (proj₁ hsum hinf v) * g (proj₂ hsum hinf v) := by
    rw [← map_mul, proj₁_mul_proj₂]
  rw [e]
  exact proj_eq_of_mul hsum hinf (h₁ _ (proj₁_mem hsum hinf v)) (h₂ _ (proj₂_mem hsum hinf v))

end DirectSum

section Iso

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}

theorem secIsoL_of_equiv (hinv₁ : ∀ k ∈ L, ∀ w ∈ W₁, k w ∈ W₁)
    (hinv₂ : ∀ k ∈ L, ∀ w ∈ W₂, k w ∈ W₂) (e : ↥W₁ ≃* ↥W₂)
    (he : ∀ (k : ↥L) (w : ↥W₁), ((e ⟨(k : MulAut V) w, hinv₁ k k.2 w w.2⟩ : ↥W₂) : V) =
      (k : MulAut V) (e w)) : SecIsoL L W₁ ⊥ W₂ ⊥ := by
  have hbot : ∀ (k : ↥L), ∀ z ∈ (⊥ : Subgroup V), (k : MulAut V) z ∈ (⊥ : Subgroup V) := by
    intro k z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  refine ⟨fun k => ⟨k, rfl⟩, bot_le, bot_le, fun k u hu => hinv₁ k k.2 u hu, hbot,
    fun (k : ↥L) m hm => hinv₂ k k.2 m hm, hbot,
    (QuotientGroup.mk' ((⊥ : Subgroup V).subgroupOf W₂)).comp e.toMonoidHom, ?_, ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp e.surjective
  · intro u
    change (QuotientGroup.mk (e u) : ↥W₂ ⧸ (⊥ : Subgroup V).subgroupOf W₂) = 1 ↔ (u : V) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have : e u = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    · intro h
      have : u = 1 := Subtype.ext h
      rw [this, map_one]
      rfl
  · intro (γ : ↥L) (u : ↥W₁) (m : ↥W₂) hu hm hum
    have hm2 : (m : V) ∈ W₂ := m.2
    have hum2 : (QuotientGroup.mk (e u) : ↥W₂ ⧸ (⊥ : Subgroup V).subgroupOf W₂) =
        QuotientGroup.mk (⟨m, hm2⟩ : ↥W₂) := hum
    have hum' : e u = ⟨m, hm2⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hum2
      exact inv_mul_eq_one.1 (Subtype.ext hum2)
    have key : e ⟨((γ : ↥L) : MulAut V) u, hinv₁ γ γ.2 u u.2⟩ =
        ⟨((γ : ↥L) : MulAut V) (m : V), hinv₂ γ γ.2 _ hm2⟩ := by
      apply Subtype.ext
      rw [he γ u, hum']
    exact congrArg (fun x : ↥W₂ => (QuotientGroup.mk x : ↥W₂ ⧸ (⊥ : Subgroup V).subgroupOf W₂))
      key

theorem equiv_of_secIsoL (h : SecIsoL L W₁ ⊥ W₂ ⊥) :
    ∃ e : ↥W₁ ≃* ↥W₂, ∀ (k : ↥L) (w : ↥W₁) (hw : (k : MulAut V) w ∈ W₁)
      (hw' : (k : MulAut V) (e w) ∈ W₂),
        e ⟨(k : MulAut V) w, hw⟩ = ⟨(k : MulAut V) (e w), hw'⟩ := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  set q : ↥W₂ ⧸ (⊥ : Subgroup V).subgroupOf W₂ ≃* ↥W₂ :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf W₂)).trans
      QuotientGroup.quotientBot with hq
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  set e : ↥W₁ ≃* ↥W₂ := (MulEquiv.ofBijective β ⟨hinj, hβs⟩).trans q with he
  have hqmk : ∀ m : ↥W₂, q (QuotientGroup.mk m) = m := fun m => rfl
  have hmkq : ∀ x, QuotientGroup.mk (q x) = x := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  refine ⟨e, fun k w hw hw' => ?_⟩
  have h1 : β w = QuotientGroup.mk (e w) := (hmkq (β w)).symm
  have h2 := hβe k w (e w) hw hw' h1
  exact (congrArg q h2).trans (hqmk ⟨_, hw'⟩)

end Iso

end CFSG.Quasithin.InternalSec
