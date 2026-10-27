module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinDef
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.A6Amt

section Counting

theorem exists_two_ne_one {G : Type*} [Group G] [Finite G] (h : 4 ≤ Nat.card G) :
    ∃ a b : G, a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := G)).mp (by omega)
  by_cases ha : a = 1
  · exact ⟨b, c, hbc, fun hb => hab (ha.trans hb.symm), fun hc => hac (ha.trans hc.symm)⟩
  · by_cases hb : b = 1
    · exact ⟨a, c, hac, ha, fun hc => hbc (hb.trans hc.symm)⟩
    · exact ⟨a, b, hab, ha, hb⟩

theorem card_le_two_mul_card_inf {G : Type*} [Group G] [Finite G] {A N : Subgroup G}
    (h : ∀ x ∈ A, x ∉ N → ∀ y ∈ A, y ∉ N → x⁻¹ * y ∈ N) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ N) := by
  have hmul := Subgroup.relIndex_mul_card (A ⊓ N) A
  rw [inf_eq_left.mpr (inf_le_left : A ⊓ N ≤ A)] at hmul
  have hidx : (A ⊓ N).relIndex A ≤ 2 := by
    by_cases hall : ∀ x ∈ A, x ∈ N
    · have : (A ⊓ N).relIndex A = 1 := by
        rw [Subgroup.relIndex_eq_one]
        exact fun x hx => ⟨hx, hall x hx⟩
      omega
    · push Not at hall
      obtain ⟨x, hxA, hxN⟩ := hall
      have hsurj : Function.Surjective
          (fun b : Bool => cond b (QuotientGroup.mk (⟨x, hxA⟩ : A))
            (QuotientGroup.mk (1 : A)) : Bool → A ⧸ (A ⊓ N).subgroupOf A) := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H y =>
          by_cases hy : (y : G) ∈ N
          · refine ⟨false, ?_⟩
            show (QuotientGroup.mk (1 : A) : A ⧸ (A ⊓ N).subgroupOf A) = QuotientGroup.mk y
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using hy
          · refine ⟨true, ?_⟩
            show (QuotientGroup.mk (⟨x, hxA⟩ : A) : A ⧸ (A ⊓ N).subgroupOf A) = QuotientGroup.mk y
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using (h x hxA hxN y y.2 hy)
      have := Nat.card_le_card_of_surjective _ hsurj
      rw [← Subgroup.index_eq_card, Nat.card_eq_fintype_card, Fintype.card_bool] at this
      exact this
  calc Nat.card A = (A ⊓ N).relIndex A * Nat.card ↥(A ⊓ N) := hmul.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ N) := Nat.mul_le_mul_right _ hidx

end Counting

section Projection

variable {V : Type*} [CommGroup V] {W₁ W₂ : Subgroup V}

theorem exists_proj (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥) :
    ∃ p : V →* V, (∀ v, p v ∈ W₁) ∧ (∀ w ∈ W₁, p w = w) ∧ (∀ w ∈ W₂, p w = 1) := by
  let φ : ↥W₁ × ↥W₂ →* V := W₁.subtype.coprod W₂.subtype
  have hφ : ∀ a b, φ (a, b) = (a : V) * b := fun a b => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker, hφ] at hab
    have h1 : (a : V) ∈ W₁ ⊓ W₂ := ⟨a.2, by
      rw [eq_inv_of_mul_eq_one_left hab]; exact W₂.inv_mem b.2⟩
    rw [hinf, Subgroup.mem_bot] at h1
    have h2 : (b : V) = 1 := by rw [h1, one_mul] at hab; exact hab
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top v)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hφ _ _⟩
  let e : ↥W₁ × ↥W₂ ≃* V := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ a b, e (a, b) = (a : V) * b := hφ
  refine ⟨W₁.subtype.comp ((MonoidHom.fst _ _).comp e.symm.toMonoidHom), fun v => ?_, ?_, ?_⟩
  · exact (e.symm v).1.2
  · intro w hw
    have : e.symm w = (⟨w, hw⟩, 1) := by
      rw [MulEquiv.symm_apply_eq, he]; simp
    simp [this]
  · intro w hw
    have : e.symm w = (1, ⟨w, hw⟩) := by
      rw [MulEquiv.symm_apply_eq, he]; simp
    simp [this]

theorem proj_compl_mem (hsup : W₁ ⊔ W₂ = ⊤) {p : V →* V} (hp1 : ∀ w ∈ W₁, p w = w)
    (hp2 : ∀ w ∈ W₂, p w = 1) (v : V) : v * (p v)⁻¹ ∈ W₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top v)
  rw [map_mul, hp1 a ha, hp2 b hb, mul_one, mul_comm a b, mul_inv_cancel_right]
  exact hb

theorem proj_comm (hsup : W₁ ⊔ W₂ = ⊤) {p : V →* V} (hp0 : ∀ v, p v ∈ W₁)
    (hp1 : ∀ w ∈ W₁, p w = w) (hp2 : ∀ w ∈ W₂, p w = 1) {γ : MulAut V}
    (h₁ : ∀ w ∈ W₁, γ w ∈ W₁) (h₂ : ∀ w ∈ W₂, γ w ∈ W₂) (v : V) : p (γ v) = γ (p v) := by
  have hv : γ v = γ (p v) * γ (v * (p v)⁻¹) := by
    rw [← map_mul, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hv, map_mul, hp1 _ (h₁ _ (hp0 v)), hp2 _ (h₂ _ (proj_compl_mem hsup hp1 hp2 v)), mul_one]

end Projection

section Ranks

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem rk_eq_of_iff (e : V ≃* V) {A B : Subgroup V} (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    rk A = rk B := by
  unfold rk
  exact congrArg (padicValNat 2) (Nat.card_congr (e.toEquiv.subtypeEquiv h))

theorem rk_sup_of_inf_eq_bot {A B : Subgroup V} (h : A ⊓ B = ⊥) :
    rk ↥(A ⊔ B) = rk A + rk B := by
  have := rk_sup_add_rk_inf A B
  rw [h, rk_bot] at this
  omega

theorem rk_eq_add_of_decomp {W₁ W₂ : Subgroup V} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥) :
    rk V = rk W₁ + rk W₂ := by
  rw [← rk_top, ← hsup]
  exact rk_sup_of_inf_eq_bot hinf

theorem rk_fixV_split {W₁ W₂ : Subgroup V} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
    {γ : MulAut V} (h₁ : ∀ w ∈ W₁, γ w ∈ W₁) (h₂ : ∀ w ∈ W₂, γ w ∈ W₂) :
    rk (fixV (Subgroup.zpowers γ)) =
      rk ↥(W₁ ⊓ fixV (Subgroup.zpowers γ)) + rk ↥(W₂ ⊓ fixV (Subgroup.zpowers γ)) := by
  obtain ⟨p, hp0, hp1, hp2⟩ := exists_proj hsup hinf
  have hsplit : (W₁ ⊓ fixV (Subgroup.zpowers γ)) ⊔ (W₂ ⊓ fixV (Subgroup.zpowers γ)) =
      fixV (Subgroup.zpowers γ) := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun v hv => ?_
    have hpv : p v ∈ fixV (Subgroup.zpowers γ) := by
      rw [mem_fixV_zpowers_iff, ← proj_comm hsup hp0 hp1 hp2 h₁ h₂ v, mem_fixV_zpowers_iff.mp hv]
    have hq : v * (p v)⁻¹ ∈ fixV (Subgroup.zpowers γ) :=
      Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hpv)
    have : v = p v * (v * (p v)⁻¹) := by rw [mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
    exact Subgroup.mul_mem_sup ⟨hp0 v, hpv⟩ ⟨proj_compl_mem hsup hp1 hp2 v, hq⟩
  have hdisj : (W₁ ⊓ fixV (Subgroup.zpowers γ)) ⊓ (W₂ ⊓ fixV (Subgroup.zpowers γ)) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf inf_le_left inf_le_left
  have := rk_sup_of_inf_eq_bot hdisj
  rw [hsplit] at this
  exact this

theorem rk_fixV_res {W : Subgroup V} {γ : MulAut V} (h : γ ∈ stabSub W) :
    A6Rank (resHom W ⟨γ, h⟩) + rk ↥(W ⊓ fixV (Subgroup.zpowers γ)) = rk ↥W := by
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers (resHom W ⟨γ, h⟩)))
  have h2 : (fixV (Subgroup.zpowers (resHom W ⟨γ, h⟩))).map W.subtype =
      W ⊓ fixV (Subgroup.zpowers γ) := by
    ext v
    simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subgroup.mem_inf, mem_fixV_zpowers_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, congrArg (fun w : W => (w : V)) hu⟩
    · rintro ⟨hvW, hv⟩
      exact ⟨⟨v, hvW⟩, Subtype.ext hv, rfl⟩
  have h3 : rk (fixV (Subgroup.zpowers (resHom W ⟨γ, h⟩))) =
      rk ↥(W ⊓ fixV (Subgroup.zpowers γ)) := by
    unfold rk
    rw [← h2, Subgroup.card_map_of_injective W.subtype_injective]
  unfold A6Rank
  omega

theorem rk_le_rkIdx_of_swap {W₁ W₂ : Subgroup V} (hinf : W₁ ⊓ W₂ = ⊥) {f : MulAut V}
    (hf : ∀ w ∈ W₂, f w ∈ W₁) : rk W₂ ≤ rkIdx (fixV (Subgroup.zpowers f)) := by
  have hF : fixV (Subgroup.zpowers f) ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : f x = x := mem_fixV_zpowers_iff.mp hx.1
    have : x ∈ W₁ ⊓ W₂ := ⟨hx1 ▸ hf x hx.2, hx.2⟩
    rw [hinf] at this
    exact this
  have h1 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers f)) W₂
  rw [hF, rk_bot] at h1
  have h2 : rk ↥(fixV (Subgroup.zpowers f) ⊔ W₂) ≤ rk V := by
    have := rk_mono (G := V) (le_top : fixV (Subgroup.zpowers f) ⊔ W₂ ≤ ⊤)
    rwa [rk_top] at this
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers f))
  omega

omit [Finite V] in
theorem rk_inf_fixV_twist {W₁ W₂ : Subgroup V} {s : MulAut V} (hs : ∀ w : V, w ∈ W₂ ↔ s⁻¹ w ∈ W₁)
    (γ : MulAut V) :
    rk ↥(W₂ ⊓ fixV (Subgroup.zpowers γ)) =
      rk ↥(W₁ ⊓ fixV (Subgroup.zpowers (s⁻¹ * γ * s))) := by
  refine rk_eq_of_iff (s⁻¹ : MulAut V) fun x => ?_
  simp only [Subgroup.mem_inf, mem_fixV_zpowers_iff, hs x]
  refine and_congr_right fun _ => ?_
  have : (s⁻¹ * γ * s) (s⁻¹ x) = s⁻¹ (γ x) := by
    simp [MulAut.mul_apply]
  rw [this]
  exact ⟨fun h => by rw [h], fun h => (s⁻¹ : MulAut V).injective h⟩

end Ranks

end CFSG.Quasithin.A6Amt
