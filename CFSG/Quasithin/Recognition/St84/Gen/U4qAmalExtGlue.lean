module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtPair
import CFSG.Monster.B.Recog.GenericIndexTwo
import CFSG.Quasithin.Background.F1AmalgamRestrict

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

section Join

variable {G : Type} [Group G]

theorem mem_or_mul_inv_mem_of_mem_sup_zpowers_u4Glue {H : Subgroup G} {τ : G}
    (hτ : τ ∈ Subgroup.normalizer (H : Set G)) (hsq : τ ^ 2 ∈ H) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers τ) : x ∈ H ∨ x * τ⁻¹ ∈ H := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H _
    (Subgroup.zpowers_le.mpr hτ)] at hx
  obtain ⟨a, ha, t, ht, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hsq' : τ ^ (2 : ℤ) ∈ H := by rwa [zpow_two, ← pow_two]
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    exact H.mul_mem ha (H.zpow_mem hsq' j)
  · right
    rw [zpow_add, zpow_mul, zpow_one, mul_assoc, mul_inv_cancel_right]
    exact H.mul_mem ha (H.zpow_mem hsq' j)

theorem index_range_inclusion_sup_zpowers_u4Glue {H : Subgroup G} {τ : G}
    (hτ : τ ∈ Subgroup.normalizer (H : Set G)) (hτH : τ ∉ H) (hsq : τ ^ 2 ∈ H) :
    (Subgroup.inclusion (le_sup_left : H ≤ H ⊔ Subgroup.zpowers τ)).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨τ, Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)⟩, ?_, fun b => ?_⟩
  · rintro ⟨a, ha⟩
    have e : (a : G) = τ := congrArg Subtype.val ha
    exact hτH (e ▸ a.2)
  · rcases mem_or_mul_inv_mem_of_mem_sup_zpowers_u4Glue hτ hsq b.2 with hb | hb
    · exact Or.inr ⟨⟨b, hb⟩, rfl⟩
    · refine Or.inl ⟨⟨(b : G) * τ, ?_⟩, rfl⟩
      have hm := H.mul_mem hb hsq
      rwa [pow_two, mul_assoc, inv_mul_cancel_left] at hm

end Join

section AmalgamIso

variable {X Y : Type} [Group X] [Group Y] {G₁ G₂ : Subgroup X} {M₁ M₂ : Subgroup Y}
  (Φ : (RankTwoAmalgam.ofSubgroups G₁ G₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))

theorem coe_φ1_eq_coe_φ2_u4Glue {x : X} (hx : x ∈ G₁ ⊓ G₂) :
    Subtype.val (Φ.φ1 ⟨x, (Subgroup.mem_inf.mp hx).1⟩) =
      Subtype.val (Φ.φ2 ⟨x, (Subgroup.mem_inf.mp hx).2⟩) :=
  (congrArg Subtype.val (Φ.comm1 ⟨x, hx⟩)).symm.trans (congrArg Subtype.val (Φ.comm2 ⟨x, hx⟩))

theorem mem_of_coe_φ1_mem_u4Glue (a : ↥G₁) (ha : Subtype.val (Φ.φ1 a) ∈ M₂) : (a : X) ∈ G₂ := by
  obtain ⟨g, hg⟩ := Φ.φ12.surjective ⟨Subtype.val (Φ.φ1 a), Subtype.property (Φ.φ1 a), ha⟩
  have hg' := congrArg Subtype.val hg
  have h1 : Φ.φ1 ((RankTwoAmalgam.ofSubgroups G₁ G₂).α1 g) = Φ.φ1 a :=
    (Φ.comm1 g).symm.trans (Subtype.ext hg')
  rw [← Φ.φ1.injective h1]
  exact (Subgroup.mem_inf.mp g.2).2

end AmalgamIso

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem center_hypSU_eq_bot_u4Glue : Subgroup.center (hypSU h 2 0) = ⊥ := by
  have := isSimpleGroup_hypSU h
  obtain ⟨a, -, b, -, hab⟩ := exists_radQ_ne_comm h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (hypSU h 2 0)) with h0 | h0
  · exact h0
  · exact absurd (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm hab

theorem eq_one_of_commute_parP_parP2_u4Glue {z : hypSU h 2 0}
    (h1 : ∀ x ∈ parP h, z * x = x * z) (h2 : ∀ x ∈ parP2 h, z * x = x * z) : z = 1 := by
  have hle : parP h ⊔ parP2 h ≤ Subgroup.centralizer {z} :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h1 x hx).symm)
      fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h2 x hx).symm
  rw [(isCoatom_parP h).sup_eq_top_of_ne (isCoatom_parP2 h) (parP_ne_parP2 h)] at hle
  have hz : z ∈ Subgroup.center (hypSU h 2 0) := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rwa [center_hypSU_eq_bot_u4Glue h, Subgroup.mem_bot] at hz

theorem left_inl_mul_inr_u4Glue (b : hypSU h 2 0) :
    (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1) :
      u4ExtGroup h).left = b := by
  simp

theorem right_inl_mul_inr_u4Glue (b : hypSU h 2 0) :
    (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1) :
      u4ExtGroup h).right = Multiplicative.ofAdd 1 := by
  simp

theorem left_inl_mul_inl_mul_inr_u4Glue (c b : hypSU h 2 0) :
    (SemidirectProduct.inl c *
        (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1)) :
      u4ExtGroup h).left = c * b := by
  simp

theorem conj_inl_mul_inr_u4Glue (b x : hypSU h 2 0) :
    (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1) : u4ExtGroup h) *
        SemidirectProduct.inl x *
        (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ =
      SemidirectProduct.inl (b * u4FieldInvol h x * b⁻¹) := by
  rw [conj_inl_u4Ext, left_inl_mul_inr_u4Glue, right_inl_mul_inr_u4Glue,
    u4FieldInvolHom_ofAdd_one]

theorem inl_mul_inr_mul_self_u4Glue (b : hypSU h 2 0) :
    (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1) : u4ExtGroup h) *
        (SemidirectProduct.inl b * SemidirectProduct.inr (Multiplicative.ofAdd 1)) =
      SemidirectProduct.inl (b * u4FieldInvol h b) := by
  ext
  · simp [u4FieldInvolHom_ofAdd_one]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul]
    decide

theorem commute_inv_mul_sq_u4Glue {G : Type} [Group G] {P : Subgroup G} {τ : G}
    (hτ : τ ∈ Subgroup.normalizer (P : Set G)) (hsq : τ ^ 2 ∈ P) {X : Subgroup (hypSU h 2 0)}
    (φ : ↥P ≃* ↥X) {b₀ : hypSU h 2 0}
    (hθ : ∀ x y : ↥P, (y : G) = τ * x * τ⁻¹ →
      ((φ y : ↥X) : hypSU h 2 0) = b₀ * u4FieldInvol h (φ x) * b₀⁻¹)
    {g : hypSU h 2 0} (hg : g ∈ X) :
    (b₀ * u4FieldInvol h b₀)⁻¹ * ((φ ⟨τ ^ 2, hsq⟩ : ↥X) : hypSU h 2 0) * g =
      g * ((b₀ * u4FieldInvol h b₀)⁻¹ * ((φ ⟨τ ^ 2, hsq⟩ : ↥X) : hypSU h 2 0)) := by
  obtain ⟨x, hx⟩ := φ.surjective ⟨g, hg⟩
  have hxg : ((φ x : ↥X) : hypSU h 2 0) = g := congrArg Subtype.val hx
  let y : ↥P := ⟨τ * x * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτ x).mp x.2⟩
  let z : ↥P := ⟨τ * y * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτ y).mp y.2⟩
  have hz : z = ⟨τ ^ 2, hsq⟩ * x * (⟨τ ^ 2, hsq⟩ : ↥P)⁻¹ := Subtype.ext (by
    show τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = τ ^ 2 * x * (τ ^ 2)⁻¹
    simp only [pow_two, mul_inv_rev, mul_assoc])
  have h2 := hθ y z rfl
  rw [hz, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hθ x y rfl, hxg, map_mul, map_mul, map_inv, u4FieldInvol_apply_apply] at h2
  set T := ((φ ⟨τ ^ 2, hsq⟩ : ↥X) : hypSU h 2 0)
  calc (b₀ * u4FieldInvol h b₀)⁻¹ * T * g
      = (b₀ * u4FieldInvol h b₀)⁻¹ * (T * g * T⁻¹) * T := by group
    _ = (b₀ * u4FieldInvol h b₀)⁻¹ *
          (b₀ * (u4FieldInvol h b₀ * g * (u4FieldInvol h b₀)⁻¹) * b₀⁻¹) * T := by rw [h2]
    _ = g * ((b₀ * u4FieldInvol h b₀)⁻¹ * T) := by group

theorem exists_mulEquiv_sup_zpowers_u4Glue {G : Type} [Group G] {P : Subgroup G} {τ : G}
    (hτ : τ ∈ Subgroup.normalizer (P : Set G)) (hτP : τ ∉ P) (hsq : τ ^ 2 ∈ P)
    {X : Subgroup (hypSU h 2 0)} (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) (φ : ↥P ≃* ↥X)
    {b₀ : hypSU h 2 0} (hb₀ : b₀ ∈ X)
    (hθ : ∀ x y : ↥P, (y : G) = τ * x * τ⁻¹ →
      ((φ y : ↥X) : hypSU h 2 0) = b₀ * u4FieldInvol h (φ x) * b₀⁻¹)
    (hφτ : ((φ ⟨τ ^ 2, hsq⟩ : ↥X) : hypSU h 2 0) = b₀ * u4FieldInvol h b₀) :
    ∃ ψ : ↥(P ⊔ Subgroup.zpowers τ) ≃* ↥(u4ExtLift h X hX),
      (∀ (x : G) (hx : x ∈ P ⊔ Subgroup.zpowers τ) (hxP : x ∈ P),
        (ψ ⟨x, hx⟩ : u4ExtGroup h) = SemidirectProduct.inl ((φ ⟨x, hxP⟩ : ↥X) : hypSU h 2 0)) ∧
      ∀ (x : G) (hx : x ∈ P ⊔ Subgroup.zpowers τ) (hxP : x * τ⁻¹ ∈ P),
        (ψ ⟨x, hx⟩ : u4ExtGroup h) =
          SemidirectProduct.inl ((φ ⟨x * τ⁻¹, hxP⟩ : ↥X) : hypSU h 2 0) *
            (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1)) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  let ι₂ : ↥P →* ↥(u4ExtLift h X hX) :=
    ((SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h).comp
      (X.subtype.comp φ.toMonoidHom)).codRestrict _ fun a => (inl_mem_u4ExtLift h _).mpr (φ a).2
  have hinj₂ : Function.Injective ι₂ := by
    intro a b hab
    have e : (SemidirectProduct.inl ((φ a : ↥X) : hypSU h 2 0) : u4ExtGroup h) =
        SemidirectProduct.inl ((φ b : ↥X) : hypSU h 2 0) := congrArg Subtype.val hab
    exact φ.injective (Subtype.ext (SemidirectProduct.inl_injective e))
  have hidx₂ : ι₂.range.index = 2 := by
    have hc := ι₂.range.card_mul_index
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₂).toEquiv, Nat.card_congr φ.toEquiv,
      card_u4ExtLift] at hc
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc
  let s₁ : ↥(P ⊔ Subgroup.zpowers τ) := ⟨τ, Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)⟩
  let s₂ : ↥(u4ExtLift h X hX) :=
    ⟨SemidirectProduct.inl b₀, (inl_mem_u4ExtLift h b₀).mpr hb₀⟩ *
      ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), inr_mem_u4ExtLift h _⟩
  have hs₁ : s₁ ∉ (Subgroup.inclusion (le_sup_left : P ≤ P ⊔ Subgroup.zpowers τ)).range := by
    rintro ⟨a, ha⟩
    have e : (a : G) = τ := congrArg Subtype.val ha
    exact hτP (e ▸ a.2)
  have hs₂ : s₂ ∉ ι₂.range := by
    rintro ⟨a, ha⟩
    have e : (SemidirectProduct.inl ((φ a : ↥X) : hypSU h 2 0) : u4ExtGroup h).right =
        (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1) :
          u4ExtGroup h).right :=
      congrArg (fun c : ↥(u4ExtLift h X hX) => (c : u4ExtGroup h).right) ha
    rw [SemidirectProduct.right_inl, right_inl_mul_inr_u4Glue] at e
    exact absurd e (by decide)
  let σA : ↥P → ↥P := fun a => ⟨τ * a * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτ a).mp a.2⟩
  have hσ₂ : ∀ a, s₂ * ι₂ a * s₂⁻¹ = ι₂ (σA a) := fun a => Subtype.ext (by
    show (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1) :
        u4ExtGroup h) * SemidirectProduct.inl ((φ a : ↥X) : hypSU h 2 0) *
        (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ =
      SemidirectProduct.inl ((φ (σA a) : ↥X) : hypSU h 2 0)
    rw [conj_inl_mul_inr_u4Glue, hθ a (σA a) rfl])
  have hτ₂ : s₂ * s₂ = ι₂ ⟨τ ^ 2, hsq⟩ := Subtype.ext (by
    show (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1) :
        u4ExtGroup h) *
        (SemidirectProduct.inl b₀ * SemidirectProduct.inr (Multiplicative.ofAdd 1)) =
      SemidirectProduct.inl ((φ ⟨τ ^ 2, hsq⟩ : ↥X) : hypSU h 2 0)
    rw [inl_mul_inr_mul_self_u4Glue, hφτ])
  obtain ⟨e, he, hes⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq
    (Subgroup.inclusion (le_sup_left : P ≤ P ⊔ Subgroup.zpowers τ)) ι₂
    (Subgroup.inclusion_injective _) hinj₂ (index_range_inclusion_sup_zpowers_u4Glue hτ hτP hsq)
    hidx₂ hs₁ hs₂ σA ⟨τ ^ 2, hsq⟩ (fun _ => rfl) hσ₂ (Subtype.ext (pow_two τ).symm) hτ₂
  refine ⟨e, fun x hx hxP => congrArg Subtype.val (he ⟨x, hxP⟩), fun x hx hxP => ?_⟩
  have e1 : (⟨x, hx⟩ : ↥(P ⊔ Subgroup.zpowers τ)) =
      Subgroup.inclusion le_sup_left ⟨x * τ⁻¹, hxP⟩ * s₁ :=
    Subtype.ext (inv_mul_cancel_right x τ).symm
  rw [e1, map_mul, he, hes]
  rfl

theorem isU4ExtTwo_of_amalgamIso_of_conj {G : Type} [Group G] [Finite G] {m : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData 2 m K) {P1 P2 : Subgroup G} {τ : G}
    (Φ : (RankTwoAmalgam.ofSubgroups P1 P2).Iso
      (RankTwoAmalgam.ofSubgroups (parP h) (parP2 h)))
    (hτ1 : τ ∈ Subgroup.normalizer (P1 : Set G)) (hτ2 : τ ∈ Subgroup.normalizer (P2 : Set G))
    (hτP1 : τ ∉ P1) (hτP2 : τ ∉ P2) (hτsq : τ ^ 2 ∈ P1 ⊓ P2)
    (hinf : (P1 ⊔ Subgroup.zpowers τ) ⊓ (P2 ⊔ Subgroup.zpowers τ) =
      (P1 ⊓ P2) ⊔ Subgroup.zpowers τ)
    {b₀ : hypSU h 2 0} (hb₀ : b₀ ∈ hypBorel h 2 0)
    (hθ1 : ∀ x y : ↥P1, (y : G) = τ * x * τ⁻¹ →
      Subtype.val (Φ.φ1 y) = b₀ * u4FieldInvol h (Subtype.val (Φ.φ1 x)) * b₀⁻¹)
    (hθ2 : ∀ x y : ↥P2, (y : G) = τ * x * τ⁻¹ →
      Subtype.val (Φ.φ2 y) = b₀ * u4FieldInvol h (Subtype.val (Φ.φ2 x)) * b₀⁻¹) :
    IsU4ExtTwo m
      (RankTwoAmalgam.ofSubgroups (P1 ⊔ Subgroup.zpowers τ) (P2 ⊔ Subgroup.zpowers τ)) := by
  have hb : b₀ ∈ parP h ⊓ parP2 h := by
    rw [parP_inf_parP2_eq_u4 h]
    exact hb₀
  have hsq1 := (Subgroup.mem_inf.mp hτsq).1
  have hsq2 := (Subgroup.mem_inf.mp hτsq).2
  let φ₁ : ↥P1 ≃* ↥(parP h) := Φ.φ1
  let φ₂ : ↥P2 ≃* ↥(parP2 h) := Φ.φ2
  have hθ₁ : ∀ x y : ↥P1, (y : G) = τ * x * τ⁻¹ →
      ((φ₁ y : ↥(parP h)) : hypSU h 2 0) = b₀ * u4FieldInvol h (φ₁ x) * b₀⁻¹ := hθ1
  have hθ₂ : ∀ x y : ↥P2, (y : G) = τ * x * τ⁻¹ →
      ((φ₂ y : ↥(parP2 h)) : hypSU h 2 0) = b₀ * u4FieldInvol h (φ₂ x) * b₀⁻¹ := hθ2
  have h12 : ∀ (x : G) (hx : x ∈ P1 ⊓ P2),
      ((φ₁ ⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥(parP h)) : hypSU h 2 0) =
        ((φ₂ ⟨x, (Subgroup.mem_inf.mp hx).2⟩ : ↥(parP2 h)) : hypSU h 2 0) :=
    fun _ hx => coe_φ1_eq_coe_φ2_u4Glue Φ hx
  have h2 : ∀ a : ↥P1, ((φ₁ a : ↥(parP h)) : hypSU h 2 0) ∈ parP2 h → (a : G) ∈ P2 :=
    mem_of_coe_φ1_mem_u4Glue Φ
  have hz := eq_one_of_commute_parP_parP2_u4Glue h
    (z := (b₀ * u4FieldInvol h b₀)⁻¹ * ((φ₁ ⟨τ ^ 2, hsq1⟩ : ↥(parP h)) : hypSU h 2 0))
    (fun x hx => commute_inv_mul_sq_u4Glue h hτ1 hsq1 φ₁ hθ₁ hx)
    (fun x hx => by
      rw [h12 _ hτsq]
      exact commute_inv_mul_sq_u4Glue h hτ2 hsq2 φ₂ hθ₂ hx)
  have hT1 : ((φ₁ ⟨τ ^ 2, hsq1⟩ : ↥(parP h)) : hypSU h 2 0) = b₀ * u4FieldInvol h b₀ :=
    (inv_mul_eq_one.mp hz).symm
  have hT2 : ((φ₂ ⟨τ ^ 2, hsq2⟩ : ↥(parP2 h)) : hypSU h 2 0) = b₀ * u4FieldInvol h b₀ :=
    (h12 _ hτsq).symm.trans hT1
  obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := exists_mulEquiv_sup_zpowers_u4Glue h hτ1 hτP1 hsq1
    (u4FieldInvol_mem_parP_iff h) φ₁ (Subgroup.mem_inf.mp hb).1 hθ₁ hT1
  obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := exists_mulEquiv_sup_zpowers_u4Glue h hτ2 hτP2 hsq2
    (u4FieldInvol_mem_parP2_iff h) φ₂ (Subgroup.mem_inf.mp hb).2 hθ₂ hT2
  have hτ12 : τ ∈ Subgroup.normalizer ((P1 ⊓ P2 : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun n =>
      and_congr (Subgroup.mem_normalizer_iff.mp hτ1 n) (Subgroup.mem_normalizer_iff.mp hτ2 n)
  have hag : ∀ (x : G) (hx₁ : x ∈ P1 ⊔ Subgroup.zpowers τ) (hx₂ : x ∈ P2 ⊔ Subgroup.zpowers τ),
      (ψ₁ ⟨x, hx₁⟩ : u4ExtGroup h) = (ψ₂ ⟨x, hx₂⟩ : u4ExtGroup h) := by
    intro x hx₁ hx₂
    have hx : x ∈ (P1 ⊓ P2) ⊔ Subgroup.zpowers τ := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hx₁, hx₂⟩
    rcases mem_or_mul_inv_mem_of_mem_sup_zpowers_u4Glue hτ12 hτsq hx with hb' | hb'
    · rw [hψ₁ x hx₁ (Subgroup.mem_inf.mp hb').1, hψ₂ x hx₂ (Subgroup.mem_inf.mp hb').2, h12 x hb']
    · rw [hψ₁' x hx₁ (Subgroup.mem_inf.mp hb').1, hψ₂' x hx₂ (Subgroup.mem_inf.mp hb').2,
        h12 _ hb']
  have hback : ∀ x : ↥(P1 ⊔ Subgroup.zpowers τ), (ψ₁ x : u4ExtGroup h) ∈ u4ExtParP2 h →
      (x : G) ∈ P2 ⊔ Subgroup.zpowers τ := by
    rintro ⟨x, hx⟩ hψ
    rcases mem_or_mul_inv_mem_of_mem_sup_zpowers_u4Glue hτ1 hsq1 hx with h1 | h1
    · rw [hψ₁ x hx h1] at hψ
      exact Subgroup.mem_sup_left (h2 ⟨x, h1⟩ ((inl_mem_u4ExtLift h _).mp hψ))
    · rw [hψ₁' x hx h1] at hψ
      have hl := mem_u4ExtLift.mp hψ
      rw [left_inl_mul_inl_mul_inr_u4Glue] at hl
      have hc := (parP2 h).mul_mem hl ((parP2 h).inv_mem (Subgroup.mem_inf.mp hb).2)
      rw [mul_inv_cancel_right] at hc
      have hmem : x * τ⁻¹ * τ ∈ P2 ⊔ Subgroup.zpowers τ :=
        (P2 ⊔ Subgroup.zpowers τ).mul_mem (Subgroup.mem_sup_left (h2 ⟨x * τ⁻¹, h1⟩ hc))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ))
      rwa [inv_mul_cancel_right] at hmem
  have hmem : ∀ x : ↥(P1 ⊔ Subgroup.zpowers τ),
      (x : G) ∈ (P1 ⊔ Subgroup.zpowers τ) ⊓ (P2 ⊔ Subgroup.zpowers τ) ↔
        (ψ₁ x : u4ExtGroup h) ∈ u4ExtParP h ⊓ u4ExtParP2 h := by
    intro x
    constructor
    · intro hx
      have e : (ψ₁ x : u4ExtGroup h) =
          (ψ₂ ⟨x, (Subgroup.mem_inf.mp hx).2⟩ : u4ExtGroup h) :=
        hag x x.2 (Subgroup.mem_inf.mp hx).2
      refine Subgroup.mem_inf.mpr ⟨(ψ₁ x).2, ?_⟩
      rw [e]
      exact (ψ₂ _).2
    · intro hx
      exact Subgroup.mem_inf.mpr ⟨x.2, hback x (Subgroup.mem_inf.mp hx).2⟩
  have e : (RankTwoAmalgam.ofSubgroups (P1 ⊔ Subgroup.zpowers τ)
      (P2 ⊔ Subgroup.zpowers τ)).Iso (RankTwoAmalgam.ofSubgroups (u4ExtParP h) (u4ExtParP2 h)) :=
    { φ1 := ψ₁
      φ12 := F1.restrictEquiv ψ₁ inf_le_left inf_le_left hmem
      φ2 := ψ₂
      comm1 := fun (g : ↥((P1 ⊔ Subgroup.zpowers τ) ⊓ (P2 ⊔ Subgroup.zpowers τ))) =>
        Subtype.ext (F1.coe_restrictEquiv ψ₁ inf_le_left inf_le_left hmem g)
      comm2 := fun (g : ↥((P1 ⊔ Subgroup.zpowers τ) ⊓ (P2 ⊔ Subgroup.zpowers τ))) =>
        Subtype.ext ((F1.coe_restrictEquiv ψ₁ inf_le_left inf_le_left hmem g).trans
          (hag g (Subgroup.mem_inf.mp g.2).1 (Subgroup.mem_inf.mp g.2).2)) }
  exact isU4ExtTwo_of_iso h e

end CFSG.Quasithin.F112R.St84

end
