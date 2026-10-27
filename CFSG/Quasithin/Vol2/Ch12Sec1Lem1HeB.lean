module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeA
public import CFSG.Quasithin.Vol2.Ch12Sec1Swap

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

namespace Sec1211He

variable {G : Type} [Group G] {m : ℕ}

theorem NatCoord.ρ_eq_one {L W : Subgroup G} (C : KGH91.NatCoord L W m) (l : ↥L)
    (hl : ∀ a ∈ W, (l : G) * a * (l : G)⁻¹ = a) : C.ρ l = 1 := by
  have h : ∀ x : Fin m → ZMod 2, (C.ρ l : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ x = x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := C.surj x
    rw [← C.conj l a ha, hl a ha]
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simp only [mulVec_single_one, col_apply] at h1
  refine h1.trans ?_
  show (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) i = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j
  simp [Matrix.one_apply, Pi.single_apply]

section Quot

variable {K : Subgroup G}

@[expose] def toQ {A : Subgroup G} (hA : A ≤ K) : ↥A →* ↥K ⧸ Subgroup.center ↥K :=
  (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hA)

theorem toQ_apply {A : Subgroup G} (hA : A ≤ K) (a : ↥A) :
    toQ hA a = QuotientGroup.mk' (Subgroup.center ↥K) ⟨a, hA a.2⟩ := rfl

@[expose] def imgQ {A : Subgroup G} (hA : A ≤ K) : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
  (toQ hA).range

theorem imgQ_mono {A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) (hAB : A ≤ B) :
    imgQ hA ≤ imgQ hB := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨a, hAB a.2⟩, rfl⟩

theorem toQ_injective {W : Subgroup G} (hW : W ≤ K)
    (hWC : W ⊓ Subgroup.centralizer (K : Set G) = ⊥) : Function.Injective (toQ hW) := by
  intro a b hab
  rw [toQ_apply, toQ_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hab
  have hz : (a : G)⁻¹ * b ∈ W ⊓ Subgroup.centralizer (K : Set G) := by
    refine ⟨W.mul_mem (W.inv_mem a.2) b.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.mp hab ⟨k, hk⟩
    simpa using congrArg Subtype.val this
  rw [hWC, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact Subtype.ext hz

end Quot

section Coord

variable [Finite G] {K Y W : Subgroup G}

omit [Finite G] in
theorem ker_toQ_le (hYK : Y ≤ K) (hWY : W ≤ Y) (C : KGH91.NatCoord Y W m) :
    (toQ hYK).ker ≤ C.ρ.ker := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy ⊢
  refine NatCoord.ρ_eq_one C y fun a ha => ?_
  rw [toQ_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨a, hYK (hWY ha)⟩)
  simp only [Subgroup.coe_mul] at h1
  rw [← h1, mul_inv_cancel_right]

@[expose] noncomputable def ρQ (hYK : Y ≤ K) (hWY : W ≤ Y) (C : KGH91.NatCoord Y W m) :
    ↥(imgQ hYK) →* SpecialLinearGroup (Fin m) (ZMod 2) :=
  (QuotientGroup.lift (toQ hYK).ker C.ρ (ker_toQ_le hYK hWY C)).comp
    (QuotientGroup.quotientKerEquivRange (toQ hYK)).symm.toMonoidHom

omit [Finite G] in
theorem ρQ_apply (hYK : Y ≤ K) (hWY : W ≤ Y) (C : KGH91.NatCoord Y W m) (y : ↥Y) :
    ρQ hYK hWY C ⟨toQ hYK y, ⟨y, rfl⟩⟩ = C.ρ y := by
  have h : (QuotientGroup.quotientKerEquivRange (toQ hYK)).symm ⟨toQ hYK y, ⟨y, rfl⟩⟩ =
      (y : ↥Y ⧸ (toQ hYK).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := congrArg (QuotientGroup.lift (toQ hYK).ker C.ρ (ker_toQ_le hYK hWY C)) h
  exact h2

@[expose] noncomputable def EQ (hYK : Y ≤ K) (hWY : W ≤ Y) (C : KGH91.NatCoord Y W m) :
    (↥K ⧸ Subgroup.center ↥K) → Fin m → ZMod 2 := fun x =>
  C.E ((Function.invFun (⇑(toQ (hWY.trans hYK))) x : ↥W) : G)

omit [Finite G] in
theorem EQ_apply (hYK : Y ≤ K) (hWY : W ≤ Y) (hWC : W ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (C : KGH91.NatCoord Y W m) (w : ↥W) :
    EQ hYK hWY C (toQ (hWY.trans hYK) w) = C.E w := by
  rw [EQ, Function.leftInverse_invFun (toQ_injective (hWY.trans hYK) hWC) w]

@[expose] noncomputable def natCoordQ (hYK : Y ≤ K) (hWY : W ≤ Y)
    (hWC : W ⊓ Subgroup.centralizer (K : Set G) = ⊥) (C : KGH91.NatCoord Y W m) :
    KGH91.NatCoord (imgQ hYK) (imgQ (hWY.trans hYK)) m where
  E := EQ hYK hWY C
  ρ := ρQ hYK hWY C
  le := by
    rintro _ ⟨y, rfl⟩
    refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨w, rfl⟩ := hx
    refine ⟨⟨(y : G) * w * (y : G)⁻¹, C.conj_mem y w.2⟩, ?_⟩
    simp only [toQ_apply, ← map_mul, ← map_inv]
    rfl
  map_mul := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, EQ_apply hYK hWY hWC, EQ_apply hYK hWY hWC, EQ_apply hYK hWY hWC]
    exact C.map_mul a a.2 b b.2
  inj := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    rw [EQ_apply hYK hWY hWC, EQ_apply hYK hWY hWC] at hab
    rw [Subtype.ext (C.inj a a.2 b b.2 hab)]
  surj := by
    intro x
    obtain ⟨a, ha, hax⟩ := C.surj x
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, by rw [EQ_apply hYK hWY hWC]; exact hax⟩
  conj := by
    rintro ⟨_, ⟨y, rfl⟩⟩ _ ⟨w, rfl⟩
    have h1 : (toQ hYK y) * toQ (hWY.trans hYK) w * (toQ hYK y)⁻¹ =
        toQ (hWY.trans hYK) ⟨(y : G) * w * (y : G)⁻¹, C.conj_mem y w.2⟩ := by
      simp only [toQ_apply, ← map_mul, ← map_inv]
      rfl
    simp only
    rw [h1, EQ_apply hYK hWY hWC, EQ_apply hYK hWY hWC, ρQ_apply]
    exact C.conj y w w.2
  ρ_surj := by
    intro g
    obtain ⟨y, hy⟩ := C.ρ_surj g
    exact ⟨⟨toQ hYK y, ⟨y, rfl⟩⟩, by rw [ρQ_apply, hy]⟩

theorem natCoordQ_ρ (hYK : Y ≤ K) (hWY : W ≤ Y)
    (hWC : W ⊓ Subgroup.centralizer (K : Set G) = ⊥) (C : KGH91.NatCoord Y W m) (y : ↥Y) :
    (natCoordQ hYK hWY hWC C).ρ ⟨toQ hYK y, ⟨y, rfl⟩⟩ = C.ρ y :=
  ρQ_apply hYK hWY C y

end Coord

@[expose] def conjK {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht k).mp k.2⟩
  invFun k := ⟨t⁻¹ * k * t, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) k).mp k.2
    simpa using this⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def conjQ {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) : MulAut (↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (conjK ht)
    (Subgroup.map_center_eq _)

theorem conjQ_toQ {K A B : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hA : A ≤ K) (hB : B ≤ K) (a : ↥A) (hab : t * a * t⁻¹ ∈ B) :
    conjQ ht (toQ hA a) = toQ hB ⟨t * a * t⁻¹, hab⟩ := by
  rw [toQ_apply, conjQ, QuotientGroup.mk'_apply, QuotientGroup.congr_mk]
  rfl

theorem heInspCfg_of [Finite G] {K Y W₁ W₂ : Subgroup G} {t : G} (hYK : Y ≤ K)
    (hWY : W₁ ⊔ W₂ ≤ Y) (hWW : W₁ ⊓ W₂ = ⊥) (hE : IsElemAbelian 2 (W₁ ⊔ W₂))
    (hWC : (W₁ ⊔ W₂) ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (C₁ : KGH91.NatCoord Y W₁ m) (C₂ : KGH91.NatCoord Y W₂ m) (hk : IsPGroup 2 C₁.ρ.ker)
    (hd : ∀ y, C₂.ρ y = slGraphAut m (ZMod 2) (C₁.ρ y))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (htW : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₂)
    (hR : m = 3 → ∃ R : Subgroup G, IsSylowTwoOf R K ∧ R ≤ Subgroup.normalizer (Y : Set G)) :
    HeInspCfg (↥K ⧸ Subgroup.center ↥K) m := by
  have hW₁Y : W₁ ≤ Y := le_sup_left.trans hWY
  have hW₂Y : W₂ ≤ Y := le_sup_right.trans hWY
  have hWK : W₁ ⊔ W₂ ≤ K := hWY.trans hYK
  have hW₁C : W₁ ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    le_bot_iff.mp (hWC ▸ inf_le_inf_right _ le_sup_left)
  have hW₂C : W₂ ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    le_bot_iff.mp (hWC ▸ inf_le_inf_right _ le_sup_right)
  have hinj := toQ_injective hWK hWC
  refine ⟨imgQ hYK, imgQ (hW₁Y.trans hYK), imgQ (hW₂Y.trans hYK),
    natCoordQ hYK hW₁Y hW₁C C₁, natCoordQ hYK hW₂Y hW₂C C₂, conjQ htK,
    sup_le (imgQ_mono _ _ hW₁Y) (imgQ_mono _ _ hW₂Y), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨⟨⟨a, ha⟩, rfl⟩, ⟨⟨b, hb⟩, hba⟩⟩
    have h1 : (⟨a, le_sup_left (b := W₂) ha⟩ : ↥(W₁ ⊔ W₂)) = ⟨b, le_sup_right (a := W₁) hb⟩ :=
      hinj hba.symm
    have hab : a = b := congrArg Subtype.val h1
    have h2 : a ∈ W₁ ⊓ W₂ := ⟨ha, by rw [hab]; exact hb⟩
    rw [hWW, Subgroup.mem_bot] at h2
    subst h2
    rw [Subgroup.mem_bot]
    exact map_one _
  ·
    have hle : imgQ (hW₁Y.trans hYK) ⊔ imgQ (hW₂Y.trans hYK) ≤ imgQ hWK :=
      sup_le (imgQ_mono _ _ le_sup_left) (imgQ_mono _ _ le_sup_right)
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha'⟩ := hle a.2
      obtain ⟨b', hb'⟩ := hle b.2
      have hab := hE.1.1.comm a' b'
      simp only [Subgroup.coe_mul]
      rw [← ha', ← hb', ← map_mul, ← map_mul, hab]
    · obtain ⟨a', rfl⟩ := hle hx
      rw [← map_pow]
      have : a' ^ 2 = 1 := Subtype.ext (by simpa using hE.2 a' a'.2)
      rw [this, map_one]
  ·
    rintro ⟨⟨x, hx⟩, hyk⟩
    obtain ⟨y, rfl⟩ := hx
    have hρ : C₁.ρ y = 1 := by
      have := hyk
      rw [MonoidHom.mem_ker, natCoordQ_ρ] at this
      exact this
    obtain ⟨n, hn⟩ := hk ⟨y, hρ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, h1, map_one]
  ·
    rintro ⟨_, ⟨y, rfl⟩⟩
    rw [natCoordQ_ρ, natCoordQ_ρ, hd]
  ·
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htY y).mp y.2⟩,
        (conjQ_toQ htK hYK hYK y _).symm⟩
    · refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).ge
      · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htY y).mp y.2⟩,
          (conjQ_toQ htK hYK hYK y _).symm⟩
      · rw [Subgroup.card_map_of_injective (f := (conjQ htK).toMonoidHom) (conjQ htK).injective]
  ·
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨t * w * t⁻¹, htW w w.2⟩, (conjQ_toQ htK _ _ w _).symm⟩
  ·
    intro h3
    obtain ⟨R, hRK, hRY⟩ := hR h3
    have hRK' : R ≤ K := hRK.1
    refine ⟨imgQ hRK', ⟨le_top, ?_, ?_⟩, ?_⟩
    · rintro ⟨_, ⟨r, rfl⟩⟩
      obtain ⟨n, hn⟩ := hRK.2.1 r
      refine ⟨n, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hn, map_one]
    · show ¬ 2 ∣ (imgQ hRK').relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      have hmap : imgQ hRK' = (R.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
        ext x
        constructor
        · rintro ⟨r, rfl⟩
          exact ⟨⟨r, hRK' r.2⟩, r.2, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, hk⟩, rfl⟩
      rw [hmap]
      intro h2
      exact hRK.2.2 (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
    · rintro _ ⟨r, rfl⟩
      refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
      obtain ⟨y, rfl⟩ := hx
      refine ⟨⟨r * y * r⁻¹, (Subgroup.mem_normalizer_iff.mp (hRY r.2) y).mp y.2⟩, ?_⟩
      simp only [toQ_apply, ← map_mul, ← map_inv]
      rfl

theorem NatCoord.card_eq {L W : Subgroup G} (C : KGH91.NatCoord L W m) :
    Nat.card W = 2 ^ m := by
  have hbij : Function.Bijective (fun w : ↥W => C.E w) := ⟨fun a b h =>
    Subtype.ext (C.inj a a.2 b b.2 h), fun x => by
      obtain ⟨a, ha, hax⟩ := C.surj x
      exact ⟨⟨a, ha⟩, hax⟩⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

theorem le_card_of_heInspCfg {X : Type} [Group X] [Finite X] {m : ℕ} (h : HeInspCfg X m) :
    ∃ E : Subgroup X, IsElemAbelian 2 E ∧ 2 ^ (2 * m) ≤ Nat.card E := by
  obtain ⟨Y, W₁, W₂, C₁, C₂, τ, -, hWW, hE, -⟩ := h
  refine ⟨W₁ ⊔ W₂, hE, ?_⟩
  let f : ↥W₁ × ↥W₂ → ↥(W₁ ⊔ W₂) := fun p =>
    ⟨p.1 * p.2, (W₁ ⊔ W₂).mul_mem (le_sup_left (b := W₂) p.1.2) (le_sup_right (a := W₁) p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hab
    have h1 : (a : X) * b = c * d := congrArg Subtype.val hab
    have h2 : (c : X)⁻¹ * a ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.mul_mem (W₁.inv_mem c.2) a.2, ?_⟩
      have : (c : X)⁻¹ * a = d * (b : X)⁻¹ := by
        calc (c : X)⁻¹ * a = (c : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
          _ = (c : X)⁻¹ * (c * d) * (b : X)⁻¹ := by rw [h1]
          _ = d * (b : X)⁻¹ := by group
      rw [this]
      exact W₂.mul_mem d.2 (W₂.inv_mem b.2)
    rw [hWW, Subgroup.mem_bot, inv_mul_eq_one] at h2
    have hac : a = c := Subtype.ext h2.symm
    subst hac
    have hbd : (b : X) = d := mul_left_cancel h1
    rw [Subtype.ext hbd]
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, NatCoord.card_eq C₁, NatCoord.card_eq C₂, ← pow_add, ← two_mul] at h1
  exact h1

theorem not_heInspCfg_of_twoRankLtSix {X : Type} [Group X] [Finite X] (hX : TwoRankLtSix X)
    {m : ℕ} (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m := by
  intro h
  obtain ⟨E, hE, hc⟩ := le_card_of_heInspCfg h
  have h1 := hX E hE
  have h2 : 2 ^ 6 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem not_heInspCfg_of_twoRankLtEight {X : Type} [Group X] [Finite X] (hX : TwoRankLtEight X) :
    ¬ HeInspCfg X 4 := by
  intro h
  obtain ⟨E, hE, hc⟩ := le_card_of_heInspCfg h
  have h1 := hX E hE
  omega

end Sec1211He

end CFSG.Quasithin.H13
