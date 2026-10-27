module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

namespace Sec1211He

variable {X X' : Type} [Group X] [Group X'] {m : ℕ}

@[expose] noncomputable def natCoordMap (e : X ≃* X') {L W : Subgroup X}
    (C : KGH91.NatCoord L W m) :
    KGH91.NatCoord (L.map (e : X →* X')) (W.map (e : X →* X')) m where
  E x := C.E (e.symm x)
  ρ := C.ρ.comp (e.subgroupMap L).symm.toMonoidHom
  le := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨l * w * l⁻¹, C.conj_mem ⟨l, hl⟩ hw, by simp⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨l⁻¹ * w * l, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (C.le hl) (l⁻¹ * w * l)).mpr (by
          simpa [mul_assoc] using hw)
        exact this
      · have h1 : e (l⁻¹ * w * l) = x := by
          have h2 : e w = e l * x * (e l)⁻¹ := by simpa using hwx
          rw [map_mul, map_mul, map_inv, h2]
          group
        simpa using h1
  map_mul := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := C.map_mul a ha b hb
    simpa [← map_mul] using this
  inj := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have : C.E a = C.E b := by simpa using hab
    rw [C.inj a ha b hb this]
  surj := by
    intro x
    obtain ⟨a, ha, hax⟩ := C.surj x
    exact ⟨e a, ⟨a, ha, rfl⟩, by simpa using hax⟩
  conj := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩ _ ⟨a, ha, rfl⟩
    have h1 := C.conj ⟨l, hl⟩ a ha
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.subgroupMap_symm_apply, MonoidHom.coe_ofClass, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
    exact h1
  ρ_surj := by
    intro g
    obtain ⟨l, hl⟩ := C.ρ_surj g
    refine ⟨e.subgroupMap L l, ?_⟩
    simp [hl]

theorem heInspCfg_of_mulEquiv (e : X ≃* X') (h : HeInspCfg X m) : HeInspCfg X' m := by
  obtain ⟨Y, W₁, W₂, C₁, C₂, τ, hWY, hWW, hE, hk, hd, hτY, hτW, hR⟩ := h
  refine ⟨Y.map (e : X →* X'), W₁.map (e : X →* X'), W₂.map (e : X →* X'), natCoordMap e C₁,
    natCoordMap e C₂, (e.symm.trans τ).trans e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hWY
  · rw [← Subgroup.map_inf _ _ _ e.injective, hWW, Subgroup.map_bot]
  · rw [← Subgroup.map_sup]
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', haa⟩ := a.2
      obtain ⟨b', hb', hbb⟩ := b.2
      have := congrArg Subtype.val (hE.1.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      simp only [Subgroup.coe_mul] at this ⊢
      rw [← haa, ← hbb, ← map_mul, ← map_mul, this]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  · intro g
    have hg : C₁.ρ ((e.subgroupMap Y).symm g.1) = 1 := g.2
    obtain ⟨n, hn⟩ := hk ⟨_, hg⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : ((e.subgroupMap Y).symm g.1) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have h2 := congrArg (e.subgroupMap Y) h1
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
    simpa using h2
  · intro y
    exact hd _
  · rw [Subgroup.map_map]
    have : ((e.symm.trans τ).trans e).toMonoidHom.comp (e : X →* X') =
        (e : X →* X').comp τ.toMonoidHom := by
      ext x
      simp
    rw [this, ← Subgroup.map_map, hτY]
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨τ w, hτW w hw, by simp⟩
  · intro h3
    obtain ⟨R, hR', hRY⟩ := hR h3
    refine ⟨R.map (e : X →* X'), ⟨le_top, hR'.2.1.map _, ?_⟩, ?_⟩
    · show ¬ 2 ∣ (R.map (e : X →* X')).relIndex ⊤
      rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq _ e.surjective
        (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le)]
      have := hR'.2.2
      rwa [show (R.subgroupOf ⊤).index = R.index from Subgroup.relIndex_top_right R] at this
    · rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨r * y * r⁻¹, (Subgroup.mem_normalizer_iff.mp (hRY hr) y).mp hy, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨r⁻¹ * y * r, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRY hr)) y).mp hy
          simpa using this
        · have h1 : e y = e r * x * (e r)⁻¹ := by simpa using hyx
          show e (r⁻¹ * y * r) = x
          rw [map_mul, map_mul, map_inv, h1]
          group

theorem twoRankLtSix_of_mulEquiv (e : X ≃* X') (h : TwoRankLtSix X') : TwoRankLtSix X := by
  intro E hE
  have h1 := h (E.map (e : X →* X')) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective] at h1
  · obtain ⟨a', ha', haa⟩ := a.2
    obtain ⟨b', hb', hbb⟩ := b.2
    have := congrArg Subtype.val (hE.1.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at this ⊢
    rw [← haa, ← hbb, ← map_mul, ← map_mul, this]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem twoRankLtEight_of_mulEquiv (e : X ≃* X') (h : TwoRankLtEight X') : TwoRankLtEight X := by
  intro E hE
  have h1 := h (E.map (e : X →* X')) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective] at h1
  · obtain ⟨a', ha', haa⟩ := a.2
    obtain ⟨b', hb', hbb⟩ := b.2
    have := congrArg Subtype.val (hE.1.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at this ⊢
    rw [← haa, ← hbb, ← map_mul, ← map_mul, this]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

end Sec1211He

end CFSG.Quasithin.H13
