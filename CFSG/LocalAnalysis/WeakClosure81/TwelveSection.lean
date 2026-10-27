module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev SecMod (W₁ W₂ : Submodule (ZMod 2) V) : Type := ↥W₁ ⧸ W₂.comap W₁.subtype

@[expose] noncomputable def secMap (W₁ W₂ : Submodule (ZMod 2) V) (f : V →ₗ[ZMod 2] V)
    (h₁ : ∀ w ∈ W₁, f w ∈ W₁) (h₂ : ∀ w ∈ W₂, f w ∈ W₂) :
    SecMod W₁ W₂ →ₗ[ZMod 2] SecMod W₁ W₂ :=
  Submodule.mapQ _ _ (f.restrict h₁) (fun w hw => by simpa using h₂ _ hw)

theorem secMap_mk (W₁ W₂ : Submodule (ZMod 2) V) (f : V →ₗ[ZMod 2] V)
    (h₁ : ∀ w ∈ W₁, f w ∈ W₁) (h₂ : ∀ w ∈ W₂, f w ∈ W₂) (w : V) (hw : w ∈ W₁) :
    secMap W₁ W₂ f h₁ h₂ (Submodule.Quotient.mk ⟨w, hw⟩) = Submodule.Quotient.mk ⟨f w, h₁ w hw⟩ :=
  rfl

private theorem b12_TwelveSection_mk_eq_zero_iff {W₁ W₂ : Submodule (ZMod 2) V} {w : V}
    (hw : w ∈ W₁) :
    (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) : SecMod W₁ W₂) = 0 ↔ w ∈ W₂ := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

section Section

variable {G : Type} [Group G]

@[expose] noncomputable def sectionRep (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) :
    G →* LGL 2 (SecMod W₁ W₂) where
  toFun g := LinearEquiv.ofLinear
    (secMap W₁ W₂ (ρ g : V →ₗ[ZMod 2] V) (h₁ g) (h₂ g))
    (secMap W₁ W₂ (ρ g⁻¹ : V →ₗ[ZMod 2] V) (h₁ g⁻¹) (h₂ g⁻¹))
    (by
      apply Submodule.linearMap_qext
      ext ⟨w, hw⟩
      show secMap W₁ W₂ (ρ g : V →ₗ[ZMod 2] V) (h₁ g) (h₂ g)
        (secMap W₁ W₂ (ρ g⁻¹ : V →ₗ[ZMod 2] V) (h₁ g⁻¹) (h₂ g⁻¹) (Submodule.Quotient.mk ⟨w, hw⟩)) =
          Submodule.Quotient.mk ⟨w, hw⟩
      rw [secMap_mk, secMap_mk]
      congr 1
      apply Subtype.ext
      show ρ g (ρ g⁻¹ w) = w
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl)
    (by
      apply Submodule.linearMap_qext
      ext ⟨w, hw⟩
      show secMap W₁ W₂ (ρ g⁻¹ : V →ₗ[ZMod 2] V) (h₁ g⁻¹) (h₂ g⁻¹)
        (secMap W₁ W₂ (ρ g : V →ₗ[ZMod 2] V) (h₁ g) (h₂ g) (Submodule.Quotient.mk ⟨w, hw⟩)) =
          Submodule.Quotient.mk ⟨w, hw⟩
      rw [secMap_mk, secMap_mk]
      congr 1
      apply Subtype.ext
      show ρ g⁻¹ (ρ g w) = w
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨w, hw⟩ := x
      show secMap W₁ W₂ (ρ 1 : V →ₗ[ZMod 2] V) (h₁ 1) (h₂ 1) (Submodule.Quotient.mk ⟨w, hw⟩) = _
      rw [secMap_mk]
      congr 1
      apply Subtype.ext
      show ρ 1 w = w
      rw [map_one]
      rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨w, hw⟩ := x
      show secMap W₁ W₂ (ρ (g * h) : V →ₗ[ZMod 2] V) (h₁ (g * h)) (h₂ (g * h))
          (Submodule.Quotient.mk ⟨w, hw⟩) =
        secMap W₁ W₂ (ρ g : V →ₗ[ZMod 2] V) (h₁ g) (h₂ g)
          (secMap W₁ W₂ (ρ h : V →ₗ[ZMod 2] V) (h₁ h) (h₂ h) (Submodule.Quotient.mk ⟨w, hw⟩))
      rw [secMap_mk, secMap_mk, secMap_mk]
      congr 1
      apply Subtype.ext
      show ρ (g * h) w = ρ g (ρ h w)
      rw [map_mul]
      rfl

theorem sectionRep_mk (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) (g : G) (w : V)
    (hw : w ∈ W₁) :
    sectionRep ρ W₁ W₂ h₁ h₂ g (Submodule.Quotient.mk ⟨w, hw⟩) =
      Submodule.Quotient.mk ⟨ρ g w, h₁ g w hw⟩ :=
  rfl

theorem mem_ker_sectionRep (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) (g : G) :
    g ∈ (sectionRep ρ W₁ W₂ h₁ h₂).ker ↔ ∀ w ∈ W₁, ρ g w - w ∈ W₂ := by
  constructor
  · intro hg w hw
    have hmem : (Submodule.Quotient.mk (⟨ρ g w, h₁ g w hw⟩ : ↥W₁) : SecMod W₁ W₂) =
        Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) := by
      have h1 : sectionRep ρ W₁ W₂ h₁ h₂ g = 1 := MonoidHom.mem_ker.mp hg
      have h2 := congrArg (fun e : LGL 2 (SecMod W₁ W₂) =>
        e (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁))) h1
      simpa [sectionRep_mk] using h2
    have hzero : (Submodule.Quotient.mk
        (⟨ρ g w - w, W₁.sub_mem (h₁ g w hw) hw⟩ : ↥W₁) : SecMod W₁ W₂) = 0 := by
      have hsub : (⟨ρ g w - w, W₁.sub_mem (h₁ g w hw) hw⟩ : ↥W₁) =
          (⟨ρ g w, h₁ g w hw⟩ : ↥W₁) - (⟨w, hw⟩ : ↥W₁) := rfl
      rw [hsub, Submodule.Quotient.mk_sub, hmem, sub_self]
    exact (b12_TwelveSection_mk_eq_zero_iff (W₂ := W₂)
      (W₁.sub_mem (h₁ g w hw) hw)).mp hzero
  · intro hall
    rw [MonoidHom.mem_ker]
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨w, hw⟩ := x
      rw [sectionRep_mk]
      rw [show (1 : LGL 2 (SecMod W₁ W₂)) (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁)) =
        Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) from rfl]
      exact (Submodule.Quotient.eq (W₂.comap W₁.subtype)).mpr
        (Submodule.mem_comap.mpr (by simpa using hall w hw))

theorem repQuad_sectionRep (ρ : G →* LGL 2 V) (A : Subgroup G) (hq : RepQuad ρ A)
    (W₁ W₂ : Submodule (ZMod 2) V) (h₁ : ∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (h₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) :
    RepQuad (sectionRep ρ W₁ W₂ h₁ h₂) A := by
  change commSpace (A.map (sectionRep ρ W₁ W₂ h₁ h₂))
    (commSub (A.map (sectionRep ρ W₁ W₂ h₁ h₂))) = ⊥
  rw [commSpace_eq_bot_iff]
  intro a ha u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  have hq' : ∀ b ∈ A.map ρ, ∀ z ∈ commSub (A.map ρ), b z = z :=
    (commSpace_eq_bot_iff).mp hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro z ⟨b, hb, v, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨w, hw⟩ := v
      have hyw : ρ y w - w ∈ commSub (A.map ρ) :=
        Submodule.subset_span ⟨ρ y, Subgroup.mem_map_of_mem ρ hy, w, rfl⟩
      have hfix : ρ x (ρ y w - w) = ρ y w - w :=
        hq' (ρ x) (Subgroup.mem_map_of_mem ρ hx) (ρ y w - w) hyw
      have h1 : sectionRep ρ W₁ W₂ h₁ h₂ y (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁)) -
          Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) =
          Submodule.Quotient.mk (⟨ρ y w - w, W₁.sub_mem (h₁ y w hw) hw⟩ : ↥W₁) := by
        rw [sectionRep_mk, ← Submodule.Quotient.mk_sub]
        congr 1
      rw [h1, sectionRep_mk]
      refine (Submodule.Quotient.eq (W₂.comap W₁.subtype)).mpr ?_
      rw [Submodule.mem_comap]
      change ρ x (ρ y w - w) - (ρ y w - w) ∈ W₂
      rw [hfix, sub_self]
      exact W₂.zero_mem
  · exact map_zero _
  · intro y z hy hz ihy ihz
    simp [map_add, ihy, ihz]
  · intro c y hy ih
    simp [map_smul, ih]

theorem isChiefFactor_sectionRep (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (hcf : IsChiefFactor ρ W₁ W₂) :
    IsChiefFactor (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1) ⊤ ⊥ := by
  obtain ⟨hw₂w₁, hW₁, hW₂, hmin⟩ := hcf
  obtain ⟨hw₂le, w, hw, hwnot⟩ := SetLike.lt_iff_le_and_exists.mp hw₂w₁
  have hne : (⊤ : Submodule (ZMod 2) (SecMod W₁ W₂)) ≠ ⊥ := by
    intro h
    have hxU : (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) : SecMod W₁ W₂) ∈
        (⊤ : Submodule (ZMod 2) (SecMod W₁ W₂)) := Submodule.mem_top
    have hzero : (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) : SecMod W₁ W₂) = 0 := by
      have hbot : (Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁) : SecMod W₁ W₂) ∈
          (⊥ : Submodule (ZMod 2) (SecMod W₁ W₂)) := h ▸ hxU
      simpa only [Submodule.mem_bot] using hbot
    exact hwnot ((b12_TwelveSection_mk_eq_zero_iff (W₂ := W₂) hw).mp hzero)
  refine ⟨lt_of_le_of_ne bot_le (Ne.symm hne), ?_, ?_, ?_⟩
  · intro g u _
    exact Submodule.mem_top
  · intro g u hu
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  · intro U _ _ hUinv
    let p := W₂.comap W₁.subtype
    let π : ↥W₁ →ₗ[ZMod 2] SecMod W₁ W₂ := Submodule.mkQ p
    let U' : Submodule (ZMod 2) V := (U.comap π).map W₁.subtype
    have hU'le : U' ≤ W₁ := Submodule.map_subtype_le (p := W₁) (U.comap π)
    have hW₂U' : W₂ ≤ U' := by
      intro u hu
      have hu₁ : u ∈ W₁ := hw₂le hu
      refine Submodule.mem_map.mpr ⟨(⟨u, hu₁⟩ : ↥W₁), ?_, rfl⟩
      exact Submodule.mem_comap.mpr (by
        have hz : (Submodule.Quotient.mk (⟨u, hu₁⟩ : ↥W₁) : SecMod W₁ W₂) = 0 :=
          (b12_TwelveSection_mk_eq_zero_iff (W₂ := W₂) hu₁).mpr hu
        rw [show π (⟨u, hu₁⟩ : ↥W₁) = Submodule.Quotient.mk (⟨u, hu₁⟩ : ↥W₁) from rfl, hz]
        exact Submodule.zero_mem U)
    have hU'inv : ∀ g : G, ∀ u ∈ U', ρ g u ∈ U' := by
      intro g u hu
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨(⟨ρ g (v : V), hW₁ g v v.2⟩ : ↥W₁), ?_, rfl⟩
      exact Submodule.mem_comap.mpr (by
        show π (⟨ρ g (v : V), hW₁ g v v.2⟩ : ↥W₁) ∈ U
        exact hUinv g (π v) (Submodule.mem_comap.mp hv))
    obtain hUW₂ | hUW₁ := hmin U' hW₂U' hU'le hU'inv
    · left
      refine (Submodule.eq_bot_iff U).mpr ?_
      intro u hu
      induction u using Submodule.Quotient.induction_on with
      | H z =>
        obtain ⟨v, hv⟩ := z
        have hvU' : v ∈ U' := by
          refine Submodule.mem_map.mpr ⟨(⟨v, hv⟩ : ↥W₁), ?_, rfl⟩
          exact Submodule.mem_comap.mpr hu
        have hvW₂ : v ∈ W₂ := by rw [hUW₂] at hvU'; exact hvU'
        exact (b12_TwelveSection_mk_eq_zero_iff (W₂ := W₂) hv).mpr hvW₂
    · right
      refine Submodule.eq_top_iff'.mpr ?_
      intro u
      induction u using Submodule.Quotient.induction_on with
      | H z =>
        obtain ⟨v, hv⟩ := z
        have hvU' : v ∈ U' := by rw [hUW₁]; exact hv
        obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.mp hvU'
        have hyeq : y = (⟨v, hv⟩ : ↥W₁) := Subtype.ext (by simpa using hyv)
        rw [← hyeq]
        exact Submodule.mem_comap.mp hy

theorem isNoncentral_sectionRep (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (hcf : IsChiefFactor ρ W₁ W₂) (hnc : IsNoncentral ρ W₁ W₂) :
    IsNoncentral (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1) ⊤ ⊥ := by
  obtain ⟨g, w, hw, hne⟩ := hnc
  refine ⟨g, Submodule.Quotient.mk (⟨w, hw⟩ : ↥W₁), Submodule.mem_top, ?_⟩
  intro hmem
  rw [Submodule.mem_bot] at hmem
  apply hne
  have hzero : (Submodule.Quotient.mk
      (⟨ρ g w - w, W₁.sub_mem (hcf.2.1 g w hw) hw⟩ : ↥W₁) : SecMod W₁ W₂) = 0 := by
    have hsub : (⟨ρ g w - w, W₁.sub_mem (hcf.2.1 g w hw) hw⟩ : ↥W₁) =
        (⟨ρ g w, hcf.2.1 g w hw⟩ : ↥W₁) - (⟨w, hw⟩ : ↥W₁) := rfl
    rw [hsub, Submodule.Quotient.mk_sub]
    exact hmem
  exact (b12_TwelveSection_mk_eq_zero_iff (W₂ := W₂)
    (W₁.sub_mem (hcf.2.1 g w hw) hw)).mp hzero

theorem invariant_induction (ρ : G →* LGL 2 V) (P : Submodule (ZMod 2) V → Prop) (h0 : P ⊥)
    (hstep : ∀ W₁ W₂ : Submodule (ZMod 2) V, IsChiefFactor ρ W₁ W₂ → P W₂ → P W₁)
    (W : Submodule (ZMod 2) V) (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) : P W := by
  classical
  haveI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun U : Submodule (ZMod 2) V => (U : Set V)) SetLike.coe_injective
  have key : ∀ n, ∀ W : Submodule (ZMod 2) V,
      (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → Module.finrank (ZMod 2) W = n → P W := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih W hW hfin
    by_cases hbot : W = ⊥
    · rw [hbot]; exact h0
    · have hbotlt : (⊥ : Submodule (ZMod 2) V) < W := bot_lt_iff_ne_bot.mpr hbot
      let s : Set (Submodule (ZMod 2) V) :=
        {W' | (∀ g : G, ∀ w ∈ W', ρ g w ∈ W') ∧ W' < W}
      have hsne : s.Nonempty :=
        ⟨⊥, (fun g w hw => by rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]), hbotlt⟩
      have hsfin : s.Finite := Set.toFinite s
      obtain ⟨W', hW'mem, hW'max⟩ := hsfin.exists_maximal hsne
      have hcf : IsChiefFactor ρ W W' := by
        refine ⟨hW'mem.2, hW, hW'mem.1, ?_⟩
        intro U hW'U hUW hUinv
        by_cases hUW' : U = W
        · exact Or.inr hUW'
        · refine Or.inl ?_
          have hUin : U ∈ s := ⟨hUinv, lt_of_le_of_ne hUW hUW'⟩
          exact le_antisymm (hW'max hUin hW'U) hW'U
      have hlt : Module.finrank (ZMod 2) W' < Module.finrank (ZMod 2) W :=
        Submodule.finrank_lt_finrank_of_lt hW'mem.2
      have hPW' : P W' :=
        ih (Module.finrank (ZMod 2) W') (by rw [← hfin]; exact hlt) W' hW'mem.1 rfl
      exact hstep W W' hcf hPW'
  exact key (Module.finrank (ZMod 2) W) W hW rfl

theorem isPGroup_map_of_trivial_on_chief (ρ : G →* LGL 2 V) (H : Subgroup G)
    (hH : ∀ W₁ W₂ : Submodule (ZMod 2) V, IsChiefFactor ρ W₁ W₂ → ∀ x ∈ H, ∀ w ∈ W₁,
      ρ x w - w ∈ W₂) : IsPGroup 2 (H.map ρ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
  let P : Submodule (ZMod 2) V → Prop :=
    fun W => ∃ k : ℕ, ∀ w ∈ W, ((ρ x) ^ 2 ^ k) w = w
  have h0 : P ⊥ := by
    refine ⟨0, ?_⟩
    intro w hw
    rw [Submodule.mem_bot] at hw
    rw [hw, map_zero]
  have hstep : ∀ W₁ W₂ : Submodule (ZMod 2) V, IsChiefFactor ρ W₁ W₂ → P W₂ → P W₁ := by
    intro W₁ W₂ hcf hP₂
    obtain ⟨k₂, hk₂⟩ := hP₂
    refine ⟨k₂ + 1, ?_⟩
    intro w hw
    let y : LGL 2 V := (ρ x) ^ 2 ^ k₂
    set δ : V := y w - w with hδdef
    have hyw : δ ∈ W₂ := by
      have h : y w - w ∈ W₂ := by
        have h' := hH W₁ W₂ hcf (x ^ 2 ^ k₂) (H.pow_mem hx (2 ^ k₂)) w hw
        rw [map_pow] at h'
        simpa [y] using h'
      rwa [hδdef]
    have hyδ : y δ = δ := by
      simpa [y] using hk₂ δ hyw
    have hδeq : y w = w + δ := by
      rw [hδdef]; abel
    have h2δ : δ + δ = 0 := by
      have h2 : (1 + 1 : ZMod 2) = 0 := CharTwo.add_self_eq_zero 1
      calc δ + δ = (1 + 1 : ZMod 2) • δ := by rw [add_smul, one_smul]
        _ = 0 := by rw [h2, zero_smul]
    have hsw : y (y w) = w := by
      calc y (y w) = y (w + δ) := by rw [hδeq]
        _ = y w + y δ := map_add y _ _
        _ = y w + δ := by rw [hyδ]
        _ = (w + δ) + δ := by rw [hδeq]
        _ = w + (δ + δ) := by rw [add_assoc]
        _ = w + 0 := by rw [h2δ]
        _ = w := add_zero w
    have hp : (ρ x) ^ 2 ^ (k₂ + 1) = y * y :=
      (by rw [show 2 ^ (k₂ + 1) = 2 ^ k₂ * 2 from pow_succ 2 k₂, pow_mul, pow_two])
    rw [hp, LinearEquiv.mul_apply]
    exact hsw
  have htop : P ⊤ := invariant_induction ρ P h0 hstep ⊤ (fun _ _ _ => Submodule.mem_top)
  obtain ⟨k, hk⟩ := htop
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow]
  rw [← hxg]
  ext w
  simpa using hk w Submodule.mem_top

end Section

end CFSG.LocalAnalysis.WeakClosure81
