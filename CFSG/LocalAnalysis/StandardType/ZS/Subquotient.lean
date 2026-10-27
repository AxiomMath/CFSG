module

public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]

abbrev Subquot (W₁ W₂ : Submodule K U) : Type _ := ↥W₂ ⧸ W₁.comap W₂.subtype

@[expose] noncomputable def subquotEquiv (W₁ W₂ : Submodule K U) (g : U ≃ₗ[K] U)
    (h₁ : W₁.map (g : U →ₗ[K] U) = W₁) (h₂ : W₂.map (g : U →ₗ[K] U) = W₂) :
    Subquot W₁ W₂ ≃ₗ[K] Subquot W₁ W₂ :=
  Submodule.Quotient.equiv (W₁.comap W₂.subtype) (W₁.comap W₂.subtype)
    (g.ofSubmodules W₂ W₂ h₂) (by
      ext x
      rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
        Submodule.mem_comap]
      change g.symm (x : U) ∈ W₁ ↔ (x : U) ∈ W₁
      constructor
      · intro hx
        rw [← h₁]
        exact ⟨g.symm x, hx, by simp⟩
      · intro hx
        rw [← h₁] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        rw [← hyx]
        simpa using hy)

@[expose] noncomputable def subquotHom (H : Subgroup (U ≃ₗ[K] U)) (W₁ W₂ : Submodule K U)
    (h₁ : ∀ g ∈ H, W₁.map (g : U →ₗ[K] U) = W₁) (h₂ : ∀ g ∈ H, W₂.map (g : U →ₗ[K] U) = W₂) :
    H →* (Subquot W₁ W₂ ≃ₗ[K] Subquot W₁ W₂) where
  toFun g := subquotEquiv W₁ W₂ g (h₁ g g.2) (h₂ g g.2)
  map_one' := LinearEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_mul' g g' := LinearEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

theorem subquotEquiv_mk (W₁ W₂ : Submodule K U) (g : U ≃ₗ[K] U)
    (h₁ : W₁.map (g : U →ₗ[K] U) = W₁) (h₂ : W₂.map (g : U →ₗ[K] U) = W₂)
    (w : ↥W₂) :
    subquotEquiv W₁ W₂ g h₁ h₂ (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (g.ofSubmodules W₂ W₂ h₂ w) := by
  rw [subquotEquiv, Submodule.Quotient.equiv_apply]
  rfl

theorem subquotEquiv_eq_one_iff {W₁ W₂ : Submodule K U} {g : U ≃ₗ[K] U}
    (h₁ : W₁.map (g : U →ₗ[K] U) = W₁) (h₂ : W₂.map (g : U →ₗ[K] U) = W₂) :
    subquotEquiv W₁ W₂ g h₁ h₂ = 1 ↔ ∀ w ∈ W₂, g w - w ∈ W₁ := by
  constructor
  · intro h w hw
    let w' : ↥W₂ := ⟨w, hw⟩
    have hx : subquotEquiv W₁ W₂ g h₁ h₂ (Submodule.Quotient.mk w') =
        Submodule.Quotient.mk w' := by
      rw [h]
      rfl
    rw [subquotEquiv_mk] at hx
    have hmem : (g.ofSubmodules W₂ W₂ h₂ w' - w') ∈ W₁.comap W₂.subtype :=
      (Submodule.Quotient.eq (W₁.comap W₂.subtype)).mp hx
    rw [Submodule.mem_comap] at hmem
    simpa [LinearEquiv.ofSubmodules_apply] using hmem
  · intro h
    ext x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [subquotEquiv_mk]
    change Submodule.Quotient.mk (g.ofSubmodules W₂ W₂ h₂ w) = Submodule.Quotient.mk w
    rw [Submodule.Quotient.eq]
    have hw := h w w.2
    rw [Submodule.mem_comap]
    simpa [LinearEquiv.ofSubmodules_apply] using hw

end Field

section Prime

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem subquotEquiv_sub_one_mk {W₁ W₂ : Submodule (ZMod p) U} {t : U ≃ₗ[ZMod p] U}
    (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁) (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (w : ↥W₂) :
    ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)
      (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w - w) := by
  rw [LinearMap.sub_apply, Module.End.one_apply]
  change subquotEquiv W₁ W₂ t h₁ h₂ (Submodule.Quotient.mk w) - Submodule.Quotient.mk w = _
  rw [subquotEquiv_mk]
  rfl

private theorem subquotEquiv_mul_self {W₁ W₂ : Submodule (ZMod p) U} {t : U ≃ₗ[ZMod p] U}
    (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁) (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (htt : t * t = 1) :
    subquotEquiv W₁ W₂ t h₁ h₂ * subquotEquiv W₁ W₂ t h₁ h₂ = 1 := by
  ext x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearEquiv.mul_apply, subquotEquiv_mk, subquotEquiv_mk]
  change Submodule.Quotient.mk (t.ofSubmodules W₂ W₂ h₂ (t.ofSubmodules W₂ W₂ h₂ w)) =
    Submodule.Quotient.mk w
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  have hcoe : (t.ofSubmodules W₂ W₂ h₂ (t.ofSubmodules W₂ W₂ h₂ w) : U) = w := by
    rw [LinearEquiv.ofSubmodules_apply, LinearEquiv.ofSubmodules_apply, ← LinearEquiv.mul_apply,
      htt]
    rfl
  have hXw : t.ofSubmodules W₂ W₂ h₂ (t.ofSubmodules W₂ W₂ h₂ w) = w := Subtype.ext hcoe
  rw [hXw]
  simp

private theorem finrank_range_subquotEquiv_sub_one_le {W₁ W₂ : Submodule (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U}
    (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁) (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (ht : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1) :
    (Module.finrank (ZMod p) (LinearMap.range
      ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) ≤ 1) ∧
      FiniteDimensional (ZMod p) (LinearMap.range
        ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) := by
  let D : Submodule (ZMod p) ↥W₂ := W₁.comap W₂.subtype
  set s : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂ :=
    (subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1 with hs
  set T : ↥W₂ →ₗ[ZMod p] ↥W₂ := (t.ofSubmodules W₂ W₂ h₂).toLinearMap - 1 with hT
  have : FiniteDimensional (ZMod p) (HardMathSupport.Kantor79.movedSpace t) :=
    FiniteDimensional.of_finrank_pos (by rw [ht]; norm_num)
  have hstep : ∀ w : ↥W₂, s (Submodule.Quotient.mk w) = Submodule.mkQ D (T w) := by
    intro w
    rw [hs, hT]
    change subquotEquiv W₁ W₂ t h₁ h₂ (Submodule.Quotient.mk w) - Submodule.Quotient.mk w =
      Submodule.mkQ D ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w - w)
    rw [subquotEquiv_mk]
    rfl
  have hle : LinearMap.range s ≤ (LinearMap.range T).map (Submodule.mkQ D) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact Submodule.mem_map.mpr ⟨T w, ⟨w, rfl⟩, (hstep w).symm⟩
  have hleT : LinearMap.range T ≤ (HardMathSupport.Kantor79.movedSpace t).comap W₂.subtype := by
    rintro y ⟨w, rfl⟩
    rw [Submodule.mem_comap]
    exact ⟨w, by rw [hT]; rfl⟩
  have hleT' : (LinearMap.range T).map W₂.subtype ≤ HardMathSupport.Kantor79.movedSpace t :=
    Submodule.map_le_iff_le_comap.mpr hleT
  have hfin' : FiniteDimensional (ZMod p) ((LinearMap.range T).map W₂.subtype) :=
    Submodule.finiteDimensional_of_le hleT'
  have hfinT : FiniteDimensional (ZMod p) (LinearMap.range T) :=
    LinearEquiv.finiteDimensional (Submodule.equivSubtypeMap W₂ (LinearMap.range T)).symm
  have hfrT : Module.finrank (ZMod p) (LinearMap.range T) ≤ 1 := by
    have h1 : Module.finrank (ZMod p) (LinearMap.range T) =
        Module.finrank (ZMod p) ((LinearMap.range T).map W₂.subtype) :=
      (Submodule.finrank_map_subtype_eq W₂ (LinearMap.range T)).symm
    rw [h1]
    exact (Submodule.finrank_mono hleT').trans (le_of_eq ht)
  have hmain : Module.finrank (ZMod p) (LinearMap.range s) ≤ 1 := by
    calc Module.finrank (ZMod p) (LinearMap.range s)
        ≤ Module.finrank (ZMod p) ((LinearMap.range T).map (Submodule.mkQ D)) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank (ZMod p) (LinearMap.range T) := Submodule.finrank_map_le _ _
      _ ≤ 1 := hfrT
  exact ⟨hmain, Submodule.finiteDimensional_of_le hle⟩

private theorem apply_eq_neg_of_mem_movedSpace {t : U ≃ₗ[ZMod p] U} (htt : t * t = 1)
    {a : U} (ha : a ∈ HardMathSupport.Kantor79.movedSpace t) : t a = -a := by
  obtain ⟨v, rfl⟩ := ha
  rw [LinearMap.sub_apply, Module.End.one_apply]
  have h1 : t ((t : U →ₗ[ZMod p] U) v) = v := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) htt
    simpa [LinearEquiv.mul_apply] using h
  rw [map_sub, h1]
  abel

theorem isRefl_subquotEquiv_or_eq_one {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁)
    (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂) :
    IsRefl p (subquotEquiv W₁ W₂ t h₁ h₂) ∨ subquotEquiv W₁ W₂ t h₁ h₂ = 1 := by
  obtain ⟨hfr, hfin⟩ := finrank_range_subquotEquiv_sub_one_le (t := t) h₁ h₂ ht.2
  have hss : subquotEquiv W₁ W₂ t h₁ h₂ * subquotEquiv W₁ W₂ t h₁ h₂ = 1 :=
    subquotEquiv_mul_self h₁ h₂ ht.1
  rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) (LinearMap.range
      ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1))) with h0 | hpos
  · right
    have hfinI := hfin
    have hbot : LinearMap.range
        ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      exact h0
    have hz : (subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1 = 0 :=
      LinearMap.range_eq_bot.mp hbot
    have hz' : (subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) = 1 :=
      sub_eq_zero.mp hz
    refine LinearEquiv.ext fun x => ?_
    have := congrArg (fun f : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂ => f x) hz'
    simpa using this
  · left
    refine ⟨hss, ?_⟩
    change Module.finrank (ZMod p) (LinearMap.range
      ((subquotEquiv W₁ W₂ t h₁ h₂ : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) = 1
    omega

private theorem exists_mem_movedSpace_not_mem_of_isRefl_subquotEquiv {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) {W₁ W₂ : Submodule (ZMod p) U}
    (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁) (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (hs : IsRefl p (subquotEquiv W₁ W₂ t h₁ h₂)) :
    ∃ a : U, a ≠ 0 ∧ a ∈ HardMathSupport.Kantor79.movedSpace t ∧ a ∈ W₂ ∧ a ∉ W₁ := by
  have hmv : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  have : FiniteDimensional (ZMod p) (HardMathSupport.Kantor79.movedSpace t) :=
    FiniteDimensional.of_finrank_pos (by rw [hmv]; norm_num)
  obtain ⟨hfr, hfin⟩ := finrank_range_subquotEquiv_sub_one_le (t := t) h₁ h₂ hmv
  change Module.finrank (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
    Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) ≤ 1 at hfr
  have : FiniteDimensional (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) := hfin
  have hne : LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1) ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    have h2 := hs.2
    change Module.finrank (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) = 1 at h2
    omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hTw : ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w - w) ∉ W₁.comap W₂.subtype := by
    intro hmem
    refine hx0 ?_
    rw [subquotEquiv_sub_one_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
  have hnotW₁ : ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w - w : U) ∉ W₁ := by
    intro hmem
    exact hTw (by rw [Submodule.mem_comap]; exact hmem)
  have hTw0 : ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w - w : ↥W₂) ≠ 0 := by
    intro h0
    exact hTw (by rw [h0]; exact Submodule.zero_mem _)
  let aU : U := ((t.ofSubmodules W₂ W₂ h₂).toLinearMap w : U) - (w : U)
  have haU0 : aU ≠ 0 := by
    intro h0
    apply hTw0
    apply Subtype.ext
    simpa [aU, map_sub] using h0
  have haU_mem : aU ∈ HardMathSupport.Kantor79.movedSpace t :=
    ⟨(w : U), by simp [aU, LinearMap.sub_apply, LinearEquiv.ofSubmodules_apply]⟩
  have haU_W₂ : aU ∈ W₂ := by
    simp only [aU]
    exact W₂.sub_mem (t.ofSubmodules W₂ W₂ h₂ w).2 w.2
  exact ⟨aU, haU0, haU_mem, haU_W₂, hnotW₁⟩

private theorem movedSpace_le_of_isRefl_subquotEquiv {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁)
    (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (hs : IsRefl p (subquotEquiv W₁ W₂ t h₁ h₂)) :
    HardMathSupport.Kantor79.movedSpace t ≤ W₂ ∧
      ¬ HardMathSupport.Kantor79.movedSpace t ≤ W₁ := by
  obtain ⟨a, ha0, ha_mem, ha_W₂, ha_notW₁⟩ :=
    exists_mem_movedSpace_not_mem_of_isRefl_subquotEquiv ht h₁ h₂ hs
  have hmv : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  have hspan : HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ a :=
    eq_span_singleton_of_mem_of_finrank_eq_one hmv ha_mem ha0
  refine ⟨?_, ?_⟩
  · rw [hspan]
    exact (Submodule.span_singleton_le_iff_mem a W₂).mpr ha_W₂
  · intro hle
    exact ha_notW₁ (hle ha_mem)

private theorem isRefl_subquotEquiv_of_movedSpace_le {t : U ≃ₗ[ZMod p] U} (hp : p ≠ 2)
    (ht : IsRefl p t) {W₁ W₂ : Submodule (ZMod p) U}
    (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁) (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂)
    (hmove : HardMathSupport.Kantor79.movedSpace t ≤ W₂)
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace t ≤ W₁) :
    IsRefl p (subquotEquiv W₁ W₂ t h₁ h₂) := by
  obtain ⟨hfr, hfin⟩ := finrank_range_subquotEquiv_sub_one_le (t := t) h₁ h₂ ht.2
  change Module.finrank (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
    Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) ≤ 1 at hfr
  have : FiniteDimensional (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) := hfin
  refine ⟨subquotEquiv_mul_self h₁ h₂ ht.1, ?_⟩
  have hne : LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1) ≠ ⊥ := by
    obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hnot
    have haW₂ : a ∈ W₂ := hmove ha
    have hneg : t a = -a := apply_eq_neg_of_mem_movedSpace ht.1 ha
    let a' : ↥W₂ := ⟨-a, W₂.neg_mem haW₂⟩
    have hneg' : t (-a) = a := by rw [map_neg, hneg, neg_neg]
    have hval : ((t.ofSubmodules W₂ W₂ h₂) a' : U) - (a' : U) = (2 : ZMod p) • a := by
      change t (-a) - (-a) = (2 : ZMod p) • a
      rw [hneg', sub_neg_eq_add, two_smul]
    have hnotmem : (t.ofSubmodules W₂ W₂ h₂ a' - a') ∉ W₁.comap W₂.subtype := by
      intro hmem
      rw [Submodule.mem_comap] at hmem
      change ((t.ofSubmodules W₂ W₂ h₂) a' : U) - (a' : U) ∈ W₁ at hmem
      rw [hval] at hmem
      apply hna
      have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
      exact (W₁.smul_mem_iff h2).mp hmem
    intro hbot
    have hz0 : ((subquotEquiv W₁ W₂ t h₁ h₂ :
        Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1) = 0 :=
      LinearMap.range_eq_bot.mp hbot
    have hz : ((subquotEquiv W₁ W₂ t h₁ h₂ :
        Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)
        (Submodule.Quotient.mk a') = 0 := by
      rw [hz0]; rfl
    rw [subquotEquiv_sub_one_mk] at hz
    exact hnotmem ((Submodule.Quotient.mk_eq_zero _).mp hz)
  have hpos : 1 ≤ Module.finrank (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
      Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) :=
    Submodule.one_le_finrank_iff.mpr hne
  change Module.finrank (ZMod p) (LinearMap.range ((subquotEquiv W₁ W₂ t h₁ h₂ :
    Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) = 1
  omega

theorem isRefl_subquotEquiv_iff (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : W₁.map (t : U →ₗ[ZMod p] U) = W₁)
    (h₂ : W₂.map (t : U →ₗ[ZMod p] U) = W₂) :
    IsRefl p (subquotEquiv W₁ W₂ t h₁ h₂) ↔
      HardMathSupport.Kantor79.movedSpace t ≤ W₂ ∧
        ¬ HardMathSupport.Kantor79.movedSpace t ≤ W₁ :=
  ⟨movedSpace_le_of_isRefl_subquotEquiv ht h₁ h₂,
    fun ⟨hmove, hnot⟩ => isRefl_subquotEquiv_of_movedSpace_le hp ht h₁ h₂ hmove hnot⟩

private theorem pow_prime_eq_self_of_mul_self (hp : p ≠ 2)
    {W₁ W₂ : Submodule (ZMod p) U}
    {u : Subquot W₁ W₂ ≃ₗ[ZMod p] Subquot W₁ W₂} (hu : u * u = 1) : u ^ p = u := by
  have hpodd : p ≡ 1 [MOD 2] := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp)
    rw [Nat.ModEq]
    omega
  have hu2 : u ^ 2 = 1 := by rwa [pow_two]
  have := pow_eq_pow_of_modEq (x := u) hpodd hu2
  simpa using this

theorem pow_prime_eq_one_of_subquotHom_eq_one {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W₁ W₂ : Submodule (ZMod p) U} (hp : p ≠ 2)
    (h₁ : ∀ g ∈ H, W₁.map (g : U →ₗ[ZMod p] U) = W₁)
    (h₂ : ∀ g ∈ H, W₂.map (g : U →ₗ[ZMod p] U) = W₂)
    (hW₁ : ∀ g ∈ H, ∀ w ∈ W₁, g w = w) (hW₂ : ∀ g ∈ H, ∀ v, g v - v ∈ W₂)
    {k : H} (hk : subquotHom H W₁ W₂ h₁ h₂ k = 1) : k ^ p = 1 := by
  have hkQ1 : ∀ w ∈ W₂, (k : U ≃ₗ[ZMod p] U) w - w ∈ W₁ :=
    (subquotEquiv_eq_one_iff (h₁ k k.2) (h₂ k k.2)).mp hk
  set N : Module.End (ZMod p) U := (k : U →ₗ[ZMod p] U) - 1 with hN
  have hNmemW₁ : ∀ w ∈ W₁, N w = 0 := by
    intro w hw
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
    have hw' : (k : U →ₗ[ZMod p] U) w = w := by simpa using hW₁ k k.2 w hw
    rw [hw', sub_self]
  have hNmemW₂ : ∀ v, N v ∈ W₂ := by
    intro v
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
    exact hW₂ k k.2 v
  have hN3 : N ^ 3 = 0 := by
    ext v
    have h1 : N v ∈ W₂ := hNmemW₂ v
    have h2 : N (N v) ∈ W₁ := by
      rw [hN, LinearMap.sub_apply, Module.End.one_apply]
      exact hkQ1 (N v) h1
    have h3 : N (N (N v)) = 0 := hNmemW₁ (N (N v)) h2
    show N (N (N v)) = 0
    exact h3
  have hNp : N ^ p = 0 := by
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    obtain ⟨m, rfl⟩ : ∃ m, p = 3 + m := ⟨p - 3, by omega⟩
    rw [pow_add, hN3, zero_mul]
  have hp0 : (p : Module.End (ZMod p) U) = 0 := by
    have h1 : (p : Module.End (ZMod p) U) =
        algebraMap (ZMod p) (Module.End (ZMod p) U) (p : ZMod p) := by
      rw [map_natCast]
    rw [h1, ZMod.natCast_self, map_zero]
  have hkp : ((k : U →ₗ[ZMod p] U)) ^ p = 1 := by
    have hk_eq : (k : U →ₗ[ZMod p] U) = 1 + N := by rw [hN]; abel
    rw [hk_eq]
    have hcomm : Commute (1 : Module.End (ZMod p) U) N := Commute.one_left N
    rw [hcomm.add_pow_prime_eq (Fact.out : p.Prime), one_pow, hNp]
    simp [hp0]
  apply Subtype.ext
  show (k : U ≃ₗ[ZMod p] U) ^ p = 1
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun f : U →ₗ[ZMod p] U => f v) hkp
  simpa [LinearEquiv.pow_apply, Module.End.pow_apply] using this

private theorem movedSpace_comap_map_mkQ_eq_range {s : U ≃ₗ[ZMod p] U}
    (hp : p ≠ 2) (hss : s * s = 1) {W₁ W₂ : Submodule (ZMod p) U}
    (h₁' : W₁.map (s : U →ₗ[ZMod p] U) = W₁) (h₂' : W₂.map (s : U →ₗ[ZMod p] U) = W₂) :
    ((HardMathSupport.Kantor79.movedSpace s).comap W₂.subtype).map
        (Submodule.mkQ (W₁.comap W₂.subtype)) =
      LinearMap.range ((subquotEquiv W₁ W₂ s h₁' h₂' :
        Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1) := by
  let D : Submodule (ZMod p) ↥W₂ := W₁.comap W₂.subtype
  let E : Submodule (ZMod p) ↥W₂ := (HardMathSupport.Kantor79.movedSpace s).comap W₂.subtype
  change E.map (Submodule.mkQ D) = LinearMap.range
      ((subquotEquiv W₁ W₂ s h₁' h₂' : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)
  ext z
  constructor
  · rintro ⟨x, hxE, rfl⟩
    have hxmv : (x : U) ∈ HardMathSupport.Kantor79.movedSpace s := hxE
    have hsx : s.ofSubmodules W₂ W₂ h₂' x = -x := by
      apply Subtype.ext
      change s (x : U) = -(x : U)
      exact apply_eq_neg_of_mem_movedSpace hss hxmv
    have hTx : (s.ofSubmodules W₂ W₂ h₂').toLinearMap (-x) - (-x) = (2 : ZMod p) • x := by
      change s.ofSubmodules W₂ W₂ h₂' (-x) - (-x) = (2 : ZMod p) • x
      rw [map_neg, hsx, neg_neg, sub_neg_eq_add, two_smul]
    have hz : ((subquotEquiv W₁ W₂ s h₁' h₂' : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)
        (Submodule.Quotient.mk (-x)) = (2 : ZMod p) • Submodule.Quotient.mk x := by
      rw [subquotEquiv_sub_one_mk, hTx]
      rfl
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have hxeq : Submodule.Quotient.mk x =
        (2 : ZMod p)⁻¹ • (((subquotEquiv W₁ W₂ s h₁' h₂' : Subquot W₁ W₂ →ₗ[ZMod p]
          Subquot W₁ W₂) - 1) (Submodule.Quotient.mk (-x))) := by
      rw [hz, smul_smul, inv_mul_cancel₀ h2, one_smul]
    change Submodule.Quotient.mk x ∈ LinearMap.range
      ((subquotEquiv W₁ W₂ s h₁' h₂' : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)
    rw [hxeq]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨(s.ofSubmodules W₂ W₂ h₂').toLinearMap w - w, ?_, ?_⟩
    · change (s.ofSubmodules W₂ W₂ h₂').toLinearMap w - w ∈
        (HardMathSupport.Kantor79.movedSpace s).comap W₂.subtype
      rw [Submodule.mem_comap]
      exact ⟨(w : U), by rw [LinearMap.sub_apply]; rfl⟩
    · exact (subquotEquiv_sub_one_mk h₁' h₂' w).symm.trans hy

private theorem finrank_movedSpace_eq_finrank_map_comap_mkQ {s : U ≃ₗ[ZMod p] U}
    (hp : p ≠ 2) (hss : s * s = 1) {W₁ W₂ : Submodule (ZMod p) U}
    (hW₁s : ∀ w ∈ W₁, s w = w) (hW₂s : ∀ v, s v - v ∈ W₂) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) =
      Module.finrank (ZMod p) (((HardMathSupport.Kantor79.movedSpace s).comap W₂.subtype).map
        (Submodule.mkQ (W₁.comap W₂.subtype))) := by
  let D : Submodule (ZMod p) ↥W₂ := W₁.comap W₂.subtype
  let E : Submodule (ZMod p) ↥W₂ := (HardMathSupport.Kantor79.movedSpace s).comap W₂.subtype
  change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) =
    Module.finrank (ZMod p) (E.map (Submodule.mkQ D))
  have hle : HardMathSupport.Kantor79.movedSpace s ≤ W₂ := by
    rintro _ ⟨v, rfl⟩
    exact hW₂s v
  have hEs : E.map W₂.subtype = HardMathSupport.Kantor79.movedSpace s := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  have hEbot : E ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxD⟩ := Submodule.mem_inf.mp hx
    have hxW₁ : (x : U) ∈ W₁ := hxD
    have hxmv : (x : U) ∈ HardMathSupport.Kantor79.movedSpace s := hxE
    have hneg : s (x : U) = -(x : U) := apply_eq_neg_of_mem_movedSpace hss hxmv
    have hfix : s (x : U) = (x : U) := hW₁s (x : U) hxW₁
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have haeq : (x : U) = -(x : U) := hfix.symm.trans hneg
    have hzero : (2 : ZMod p) • (x : U) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [haeq]
      rw [add_neg_cancel]
    exact Subtype.ext ((smul_eq_zero.mp hzero).resolve_left h2)
  have hfr1 : Module.finrank (ZMod p) E =
      Module.finrank (ZMod p) (E.map (Submodule.mkQ D)) := by
    have hinj : Function.Injective ((Submodule.mkQ D).domRestrict E) := by
      rw [← LinearMap.ker_eq_bot]
      rw [LinearMap.ker_domRestrict]
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_comap] at hx
      rw [Submodule.ker_mkQ] at hx
      have hxinf : (x : ↥W₂) ∈ E ⊓ D := Submodule.mem_inf.mpr ⟨x.2, hx⟩
      have hx0 : (x : ↥W₂) = 0 := by simpa using hEbot.le hxinf
      exact Subtype.ext hx0
    have := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at this
    exact this.symm
  have hfr2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) =
      Module.finrank (ZMod p) E := by
    rw [← hEs, Submodule.finrank_map_subtype_eq]
  rw [hfr2, hfr1]

theorem finrank_movedSpace_of_isRefl_subquot {s : U ≃ₗ[ZMod p] U}
    (hp : p ≠ 2) (hss : s * s = 1) {W₁ W₂ : Submodule (ZMod p) U}
    (h₁' : W₁.map (s : U →ₗ[ZMod p] U) = W₁) (h₂' : W₂.map (s : U →ₗ[ZMod p] U) = W₂)
    (hW₁s : ∀ w ∈ W₁, s w = w) (hW₂s : ∀ v, s v - v ∈ W₂)
    (hsbar : Module.finrank (ZMod p) (LinearMap.range
      ((subquotEquiv W₁ W₂ s h₁' h₂' : Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) = 1) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) = 1 := by
  have hEmap := movedSpace_comap_map_mkQ_eq_range (s := s) hp hss h₁' h₂'
  have hfr := finrank_movedSpace_eq_finrank_map_comap_mkQ (s := s) hp hss hW₁s hW₂s
  rw [hfr, hEmap, hsbar]

theorem isRefl_subquotHom (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : ∀ g ∈ H, W₁.map (g : U →ₗ[ZMod p] U) = W₁)
    (h₂ : ∀ g ∈ H, W₂.map (g : U →ₗ[ZMod p] U) = W₂) (hW₁ : ∀ g ∈ H, ∀ w ∈ W₁, g w = w)
    (hW₂ : ∀ g ∈ H, ∀ v, g v - v ∈ W₂) {t : H} (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    IsRefl p (subquotHom H W₁ W₂ h₁ h₂ t) := by
  have hmove : HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) ≤ W₂ := by
    rintro _ ⟨v, rfl⟩
    exact hW₂ t t.2 v
  have hnot : ¬ HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) ≤ W₁ := by
    intro hle
    have hmv : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
        (t : U ≃ₗ[ZMod p] U)) = 1 := ht.2
    have hne : HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hmv
      exact one_ne_zero hmv.symm
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hne
    have hfix : (t : U ≃ₗ[ZMod p] U) a = a := hW₁ t t.2 a (hle ha)
    have hneg : (t : U ≃ₗ[ZMod p] U) a = -a := apply_eq_neg_of_mem_movedSpace ht.1 ha
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have haeq : a = -a := hfix.symm.trans hneg
    have hzero : (2 : ZMod p) • a = 0 := by
      rw [two_smul]
      nth_rewrite 2 [haeq]
      rw [add_neg_cancel]
    exact ha0 ((smul_eq_zero.mp hzero).resolve_left h2)
  exact (isRefl_subquotEquiv_iff hp ht (h₁ t t.2) (h₂ t t.2)).mpr ⟨hmove, hnot⟩

theorem exists_isRefl_subquotHom_eq (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : ∀ g ∈ H, W₁.map (g : U →ₗ[ZMod p] U) = W₁)
    (h₂ : ∀ g ∈ H, W₂.map (g : U →ₗ[ZMod p] U) = W₂) (hW₁ : ∀ g ∈ H, ∀ w ∈ W₁, g w = w)
    (hW₂ : ∀ g ∈ H, ∀ v, g v - v ∈ W₂) {g : H} (hg : IsRefl p (subquotHom H W₁ W₂ h₁ h₂ g)) :
    ∃ t : H, IsRefl p (t : U ≃ₗ[ZMod p] U) ∧
      subquotHom H W₁ W₂ h₁ h₂ t = subquotHom H W₁ W₂ h₁ h₂ g := by
  refine ⟨g ^ p, ?_, ?_⟩
  · have hgp2 : (g ^ p) ^ 2 = 1 := by
      have hg2ker : subquotHom H W₁ W₂ h₁ h₂ (g ^ 2) = 1 := by
        rw [map_pow, pow_two, hg.1]
      have hg2p : (g ^ 2) ^ p = 1 := pow_prime_eq_one_of_subquotHom_eq_one hp h₁ h₂ hW₁ hW₂ hg2ker
      rw [← pow_mul, mul_comm p 2, pow_mul, hg2p]
    have hgp2' : ((g ^ p : H) : U ≃ₗ[ZMod p] U) * ((g ^ p : H) : U ≃ₗ[ZMod p] U) = 1 := by
      have := congrArg (fun x : H => (x : U ≃ₗ[ZMod p] U)) hgp2
      simpa [pow_two, map_pow] using this
    have hφ : subquotEquiv W₁ W₂ (g ^ p) (h₁ (g ^ p) (g ^ p).2) (h₂ (g ^ p) (g ^ p).2) =
        subquotHom H W₁ W₂ h₁ h₂ g := by
      change subquotHom H W₁ W₂ h₁ h₂ (g ^ p) = subquotHom H W₁ W₂ h₁ h₂ g
      rw [map_pow, pow_prime_eq_self_of_mul_self hp hg.1]
    have hsbar : Module.finrank (ZMod p) (LinearMap.range
        ((subquotEquiv W₁ W₂ (g ^ p) (h₁ (g ^ p) (g ^ p).2) (h₂ (g ^ p) (g ^ p).2) :
          Subquot W₁ W₂ →ₗ[ZMod p] Subquot W₁ W₂) - 1)) = 1 := by
      rw [hφ]
      exact hg.2
    have hfr := finrank_movedSpace_of_isRefl_subquot hp hgp2' (h₁ (g ^ p) (g ^ p).2)
      (h₂ (g ^ p) (g ^ p).2) (hW₁ (g ^ p) (g ^ p).2) (hW₂ (g ^ p) (g ^ p).2) hsbar
    exact ⟨hgp2', hfr⟩
  · rw [map_pow, pow_prime_eq_self_of_mul_self hp hg.1]

theorem exists_isRefl_closure_eq_of_injective (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W₁ W₂ : Submodule (ZMod p) U} (h₁ : ∀ g ∈ H, W₁.map (g : U →ₗ[ZMod p] U) = W₁)
    (h₂ : ∀ g ∈ H, W₂.map (g : U →ₗ[ZMod p] U) = W₂) (hW₁ : ∀ g ∈ H, ∀ w ∈ W₁, g w = w)
    (hW₂ : ∀ g ∈ H, ∀ v, g v - v ∈ W₂)
    (hinj : Function.Injective (subquotHom H W₁ W₂ h₁ h₂)) {ι : Type*}
    (x : ι → (Subquot W₁ W₂ ≃ₗ[ZMod p] Subquot W₁ W₂)) (hx : ∀ i, IsRefl p (x i))
    (hgen : (subquotHom H W₁ W₂ h₁ h₂).range = Subgroup.closure (Set.range x)) :
    ∃ y : ι → H, (∀ i, IsRefl p (y i : U ≃ₗ[ZMod p] U) ∧ subquotHom H W₁ W₂ h₁ h₂ (y i) = x i) ∧
      H = Subgroup.closure (Set.range fun i => (y i : U ≃ₗ[ZMod p] U)) := by
  choose z hz using fun i => (show x i ∈ (subquotHom H W₁ W₂ h₁ h₂).range from by
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩)
  choose y hy using fun i => exists_isRefl_subquotHom_eq hp h₁ h₂ hW₁ hW₂
    (g := z i) (by rw [hz i]; exact hx i)
  refine ⟨y, fun i => ⟨(hy i).1, by rw [(hy i).2, hz i]⟩, ?_⟩
  have hcl : Subgroup.map (subquotHom H W₁ W₂ h₁ h₂) (Subgroup.closure (Set.range y)) =
      Subgroup.closure (Set.range x) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext w
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, ((hy i).2.trans (hz i)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨y i, ⟨i, rfl⟩, (hy i).2.trans (hz i)⟩
  have hmapK : Subgroup.map (subquotHom H W₁ W₂ h₁ h₂) (Subgroup.closure (Set.range y)) =
      Subgroup.map (subquotHom H W₁ W₂ h₁ h₂) ⊤ := by
    rw [hcl, ← MonoidHom.range_eq_map]
    exact hgen.symm
  have hK : Subgroup.closure (Set.range y) = ⊤ :=
    Subgroup.map_injective hinj hmapK
  have hKmap : (Subgroup.closure (Set.range y)).map H.subtype =
      Subgroup.closure (Set.range fun i => (y i : U ≃ₗ[ZMod p] U)) := by
    rw [MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp']
    rfl
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hKmap, hK, htop]

end Prime

end CFSG.StandardType.ZS
