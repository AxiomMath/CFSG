module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Conc
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSixStmt
import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace A7Mod

theorem genFittingFStar_normal' (G : Type*) [Group G] : (genFittingFStar G).Normal :=
  CFSG.ComponentClassification.GeneralizedFitting.normal G

@[expose] def conjEquiv {V W : Type*} [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid W]
    [Module (ZMod 2) W] (ψ : V ≃ₗ[ZMod 2] W) : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun γ := ψ.symm.trans (γ.trans ψ)
  invFun δ := ψ.trans (δ.trans ψ.symm)
  left_inv γ := LinearEquiv.ext fun x => by simp
  right_inv δ := LinearEquiv.ext fun x => by simp
  map_mul' γ δ := LinearEquiv.ext fun x => by
    simp [LinearEquiv.mul_apply]

theorem conjEquiv_apply {V W : Type*} [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid W]
    [Module (ZMod 2) W] (ψ : V ≃ₗ[ZMod 2] W) (γ : V ≃ₗ[ZMod 2] V) (x : W) :
    conjEquiv ψ γ x = ψ (γ (ψ.symm x)) := rfl

theorem isSylowTwoOf_of_map {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {S H : Subgroup G} (h : IsSylowTwoOf (S.map f) (H.map f)) :
    IsSylowTwoOf S H := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 hle,
    hp.of_equiv (S.equivMapOfInjective f hf).symm, ?_⟩
  show ¬ 2 ∣ S.relIndex H
  rw [← Subgroup.relIndex_map_map_of_injective S H hf]
  exact hidx

theorem isSylowTwoOf_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.of_equiv (S.equivMapOfInjective _ e.injective), ?_⟩
  show ¬ 2 ∣ (S.map e.toMonoidHom).relIndex (H.map e.toMonoidHom)
  rw [Subgroup.relIndex_map_map_of_injective S H e.injective]
  exact hidx

theorem a7NatFact12813_of_raw (h : A7Raw) : A7NatFact12813 := by
  intro V _ _ _ B Γ S v hC4 halt hnd hinv hS hv0 hSv
  classical
  obtain ⟨-, φ, ψ, hψ⟩ := hC4
  set c := conjEquiv ψ with hcdef
  set F := (genFittingFStar ↥Γ).map Γ.subtype with hFdef
  have hcF : ∀ γ : ↥(genFittingFStar ↥Γ),
      c ((γ : ↥Γ) : V ≃ₗ[ZMod 2] V) = pAct (φ γ : Equiv.Perm (Fin 7)) := by
    intro γ
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    rw [conjEquiv_apply]
    have h1 := hψ γ (ψ.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hpA7 : pA7 = F.map c.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨γ, hγ⟩ := φ.surjective ⟨σ, hσ⟩
      refine ⟨((γ : ↥Γ) : V ≃ₗ[ZMod 2] V), ⟨γ, γ.2, rfl⟩, ?_⟩
      show c _ = pAct σ
      rw [hcF, hγ]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨φ ⟨γ, hγ⟩, (φ ⟨γ, hγ⟩).2, (hcF ⟨γ, hγ⟩).symm⟩
  set Γ' := Γ.map c.toMonoidHom with hΓ'def
  have hFΓ : F ≤ Γ := Subgroup.map_subtype_le _
  have hle1 : pA7 ≤ Γ' := hpA7 ▸ Subgroup.map_mono hFΓ
  have hΓF : Γ ≤ Subgroup.normalizer (F : Set (V ≃ₗ[ZMod 2] V)) := by
    have := genFittingFStar_normal' ↥Γ
    have h1 := Subgroup.le_normalizer_map (H := genFittingFStar ↥Γ) Γ.subtype
    rw [Subgroup.normalizer_eq_top (genFittingFStar ↥Γ), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have hle2 : Γ' ≤ Subgroup.normalizer (pA7 : Set (V7 ≃ₗ[ZMod 2] V7)) := by
    rw [hpA7]
    exact (Subgroup.map_mono hΓF).trans (Subgroup.le_normalizer_map c.toMonoidHom)
  obtain ⟨K, hK, hΓK⟩ := eq_map_of_le_normalizer (stabCount_of_raw h) hle1 hle2
  set B' : LinearMap.BilinForm (ZMod 2) V7 := B.compl₁₂ ψ.symm.toLinearMap ψ.symm.toLinearMap
    with hB'def
  have hB'apply : ∀ x y, B' x y = B (ψ.symm x) (ψ.symm y) := fun x y => rfl
  have hB' : B' = B0 := by
    refine eq_B0 B' (fun x => by rw [hB'apply]; exact halt _) (fun x hx => ?_) ?_
    · have h1 : ψ.symm x = 0 := hnd _ fun w => by
        have := hx (ψ w)
        rwa [hB'apply, LinearEquiv.symm_apply_apply] at this
      rw [← LinearEquiv.apply_symm_apply ψ x, h1, map_zero]
    · intro σ hσ x y
      have hσF : pAct σ ∈ F.map c.toMonoidHom := hpA7 ▸ ⟨σ, hσ, rfl⟩
      obtain ⟨γ, hγF, hγσ⟩ := hσF
      rw [← hγσ, hB'apply, hB'apply]
      change B (ψ.symm (ψ (γ (ψ.symm x)))) (ψ.symm (ψ (γ (ψ.symm y)))) = _
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact hinv γ (hFΓ hγF) _ _
  set S' := S.map c.toMonoidHom with hS'def
  have hS'syl : IsSylowTwoOf S' Γ' := isSylowTwoOf_map_equiv c hS
  have hS'K : S' ≤ K.map pAct := hΓK ▸ hS'syl.1
  set Sh := S'.comap pAct with hShdef
  have hShmap : Sh.map pAct = S' := by
    rw [hShdef, Subgroup.map_comap_eq, inf_eq_right]
    exact hS'K.trans (Subgroup.map_le_range _ _)
  have hShsyl : IsSylowTwoOf Sh K := by
    apply isSylowTwoOf_of_map pAct_injective
    rw [hShmap, ← hΓK]
    exact hS'syl
  have hv'0 : ψ v ≠ 0 := fun h0 => hv0 (ψ.injective (by rw [h0, map_zero]))
  have hShv : ∀ s ∈ Sh, pAct s (ψ v) = ψ v := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := (hs : pAct s ∈ S')
    rw [← hts]
    change ψ (t (ψ.symm (ψ v))) = ψ v
    rw [LinearEquiv.symm_apply_apply, hSv t ht]
  obtain ⟨U, hUinv, hUorth, hUnot, hUcases⟩ := exists_concl h hK hShsyl (ψ v) hv'0 hShv
  have hmemS' : ∀ s ∈ S, ∃ sh ∈ Sh, pAct sh = c s := by
    intro s hs
    have : c s ∈ S' := ⟨s, hs, rfl⟩
    rw [← hShmap] at this
    obtain ⟨sh, hsh, hshs⟩ := this
    exact ⟨sh, hsh, hshs⟩
  have hA : ∀ k : ℕ, (∀ A : Subgroup (Equiv.Perm (Fin 7)), A ≤ Sh → IsElemAbelian 2 A →
      (∀ a ∈ A, ∀ u ∈ U, pAct a u = u) → Nat.card A ≤ k) →
      ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ S → IsElemAbelian 2 A →
        (∀ a ∈ A, ∀ u ∈ U.comap ψ.toLinearMap, a u = u) → Nat.card A ≤ k := by
    intro k hk A hAS hAel hAU
    set Ah := (A.map c.toMonoidHom).comap pAct with hAhdef
    have hAhmap : Ah.map pAct = A.map c.toMonoidHom := by
      rw [hAhdef, Subgroup.map_comap_eq, inf_eq_right]
      have hS'r : S' ≤ pAct.range := by
        rw [← hShmap]
        exact Subgroup.map_le_range _ _
      exact (Subgroup.map_mono hAS).trans hS'r
    have hcard : Nat.card Ah = Nat.card A := by
      rw [← Subgroup.card_map_of_injective (f := pAct) pAct_injective, hAhmap,
        Subgroup.card_map_of_injective c.injective]
    have hAhel : IsElemAbelian 2 Ah := by
      have h1 := CFSG.SectionRank.isElemAbelian_map hAel c.toMonoidHom
      rw [← hAhmap] at h1
      refine ⟨⟨⟨fun a b => Subtype.ext (pAct_injective ?_)⟩⟩, fun a ha => pAct_injective ?_⟩
      · have := h1.1.is_comm.comm ⟨pAct a, ⟨a, a.2, rfl⟩⟩ ⟨pAct b, ⟨b, b.2, rfl⟩⟩
        have h2 := congrArg Subtype.val this
        simpa using h2
      · have := h1.2 (pAct a) ⟨a, ha, rfl⟩
        simpa using this
    rw [← hcard]
    refine hk Ah (fun a ha => ?_) hAhel fun a ha u hu => ?_
    · obtain ⟨b, hb, hba⟩ := (ha : pAct a ∈ A.map c.toMonoidHom)
      have : pAct a ∈ S' := ⟨b, hAS hb, hba⟩
      exact this
    · obtain ⟨b, hb, hba⟩ := (ha : pAct a ∈ A.map c.toMonoidHom)
      have hu' : ψ.symm u ∈ U.comap ψ.toLinearMap := by
        show ψ (ψ.symm u) ∈ U
        rw [LinearEquiv.apply_symm_apply]
        exact hu
      rw [← hba]
      change ψ (b (ψ.symm u)) = u
      rw [hAU b hb _ hu', LinearEquiv.apply_symm_apply]
  refine ⟨U.comap ψ.toLinearMap, fun s hs u hu => ?_, fun u hu => ?_, fun hv => hUnot hv, ?_⟩
  · obtain ⟨sh, hsh, hshs⟩ := hmemS' s hs
    show ψ (s u) ∈ U
    have h1 : ψ (s u) = c s (ψ u) := by
      rw [conjEquiv_apply, LinearEquiv.symm_apply_apply]
    rw [h1, ← hshs]
    exact hUinv sh hsh _ hu
  · have h1 := hUorth (ψ u) hu
    rw [← hB', hB'apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1
  · rcases hUcases with h2 | ⟨h4, Y, hYK, hYv, hY3, hY9⟩
    · exact Or.inl (hA 2 h2)
    · refine Or.inr ⟨hA 4 h4, (Y.map pAct).map c.symm.toMonoidHom, ?_, ?_,
        CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hY3 _) _, ?_⟩
      · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        have h1 : pAct y ∈ Γ' := hΓK ▸ ⟨y, hYK hy, rfl⟩
        obtain ⟨γ, hγ, hγy⟩ := h1
        rw [← hγy]
        change c.symm (c γ) ∈ Γ
        rw [MulEquiv.symm_apply_apply]
        exact hγ
      · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        change ψ.symm (pAct y (ψ v)) = v
        rw [hYv y hy, LinearEquiv.symm_apply_apply]
      · rw [Subgroup.card_map_of_injective c.symm.injective,
          Subgroup.card_map_of_injective pAct_injective, hY9]

end A7Mod

end CFSG.Quasithin.H13
