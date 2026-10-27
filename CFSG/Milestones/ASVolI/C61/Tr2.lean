module

public import CFSG.Milestones.ASVolI.C61.Tr1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {A B : Type} [Group A] [Group B] {f : A →* B} (hf : Function.Injective f)
include hf

theorem burnsideC56_tr_map_subgroupOf (X Y : Subgroup A) :
    (Y.subgroupOf X).map (X.equivMapOfInjective f hf).toMonoidHom = (Y.map f).subgroupOf (X.map f) := by
  ext b
  constructor
  · rintro ⟨a, hay, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    show ((X.equivMapOfInjective f hf a : ↥(X.map f)) : B) ∈ Y.map f
    rw [Subgroup.coe_equivMapOfInjective_apply]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mp hay)
  · intro hbY
    obtain ⟨a, rfl⟩ := (X.equivMapOfInjective f hf).surjective b
    refine ⟨a, ?_, rfl⟩
    show a ∈ Y.subgroupOf X
    rw [Subgroup.mem_subgroupOf] at hbY ⊢
    rw [Subgroup.coe_equivMapOfInjective_apply] at hbY
    exact (Subgroup.mem_map_iff_mem hf).mp hbY

theorem burnsideC56_tr_quotHas (L N : Subgroup A) (P : ∀ (Y : Type) [Group Y], Prop) :
    QuotHas (L.map f) (N.map f) P ↔ QuotHas L N P := by
  let e : L ≃* (L.map f) := L.equivMapOfInjective f hf
  have hk : (N.subgroupOf L).map e.toMonoidHom = (N.map f).subgroupOf (L.map f) :=
    burnsideC56_tr_map_subgroupOf hf L N
  unfold QuotHas
  constructor
  · rintro ⟨Y, _, φ, hφ, hker, hP⟩
    refine ⟨Y, inferInstance, φ.comp e.toMonoidHom, hφ.comp e.surjective, ?_, hP⟩
    rw [← MonoidHom.comap_ker, hker, ← hk,
      Subgroup.comap_map_eq_self_of_injective e.injective]
  · rintro ⟨Y, _, φ, hφ, hker, hP⟩
    refine ⟨Y, inferInstance, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_, hP⟩
    rw [← MonoidHom.comap_ker, hker, ← hk]
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy

theorem burnsideC56_tr_blockQ (L : Subgroup A) : blockQ (L.map f) = (blockQ L).map f :=
  burnsideC56_tr_pCoreOf hf 2 L

theorem burnsideC56_tr_blockU (L : Subgroup A) : blockU (L.map f) = (blockU L).map f := by
  unfold blockU
  rw [burnsideC56_tr_blockQ hf, Subgroup.map_commutator]

theorem burnsideC56_tr_blockZ (L : Subgroup A) : blockZ (L.map f) = (blockZ L).map f := by
  unfold blockZ
  rw [burnsideC56_tr_blockU hf, ← burnsideC56_tr_centralizer hf]

omit hf in
theorem burnsideC56_tr_noTwoQuot {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤) :
    ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → N = ⊤ := by
  intro N _ hN
  have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
  have h2 : IsPGroup 2 (X ⧸ N.comap e.toMonoidHom) :=
    hN.of_equiv (QuotientGroup.congr _ _ e hmap).symm
  rw [← hmap, h _ h2, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

omit hf in
theorem burnsideC56_tr_qs {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X) ∨ Nat.card (X ⧸ CFSG.pCore 2 X) = 3) :
    CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y) ∨ Nat.card (Y ⧸ CFSG.pCore 2 Y) = 3 := by
  have e' := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
  rcases h with hq | hp
  · exact Or.inl (hq.of_mulEquiv e'.symm)
  · exact Or.inr (by rwa [← Nat.card_congr e'.toEquiv])

theorem burnsideC56_tr_irr_fwd {L : Subgroup A}
    (h : ∀ W : Subgroup A, blockZ L ≤ W → W ≤ blockU L → L ≤ Subgroup.normalizer (W : Set A) →
      W = blockZ L ∨ W = blockU L) :
    ∀ W : Subgroup B, blockZ (L.map f) ≤ W → W ≤ blockU (L.map f) →
      L.map f ≤ Subgroup.normalizer (W : Set B) → W = blockZ (L.map f) ∨ W = blockU (L.map f) := by
  intro W hZW hWU hLW
  rw [burnsideC56_tr_blockU hf] at hWU ⊢
  rw [burnsideC56_tr_blockZ hf] at hZW ⊢
  have hW := burnsideC56_tr_eq_map_comap hf hWU
  rw [← hW] at hZW hWU hLW ⊢
  rw [Subgroup.map_le_map_iff_of_injective hf] at hZW hWU
  have hLW₀ : L ≤ Subgroup.normalizer ((W.comap f : Subgroup A) : Set A) := by
    have h1 : (L ⊓ Subgroup.normalizer ((W.comap f : Subgroup A) : Set A)).map f = L.map f := by
      rw [burnsideC56_tr_normalizer hf]
      exact inf_eq_left.mpr hLW
    have h2 := (Subgroup.map_injective hf) (h1.trans (by rfl))
    exact inf_eq_left.mp h2
  rcases h _ hZW hWU hLW₀ with h3 | h3
  · exact Or.inl (by rw [h3])
  · exact Or.inr (by rw [h3])

theorem burnsideC56_tr_irr_bwd {L : Subgroup A}
    (h : ∀ W : Subgroup B, blockZ (L.map f) ≤ W → W ≤ blockU (L.map f) →
      L.map f ≤ Subgroup.normalizer (W : Set B) → W = blockZ (L.map f) ∨ W = blockU (L.map f)) :
    ∀ W : Subgroup A, blockZ L ≤ W → W ≤ blockU L → L ≤ Subgroup.normalizer (W : Set A) →
      W = blockZ L ∨ W = blockU L := by
  intro W hZW hWU hLW
  have hLW' : L.map f ≤ Subgroup.normalizer ((W.map f : Subgroup B) : Set B) := by
    have := Subgroup.map_mono (f := f) (le_inf le_rfl hLW)
    rw [burnsideC56_tr_normalizer hf] at this
    exact this.trans inf_le_right
  rcases h (W.map f) (by rw [burnsideC56_tr_blockZ hf]; exact Subgroup.map_mono hZW)
    (by rw [burnsideC56_tr_blockU hf]; exact Subgroup.map_mono hWU) hLW' with h3 | h3
  · rw [burnsideC56_tr_blockZ hf] at h3
    exact Or.inl ((Subgroup.map_injective hf) h3)
  · rw [burnsideC56_tr_blockU hf] at h3
    exact Or.inr ((Subgroup.map_injective hf) h3)

theorem burnsideC56_tr_isShort2 (L : Subgroup A) : IsShort2 (L.map f) ↔ IsShort2 L := by
  let e : L ≃* (L.map f) := L.equivMapOfInjective f hf
  unfold IsShort2
  rw [burnsideC56_tr_charTwo hf, burnsideC56_tr_blockU hf, burnsideC56_tr_blockQ hf,
    burnsideC56_tr_blockZ hf, ← burnsideC56_tr_centralizer hf,
    Subgroup.map_le_map_iff_of_injective hf, Subgroup.map_lt_map_iff_of_injective hf]
  have hsq : (∀ x ∈ (blockU L).map f, x ^ 2 = 1) ↔ ∀ x ∈ blockU L, x ^ 2 = 1 := by
    constructor
    · intro h x hx
      have := h (f x) (Subgroup.mem_map_of_mem f hx)
      rw [← map_pow] at this
      exact hf (this.trans (map_one f).symm)
    · rintro h _ ⟨x, hx, rfl⟩
      rw [← map_pow, h x hx, map_one]
  rw [hsq]
  have hirr := @burnsideC56_tr_irr_fwd A B _ _ f hf L
  have hirr' := @burnsideC56_tr_irr_bwd A B _ _ f hf L
  rw [burnsideC56_tr_blockU hf, burnsideC56_tr_blockZ hf] at hirr hirr'
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨burnsideC56_tr_noTwoQuot e.symm h1, h2, h3, burnsideC56_tr_qs e.symm h4, h5, hirr' h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨burnsideC56_tr_noTwoQuot e h1, h2, h3, burnsideC56_tr_qs e h4, h5, hirr h6⟩

theorem burnsideC56_tr_isBlock2 (X L : Subgroup A) : IsBlock2 (X.map f) (L.map f) ↔ IsBlock2 X L := by
  unfold IsBlock2
  rw [burnsideC56_tr_isShort2 hf, Subgroup.map_le_map_iff_of_injective hf,
    ← burnsideC56_tr_map_subgroupOf hf X L]
  let e : X ≃* (X.map f) := X.equivMapOfInjective f hf
  have hsub : ((L.subgroupOf X).map e.toMonoidHom).IsSubnormal ↔ (L.subgroupOf X).IsSubnormal := by
    constructor
    · intro h
      have := h.map (f := e.symm.toMonoidHom) e.symm.surjective
      rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ by
        ext; simp, Subgroup.map_id] at this
    · intro h
      exact h.map (f := e.toMonoidHom) e.surjective
  rw [hsub]

end CFSG.ASVolI
