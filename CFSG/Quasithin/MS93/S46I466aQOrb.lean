module

public import CFSG.Quasithin.MS93.S46I466aQLin
public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix

section Lin

variable {F : Type} [Field F]

theorem rootElt01_mul_rootElt02_mulVec (a b : F) (w : Fin 3 → F) :
    ((rootElt 0 1 a * rootElt 0 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
      ![w 0 + a * w 1 + b * w 2, w 1, w 2] := by
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, rootElt_mulVec_add_single (by decide),
    rootElt_mulVec_add_single (by decide)]
  ext i
  simp only [Pi.add_apply, Pi.single_apply]
  fin_cases i
  · simp
    ring
  · simp
  · simp

theorem map_mulVecLin_mul_SL3 (S : Submodule F (Fin 3 → F)) (g g' : SL3 F) :
    S.map ((g * g' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin =
      (S.map ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin).map
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
  rw [coe_mul_SL3, Matrix.mulVecLin_mul, Submodule.map_comp]

theorem eq_of_map_span_e₁_eq {a b a' b' : F}
    (h : (F ∙ (![0, 1, 0] : Fin 3 → F)).map
        ((rootElt 0 1 a * rootElt 2 1 b : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin =
      (F ∙ (![0, 1, 0] : Fin 3 → F)).map
        ((rootElt 0 1 a' * rootElt 2 1 b' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin) :
    a = a' ∧ b = b' := by
  rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton,
    Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, rootElt_mul_mulVec_e₁,
    rootElt_mul_mulVec_e₁] at h
  have hmem : (![a, 1, b] : Fin 3 → F) ∈ F ∙ (![a', 1, b'] : Fin 3 → F) := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 : c = 1 := by simpa using congrFun hc 1
  have h0 : c * a' = a := by simpa using congrFun hc 0
  have h2 : c * b' = b := by simpa using congrFun hc 2
  rw [h1, one_mul] at h0 h2
  exact ⟨h0.symm, h2.symm⟩

theorem eq_of_map_coordZero_eq {a b a' b' : F}
    (h : (coordZero 0 : Submodule F (Fin 3 → F)).map
        ((rootElt 0 1 a * rootElt 0 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin =
      (coordZero 0 : Submodule F (Fin 3 → F)).map
        ((rootElt 0 1 a' * rootElt 0 2 b' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin) :
    a = a' ∧ b = b' := by
  have key : ∀ w : Fin 3 → F, w 0 = 0 → ∃ w' : Fin 3 → F, w' 0 = 0 ∧
      (![w' 0 + a' * w' 1 + b' * w' 2, w' 1, w' 2] : Fin 3 → F) =
        ![w 0 + a * w 1 + b * w 2, w 1, w 2] := by
    intro w hw
    have hmem : ((rootElt 0 1 a * rootElt 0 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈
        (coordZero 0 : Submodule F (Fin 3 → F)).map
          ((rootElt 0 1 a' * rootElt 0 2 b' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
      rw [← h]
      exact Submodule.mem_map_of_mem (show w ∈ (coordZero 0 : Submodule F (Fin 3 → F)) from hw)
    obtain ⟨w', hw', he⟩ := Submodule.mem_map.mp hmem
    refine ⟨w', hw', ?_⟩
    rw [Matrix.mulVecLin_apply, rootElt01_mul_rootElt02_mulVec,
      rootElt01_mul_rootElt02_mulVec] at he
    exact he
  obtain ⟨w₁, hw₁, h1⟩ := key ![0, 1, 0] (by simp)
  obtain ⟨w₂, hw₂, h2⟩ := key ![0, 0, 1] (by simp)
  have e11 : w₁ 1 = 1 := by simpa using congrFun h1 1
  have e12 : w₁ 2 = 0 := by simpa using congrFun h1 2
  have e10 : w₁ 0 + a' * w₁ 1 + b' * w₁ 2 = a := by simpa using congrFun h1 0
  have e21 : w₂ 1 = 0 := by simpa using congrFun h2 1
  have e22 : w₂ 2 = 1 := by simpa using congrFun h2 2
  have e20 : w₂ 0 + a' * w₂ 1 + b' * w₂ 2 = b := by simpa using congrFun h2 0
  rw [hw₁, e11, e12] at e10
  rw [hw₂, e21, e22] at e20
  constructor
  · simpa using e10.symm
  · simpa using e20.symm

end Lin

section Orbit

variable {F : Type} [Field F] [Fintype F] {𝔾 : Type*} [Group 𝔾]

theorem exists_regular_labels {K X : Subgroup 𝔾} (ρ : ↥K →* SL3 F)
    (hρ : Function.Surjective ρ)
    (hX : ∀ c : F, ∃ x : ↥K, (x : 𝔾) ∈ X ∧ ρ x = rootElt 0 1 c)
    (κ : Subgroup 𝔾 → Submodule F (Fin 3 → F))
    (hκ : ∀ (k : ↥K) (s : Subgroup 𝔾), κ (s.map (MulAut.conj (k : 𝔾)).toMonoidHom) =
      (κ s).map ((ρ k : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin)
    {s₁ : Subgroup 𝔾} (hs₁ : Module.finrank F (κ s₁) = 1 ∨ Module.finrank F (κ s₁) = 2) :
    ∃ 𝒪 : Finset (Subgroup 𝔾), Fintype.card F * (Fintype.card F - 1) ≤ 𝒪.card ∧
      (∀ s ∈ 𝒪, ∃ k : ↥K, s = s₁.map (MulAut.conj (k : 𝔾)).toMonoidHom) ∧
      ∀ s ∈ 𝒪, ∃ x ∈ X, s.map (MulAut.conj x).toMonoidHom ∉ 𝒪 := by
  classical
  obtain ⟨y₁, S₀, Y, hy₁, hfree⟩ : ∃ (y₁ : SL3 F) (S₀ : Submodule F (Fin 3 → F))
      (Y : F → SL3 F),
      (κ s₁).map ((y₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin = S₀ ∧
      ∀ a b a' b' : F,
        S₀.map ((rootElt 0 1 a * Y b : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin =
          S₀.map ((rootElt 0 1 a' * Y b' : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin →
        a = a' ∧ b = b' := by
    rcases hs₁ with h1 | h2
    · have hne : κ s₁ ≠ ⊥ := by
        intro hb
        rw [hb, finrank_bot] at h1
        omega
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hκv : κ s₁ = F ∙ v := (Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
        (by rw [finrank_span_singleton hv0, h1])).symm
      obtain ⟨y₁, hy₁⟩ := exists_mulVec_eq_e₁ hv0
      refine ⟨y₁, F ∙ ![0, 1, 0], rootElt 2 1, ?_, fun a b a' b' he => eq_of_map_span_e₁_eq he⟩
      rw [hκv, Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply, hy₁]
    · obtain ⟨y₁, hy₁⟩ := exists_map_eq_coordZero h2
      exact ⟨y₁, coordZero 0, rootElt 0 2, hy₁, fun a b a' b' he => eq_of_map_coordZero_eq he⟩
  choose k hk using fun p : F × F => hρ (rootElt 0 1 p.1 * Y p.2 * y₁)
  obtain ⟨lab, hlab⟩ : ∃ lab : F × F → Subgroup 𝔾,
      ∀ p, lab p = s₁.map (MulAut.conj (k p : 𝔾)).toMonoidHom := ⟨_, fun _ => rfl⟩
  have hκlab : ∀ p : F × F, κ (lab p) =
      S₀.map ((rootElt 0 1 p.1 * Y p.2 : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
    intro p
    rw [hlab p, hκ (k p) s₁, hk p, map_mulVecLin_mul_SL3, hy₁]
  have hinj : Function.Injective lab := by
    intro p p' he
    have := hfree p.1 p.2 p'.1 p'.2 (by rw [← hκlab p, ← hκlab p', he])
    exact Prod.ext this.1 this.2
  refine ⟨((Finset.univ.erase (0 : F)) ×ˢ (Finset.univ : Finset F)).image lab, ?_, ?_, ?_⟩
  · apply le_of_eq
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, mul_comm]
  · intro s hs
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨k p, hlab p⟩
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨x, hxX, hx⟩ := hX (-p.1)
    refine ⟨x, hxX, fun hmem => ?_⟩
    obtain ⟨p', hp', he⟩ := Finset.mem_image.mp hmem
    have hp'1 : p'.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp').1).1
    have hκe := congrArg κ he
    rw [hκ x (lab p), hκlab p', hκlab p, hx, ← map_mulVecLin_mul_SL3, ← mul_assoc,
      ← rootElt_add, neg_add_cancel] at hκe
    exact hp'1 (hfree _ _ _ _ hκe).1

end Orbit

section Span

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

@[expose] noncomputable def natSpan (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (y : SL3 F)
    (s : Subgroup G) : Submodule F (Fin 3 → F) :=
  Submodule.span F ((fun u : ↥V => ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hφ u) ''
    {u | (u : G) ∈ s})

theorem conj_mulVec_mulVec (y g : SL3 F) (w : Fin 3 → F) :
    ((y * g * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← coe_mul_SL3, ← coe_mul_SL3,
    show y * g * y⁻¹ * y = y * g by group]

theorem natSpan_map_conj (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (y : SL3 F) (k : ↥K)
    (s : Subgroup G) :
    natSpan hφ y (s.map (MulAut.conj (k : G)).toMonoidHom) =
      (natSpan hφ y s).map
        ((y * toSL3 φ k * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
  rw [natSpan, natSpan, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨t, ht, htu⟩ := Subgroup.mem_map.mp hu
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at htu
    have htV : t ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hφ.1 (K.inv_mem k.2)) u).mp u.2
      rw [← htu, inv_inv] at this
      simpa [mul_assoc] using this
    refine ⟨((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hφ ⟨t, htV⟩,
      ⟨⟨t, htV⟩, ht, rfl⟩, ?_⟩
    dsimp only
    rw [Matrix.mulVecLin_apply, conj_mulVec_mulVec,
      natVec_conj hφ k ⟨t, htV⟩ u htu.symm]
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have huV : (k : G) * t * (k : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hφ.1 k.2) t).mp t.2
    refine ⟨⟨_, huV⟩, Subgroup.mem_map.mpr ⟨t, ht, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩, ?_⟩
    dsimp only
    rw [Matrix.mulVecLin_apply, conj_mulVec_mulVec, natVec_conj hφ k t ⟨_, huV⟩ rfl]

theorem natSpan_ne_bot (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (y : SL3 F)
    {s : Subgroup G} {u : ↥V} (hu : (u : G) ∈ s) (hu1 : u ≠ 1) : natSpan hφ y s ≠ ⊥ := by
  intro hb
  have hmem : ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hφ u ∈ natSpan hφ y s :=
    Submodule.subset_span ⟨u, hu, rfl⟩
  rw [hb, Submodule.mem_bot] at hmem
  have h0 : natVec hφ u = 0 := by
    rw [← inv_mulVec_mulVec_SL3 y (natVec hφ u), hmem, Matrix.mulVec_zero]
  exact hu1 (natVec_injective hφ (h0.trans (natVec_one hφ).symm))

theorem natSpan_le_map (hφ : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (y : SL3 F)
    {s : Subgroup G} {W : Submodule F (Fin 3 → F)} (hW : ∀ u : ↥V, (u : G) ∈ s → natVec hφ u ∈ W) :
    natSpan hφ y s ≤ W.map ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, hu, rfl⟩
  exact Submodule.mem_map_of_mem (hW u hu)

end Span

end CFSG.Quasithin.MS93.S46
