module

public import CFSG.Quasithin.H13.KGFact68LieRed

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Transport

variable {X S : Type} [Group X] [Group S] (e : X ≃* S)

theorem congr_apply_apply (ρ : MulAut X) (s : S) : MulAut.congr e ρ s = e (ρ (e.symm s)) :=
  rfl

theorem congr_conj (p : X) : MulAut.congr e (MulAut.conj p) = MulAut.conj (e p) := by
  ext s
  rw [congr_apply_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mem_map_equiv_iff {H : Subgroup X} {s : S} : s ∈ H.map e.toMonoidHom ↔ e.symm s ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hs
    exact ⟨e.symm s, hs, by simp⟩

theorem card_map_equiv (H : Subgroup X) : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective e.injective

variable {e}

theorem CartanSingerHyp.map {P : Subgroup X} {𝓡 : Subgroup (MulAut X)} {G : Subgroup X}
    (h : CartanSingerHyp P 𝓡 G) :
    CartanSingerHyp (P.map e.toMonoidHom) (𝓡.map (MulAut.congr e).toMonoidHom)
      (G.map e.toMonoidHom) := by
  refine ⟨h.isPGroup.map _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨p, hp, rfl⟩
    refine ⟨ρ p, h.normalizes ρ hρ p hp, ?_⟩
    simp
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨MulAut.conj p, h.inner p hp, ?_⟩
    exact congr_conj e p
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, (h.le g hg).1, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, (h.le g hg).2 t ht]
  · rintro _ ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, h.sq g hg, map_one]
  · rw [card_map_equiv]
    exact h.four_le
  · rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨g, hg, rfl⟩
    simp [h.fixed ρ hρ g hg]

theorem CentralizerCond.map {G : Subgroup X} (h : CentralizerCond G) :
    CentralizerCond (G.map e.toMonoidHom) := by
  rintro _ ⟨g, hg, rfl⟩ hg1 y hyg ⟨k, hk⟩ _ ⟨g', hg', rfl⟩
  simp only [MulEquiv.coe_toMonoidHom] at hg1 hyg ⊢
  have hg1' : g ≠ 1 := fun h1 => hg1 (by rw [h1, map_one])
  have hyg' : e.symm y * g = g * e.symm y := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hyg]
  have hk' : e.symm y ^ 2 ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have h1 := h g hg hg1' (e.symm y) hyg' ⟨k, hk'⟩ g' hg'
  have h2 := congrArg e h1
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2

theorem CartanSingerConcl.of_map {P : Subgroup X} {𝓡 : Subgroup (MulAut X)} {G : Subgroup X}
    (h : CartanSingerConcl (P.map e.toMonoidHom) (𝓡.map (MulAut.congr e).toMonoidHom)
      (G.map e.toMonoidHom)) : CartanSingerConcl P 𝓡 G := by
  obtain ⟨x, hxN, hxodd, hxR, hxS⟩ := h
  refine ⟨e.symm x, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro p
    have h1 := hxN (e p)
    rw [mem_map_equiv_iff, mem_map_equiv_iff, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    simp
  · rwa [MulEquiv.orderOf_eq]
  · intro ρ hρ
    have h1 := hxR (MulAut.congr e ρ) ⟨ρ, hρ, rfl⟩
    rw [mem_map_equiv_iff] at h1
    simpa [congr_apply_apply] using h1
  · intro hxG j
    have hxG' : ∀ g ∈ G.map e.toMonoidHom, x * g * x⁻¹ ∈ G.map e.toMonoidHom := by
      intro g hg
      rw [mem_map_equiv_iff] at hg ⊢
      have := hxG _ hg
      simpa using this
    rw [← card_map_equiv e G, ← hxS hxG' j]
    constructor
    · intro hj g hg
      rw [mem_map_equiv_iff] at hg
      have h1 := hj _ hg
      have h2 := congrArg e h1
      simpa using h2
    · intro hj g hg
      have h1 := hj (e g) ⟨g, hg, rfl⟩
      apply e.injective
      simpa using h1

end Transport

section Instances

variable {X S : Type} [Group X] [Group S] [Finite X] [Finite S]

omit [Finite S] in
theorem CartanSinger.of_mulEquiv (e : X ≃* S) (h : CartanSinger S) : CartanSinger X := by
  intro P 𝓡 G hG hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := h (P.mapSurjective (f := e.toMonoidHom) e.surjective) _ _ hG.map hC.map
  exact CartanSingerConcl.of_map h1

omit [Finite S] in
theorem CartanSingerCover.of_mulEquiv (e : X ≃* S) (h : CartanSingerCover S) :
    CartanSingerCover X := by
  intro P 𝓡 G hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CartanSingerConcl.of_map (h (P.mapSurjective (f := e.toMonoidHom) e.surjective) _ _ hG.map)

omit [Finite S] in
theorem map_conj_sylow (P : Sylow 2 S) (g : S) :
    (P : Subgroup S).map (MulAut.conj g).toMonoidHom = ((g • P : Sylow 2 S) : Subgroup S) := by
  ext s
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem cartanSinger_of_sylow (P₀ : Sylow 2 S)
    (h : ∀ (𝓡 : Subgroup (MulAut S)) (G : Subgroup S), CartanSingerHyp (P₀ : Subgroup S) 𝓡 G →
      CentralizerCond G → CartanSingerConcl (P₀ : Subgroup S) 𝓡 G) : CartanSinger S := by
  intro P 𝓡 G hG hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P P₀
  have hP : (P : Subgroup S).map (MulAut.conj g).toMonoidHom = (P₀ : Subgroup S) := by
    rw [map_conj_sylow, hg]
  have h1 := h _ _ ((hP ▸ hG.map (e := MulAut.conj g))) hC.map
  exact CartanSingerConcl.of_map (hP ▸ h1)

theorem cartanSingerCover_of_sylow (P₀ : Sylow 2 S)
    (h : ∀ (𝓡 : Subgroup (MulAut S)) (G : Subgroup S), CartanSingerHyp (P₀ : Subgroup S) 𝓡 G →
      CartanSingerConcl (P₀ : Subgroup S) 𝓡 G) : CartanSingerCover S := by
  intro P 𝓡 G hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P P₀
  have hP : (P : Subgroup S).map (MulAut.conj g).toMonoidHom = (P₀ : Subgroup S) := by
    rw [map_conj_sylow, hg]
  have h1 := h _ _ ((hP ▸ hG.map (e := MulAut.conj g)))
  exact CartanSingerConcl.of_map (hP ▸ h1)

end Instances

end CFSG.Quasithin.H13.KG68
