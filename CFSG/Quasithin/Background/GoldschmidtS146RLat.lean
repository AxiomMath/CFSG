module

public import CFSG.Quasithin.Background.GoldschmidtS146RBend1

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def ordL2 (m : ℕ) : ℕ := 2 ^ m * ((2 ^ m) ^ 2 - 1)

@[expose] def LatShape (X : Type) [Group X] (U : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, U ≤ Y → Y ≠ ⊤ →
    Y ≤ Subgroup.normalizer (U : Set X) ∨ Nat.card ↥Y = 3 * Nat.card ↥U ∨
      ∃ m : ℕ, 2 ≤ m ∧ ¬ Group.IsSolvable ↥Y ∧
        ∃ (Q : Type) (_ : Group Q) (π : ↥(perfectCore Y) →* Q),
          Function.Surjective π ∧ IsPGroup 2 π.ker ∧ IsSimpleGroup Q ∧ Nat.card Q = ordL2 m

theorem LatShape.of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  intro Y hUY hY
  left
  have hB' : fusionIsBenderGroup ↥(⊤ : Subgroup X) :=
    fusionIsBenderGroup_congr Subgroup.topEquiv.symm hB
  rcases bender_overgroup (A := ⊤) hB' hU hUY le_top with h | h
  · exact h
  · exact absurd (top_le_iff.mp h) hY

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem map_map_symm' (e : X ≃* X') (Y : Subgroup X') :
    (Y.map e.symm.toMonoidHom).map e.toMonoidHom = Y := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X' := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem normalizer_map_equiv (e : X ≃* X') (S : Subgroup X) :
    Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
  apply le_antisymm
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    change e.symm y ∈ Subgroup.normalizer (S : Set X)
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    have h1 := hy (e h)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
    simpa only [MulEquiv.symm_apply_apply, map_mul, map_inv] using h1
  · exact Subgroup.le_normalizer_map e.toMonoidHom

theorem LatShape.map [Finite X] [Finite X'] (e : X ≃* X') {U : Subgroup X} (h : LatShape X U) :
    LatShape X' (U.map e.toMonoidHom) := by
  intro Y' hUY' hY'
  set Y : Subgroup X := Y'.map e.symm.toMonoidHom with hYdef
  have hYe : Y.map e.toMonoidHom = Y' := map_map_symm' e Y'
  have hUY : U ≤ Y := by
    intro u hu
    refine ⟨e u, hUY' ⟨u, hu, rfl⟩, by simp⟩
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply hY'
    rw [← hYe, htop, Subgroup.map_top_of_surjective _ e.surjective]
  have hcardY : Nat.card ↥Y' = Nat.card ↥Y := by
    rw [← hYe]
    exact Subgroup.card_map_of_injective e.injective
  rcases h Y hUY hYtop with h1 | h2 | ⟨m, hm, hns, Q, _, π, hπ, hker, hQ, hcard⟩
  · left
    rw [← hYe, normalizer_map_equiv]
    exact Subgroup.map_mono h1
  · right; left
    have hU : Nat.card ↥(U.map e.toMonoidHom) = Nat.card ↥U :=
      Subgroup.card_map_of_injective e.injective
    rw [hU, hcardY]
    exact h2
  · right; right
    have hperf : (perfectCore Y).map e.toMonoidHom = perfectCore Y' := by
      rw [map_perfectCore, hYe]
    let ψ : ↥(perfectCore Y') ≃* ↥(perfectCore Y) :=
      (MulEquiv.subgroupCongr hperf.symm).trans
        ((perfectCore Y).equivMapOfInjective e.toMonoidHom e.injective).symm
    refine ⟨m, hm, ?_, Q, inferInstance, π.comp ψ.toMonoidHom, hπ.comp ψ.surjective, ?_, hQ,
      hcard⟩
    · intro hs
      apply hns
      rw [← hYe] at hs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Y.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (Y.equivMapOfInjective e.toMonoidHom e.injective).injective
    · rw [← MonoidHom.comap_ker]
      exact hker.comap_of_injective _ ψ.injective

end Transport

section Sylow

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def sylowOfTop {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : Sylow 2 X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hU.2.1.toSylow (by
    have h := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h)

omit [Finite X] in
theorem coe_sylowOfTop {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ((sylowOfTop hU : Sylow 2 X) : Subgroup X) = U := rfl

theorem exists_conj_of_isSylowTwoOf_top {U₁ U₂ : Subgroup X} (h₁ : IsSylowTwoOf U₁ ⊤)
    (h₂ : IsSylowTwoOf U₂ ⊤) : ∃ g : X, U₂ = U₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (sylowOfTop h₁) (sylowOfTop h₂)
  refine ⟨g, ?_⟩
  rw [← coe_sylowOfTop h₂, ← hg, Sylow.coe_subgroup_smul, coe_sylowOfTop h₁]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact ⟨y, hy, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, hy, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]

theorem LatShape.of_sylow {U₀ U : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤)
    (h : LatShape X U₀) : LatShape X U := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hU₀ hU
  rw [hg]
  exact h.map (MulAut.conj g)

end Sylow

end CFSG.Quasithin.GoldS146R
