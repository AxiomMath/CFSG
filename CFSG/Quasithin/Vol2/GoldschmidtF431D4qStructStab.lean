module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.Sec53F.Yam

set_option linter.unusedSectionVars false


section Ust

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem fieldActor_map_Ust (δ : K ≃+* K) :
    (Ust σ).map (fieldActor σ δ).toMonoidHom = Ust σ := by
  have h := CFSG.Quasithin.H13.Sec53F.TriD4.d4_F_U σ (fieldActor σ δ) ⟨δ, rfl⟩
  ext x
  rw [Subgroup.mem_map_equiv]
  have := h ((fieldActor σ δ).symm x)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem fieldActor_map_normalizer (δ : K ≃+* K) :
    (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).map
      (fieldActor σ δ).toMonoidHom = Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) :=
  by
  rw [Subgroup.map_equiv_normalizer_eq, fieldActor_map_Ust]

end Ust

theorem mem_autStab_iff_map {D : Type} [Group D] (P : Subgroup D) (φ : MulAut D) :
    φ ∈ autStab P ↔ P.map φ.toMonoidHom = P := by
  constructor
  · intro h
    ext x
    rw [Subgroup.mem_map_equiv]
    have := h (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  · intro h y
    have h1 : φ y ∈ P.map φ.toMonoidHom ↔ φ y ∈ P := by rw [h]
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    exact h1

section Pst

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσ

theorem relIndex_Pst_ne :
    (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).relIndex (Pst0 σ) ≠
      (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).relIndex (Pst1 σ) := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσ
  obtain ⟨U₀, hU₀, hc₀⟩ := triality_hasUnequalCovers hf hK σ (fun c => hσ c)
  have hc := HasUnequalCovers.of_isSylow (MulEquiv.refl (Cm σ)) hc₀ hU₀ hS.sylow
  obtain ⟨Q₁, Q₂, hcov, -, -, -, i₁, i₂⟩ := hc
  have hn01 : ¬ Pst0 σ ≤ Pst1 σ := fun h => by
    rcases hS.coatom₀.le_iff.1 h with h' | h'
    · exact hS.coatom₁.1 h'
    · exact hS.ne h'.symm
  have hn10 : ¬ Pst1 σ ≤ Pst0 σ := fun h => by
    rcases hS.coatom₁.le_iff.1 h with h' | h'
    · exact hS.coatom₀.1 h'
    · exact hS.ne h'
  have hlat := CFSG.Quasithin.H13.F431.D4q.Hex.d4_overgroups_normalizer σ
  have hcov0 : Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ⋖ Pst0 σ := by
    refine ⟨lt_of_le_of_ne hS.le₀ fun h => hn01 (h ▸ hS.le₁), fun A hNA hAP => ?_⟩
    rcases hlat A hNA.le with h | h | h | h
    · exact hNA.ne h.symm
    · exact hAP.ne h
    · exact hn10 (le_of_eq_of_le h.symm hAP.le)
    · exact hS.coatom₀.1 (top_le_iff.1 (le_of_eq_of_le h.symm hAP.le))
  have hcov1 : Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ⋖ Pst1 σ := by
    refine ⟨lt_of_le_of_ne hS.le₁ fun h => hn10 (h ▸ hS.le₀), fun A hNA hAP => ?_⟩
    rcases hlat A hNA.le with h | h | h | h
    · exact hNA.ne h.symm
    · exact hn01 (le_of_eq_of_le h.symm hAP.le)
    · exact hAP.ne h
    · exact hS.coatom₁.1 (top_le_iff.1 (le_of_eq_of_le h.symm hAP.le))
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hlt : 2 ^ f < (2 ^ f) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases (hcov _).1 hcov0 with h0 | h0 <;> rcases (hcov _).1 hcov1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hS.ne
  · rw [h0, h1, i₁, i₂]
    omega
  · rw [h0, h1, i₁, i₂]
    omega
  · exact absurd (h0.trans h1.symm) hS.ne

theorem fieldActor_map_Pst (δ : K ≃+* K) :
    (Pst0 σ).map (fieldActor σ δ).toMonoidHom = Pst0 σ ∧
      (Pst1 σ).map (fieldActor σ δ).toMonoidHom = Pst1 σ := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσ
  have hlat := CFSG.Quasithin.H13.F431.D4q.Hex.d4_overgroups_normalizer σ
  have hne := relIndex_Pst_ne σ hf hK hσ
  have hN := fieldActor_map_normalizer σ δ
  have hN' : (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).map
      (fieldActor σ δ).symm.toMonoidHom =
      Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) :=
    (Subgroup.map_symm_eq_iff_map_eq _ (e := fieldActor σ δ)).2 hN
  have hcases : ∀ P : Subgroup (Cm σ),
      Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ≤ P → P ≠ ⊤ →
      Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ≠ P →
      (P.map (fieldActor σ δ).toMonoidHom = Pst0 σ ∨
        P.map (fieldActor σ δ).toMonoidHom = Pst1 σ) := by
    intro P hNP hP1 hP2
    have h1 : Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ≤
        P.map (fieldActor σ δ).toMonoidHom := by
      rw [← hN]
      exact Subgroup.map_mono hNP
    rcases hlat _ h1 with h | h | h | h
    · exfalso
      apply hP2
      have := (Subgroup.map_symm_eq_iff_map_eq P (e := fieldActor σ δ)).2 h
      exact hN'.symm.trans this
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hP1
      have := congrArg (Subgroup.map (fieldActor σ δ).symm.toMonoidHom) h
      rwa [map_symm_map, Subgroup.map_top_of_surjective _ (fieldActor σ δ).symm.surjective]
        at this
  have hn01 : ¬ Pst0 σ ≤ Pst1 σ := fun h => by
    rcases hS.coatom₀.le_iff.1 h with h' | h'
    · exact hS.coatom₁.1 h'
    · exact hS.ne h'.symm
  have hn10 : ¬ Pst1 σ ≤ Pst0 σ := fun h => by
    rcases hS.coatom₁.le_iff.1 h with h' | h'
    · exact hS.coatom₀.1 h'
    · exact hS.ne h'
  have h0 := hcases (Pst0 σ) hS.le₀ hS.coatom₀.1 fun h => hn01 (h ▸ hS.le₁)
  have h1 := hcases (Pst1 σ) hS.le₁ hS.coatom₁.1 fun h => hn10 (h ▸ hS.le₀)
  have hidx : ∀ P : Subgroup (Cm σ),
      (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).relIndex
        (P.map (fieldActor σ δ).toMonoidHom) =
      (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))).relIndex P := fun P => by
    have := Subgroup.relIndex_map_map_of_injective
      (Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ))) P
      (f := (fieldActor σ δ).toMonoidHom) (fieldActor σ δ).injective
    rwa [hN] at this
  refine ⟨?_, ?_⟩
  · rcases h0 with h | h
    · exact h
    · exact absurd (by rw [← hidx (Pst0 σ), h]) hne
  · rcases h1 with h | h
    · exact absurd (by rw [← hidx (Pst1 σ), h]) hne
    · exact h

theorem fieldActor_mem_autStab_Pst0 (δ : K ≃+* K) : fieldActor σ δ ∈ autStab (Pst0 σ) :=
  (mem_autStab_iff_map _ _).2 (fieldActor_map_Pst σ hf hK hσ δ).1

theorem fieldActor_mem_autStab_Pst1 (δ : K ≃+* K) : fieldActor σ δ ∈ autStab (Pst1 σ) :=
  (mem_autStab_iff_map _ _).2 (fieldActor_map_Pst σ hf hK hσ δ).2

end Pst

end CFSG.Quasithin.H13.F431.D4q.Struct
