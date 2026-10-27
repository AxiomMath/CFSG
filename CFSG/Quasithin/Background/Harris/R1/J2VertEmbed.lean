module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17AutData

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification.J2Cover CFSG.Quasithin.S1421QA17

theorem exists_autJ2_embedding
    {X : Type} [Group X] [Finite X] (hX : Nat.card X = 3840) (φ : X →* Equiv.Perm (Fin 315))
    (hφ : Function.Injective φ) (hR : φ.range ≤ R) :
    ∃ (Y : Type) (_ : Group Y), Nonempty (Y ≃* MulAut quasithinJ2) ∧
      ∃ (TY M₁ : Subgroup Y) (_ : X ≃* ↥M₁), IsSylowTwoOf TY ⊤ ∧ TY ≤ M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₁ : Subgroup ↥R := φ.range.subgroupOf R with hM₁
  let e : X ≃* ↥M₁ := (MonoidHom.ofInjective hφ).trans (Subgroup.subgroupOfEquivOfLe hR).symm
  have hM : Nat.card M₁ = 3840 := by rw [← Nat.card_congr e.toEquiv, hX]
  have hidxM : M₁.index = 315 := by
    have h1 := Subgroup.index_mul_card M₁
    rw [hM, card_R] at h1
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥M₁) := inferInstance
  set TY : Subgroup ↥R := (P : Subgroup ↥M₁).map M₁.subtype with hTY
  have hTYM : TY ≤ M₁ := by
    rw [hTY]
    exact Subgroup.map_subtype_le _
  have hrel : TY.relIndex M₁ = (P : Subgroup ↥M₁).index := by
    rw [Subgroup.relIndex, hTY, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M₁.subtype_injective]
  have hPodd : ¬ 2 ∣ (P : Subgroup ↥M₁).index := P.not_dvd_index
  have hTYodd : ¬ 2 ∣ TY.index := by
    rw [← Subgroup.relIndex_mul_index hTYM, hrel, hidxM]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact hPodd h
    · exact absurd h (by norm_num)
  refine ⟨↥R, inferInstance, ⟨mulAutQuasithinJ2EquivR.symm⟩, TY, M₁, e, ⟨le_top, ?_, ?_⟩, hTYM⟩
  · exact P.isPGroup'.map M₁.subtype
  · rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact hTYodd

end CFSG.Quasithin.Background.Harris.R1.J2Vert
