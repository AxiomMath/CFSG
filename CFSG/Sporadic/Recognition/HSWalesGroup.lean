module

public import CFSG.Sporadic.Recognition.HSWalesIso
public import CFSG.Sporadic.Recognition.HSGraph

public section

namespace CFSG.Sporadic.Recognition.HSWales

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Recognition.HSGraph

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω}
  {φ : stabilizer G a ≃* M22}

theorem natCard_eq [IsPretransitive G Ω] (hΩ : Nat.card Ω = 100)
    (φ : stabilizer G a ≃* M22) :
    Nat.card G = 44352000 := by
  have h := Subgroup.card_mul_index (stabilizer G a)
  rw [index_stabilizer_of_transitive G a, hΩ, Nat.card_congr φ.toEquiv, card_M22'] at h
  omega

namespace Model

variable (𝓜 : Model G a b c φ) [Finite Ω] [IsPretransitive G Ω]
  (D : Rank3 G a b c)

include 𝓜 D

theorem permCongr_toPerm_mem
    (g : G) :
    (𝓜.toVertEquiv D).permCongr (toPerm g) ∈ autGroup hexads := by
  intro u v
  obtain ⟨x, rfl⟩ := (𝓜.toVertEquiv D).surjective u
  obtain ⟨y, rfl⟩ := (𝓜.toVertEquiv D).surjective v
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  change (hsGraph hexads).Adj (𝓜.toVert (g • x)) (𝓜.toVert (g • y)) ↔
    (hsGraph hexads).Adj (𝓜.toVert x) (𝓜.toVert y)
  rw [𝓜.adj_toVert D, 𝓜.adj_toVert D, D.adj_smul]

@[expose] noncomputable def autHom :
    G →* autGroup hexads :=
  (((𝓜.toVertEquiv D).permCongrHom.toMonoidHom).comp (toPermHom G Ω)).codRestrict
    (autGroup hexads) (𝓜.permCongr_toPerm_mem D)

theorem autHom_injective
    [FaithfulSMul G Ω] : Function.Injective (𝓜.autHom D) := by
  intro g h hgh
  have h1 := congrArg Subtype.val hgh
  exact toPerm_injective ((𝓜.toVertEquiv D).permCongrHom.injective h1)

theorem index_autHom_range
    [FaithfulSMul G Ω] : (𝓜.autHom D).range.index = 2 := by
  have hcard : Nat.card (𝓜.autHom D).range = 44352000 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (𝓜.autHom_injective D)).toEquiv,
      natCard_eq D.card_Ω φ]
  obtain ⟨-, -, ⟨-, hA, -⟩, -⟩ :=
    higman_sims_1968_graph_automorphism_group hexads isSteinerTriple_hexads
  have h2 := Subgroup.card_mul_index (𝓜.autHom D).range
  rw [hcard, hA] at h2
  omega

theorem nonempty_mulEquiv_range
    [FaithfulSMul G Ω] : Nonempty (G ≃* (𝓜.autHom D).range) :=
  ⟨MonoidHom.ofInjective (𝓜.autHom_injective D)⟩

end Model

end CFSG.Sporadic.Recognition.HSWales
