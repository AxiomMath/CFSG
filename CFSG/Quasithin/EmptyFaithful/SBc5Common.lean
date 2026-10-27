module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.EmptyFaithful.S153D0J

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc5

section Generic

variable {G : Type} [Group G]

theorem oPrimeResidualOf_le (p : ℕ) (X : Subgroup G) : oPrimeResidualOf p X ≤ X := by
  unfold oPrimeResidualOf
  exact (Subgroup.closure_le _).2 fun x hx => hx.1

theorem commutator_eq_top_of_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (h : commutator G₁ = ⊤) : commutator G₂ = ⊤ := by
  have hs : (⊤ : Subgroup G₁).map e.toMonoidHom = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
  have h1 : (commutator G₁).map e.toMonoidHom = commutator G₂ := by
    show (⁅(⊤ : Subgroup G₁), (⊤ : Subgroup G₁)⁆ : Subgroup G₁).map e.toMonoidHom =
      ⁅(⊤ : Subgroup G₂), (⊤ : Subgroup G₂)⁆
    rw [Subgroup.map_commutator, hs]
  rw [← h1, h, hs]

theorem commutator_subgroup_eq_map {H : Subgroup G} :
    ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
  have h1 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show ⁅H, H⁆ = (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H).map H.subtype
  rw [Subgroup.map_commutator, h1]

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem omegaOneCenter_le_Sgp (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

end Context

end SBc5

end CFSG.Quasithin
