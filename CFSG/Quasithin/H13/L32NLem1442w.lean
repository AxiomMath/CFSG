module

public import CFSG.Quasithin.H13.L32NLem1442v
public import CFSG.Quasithin.H13.L32NLem1442s
public import CFSG.Quasithin.H13.L32NLem1442p
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.SzG11B49Main

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem irr (hd : Module.finrank (ZMod 2) D.V ≠ 4) :
    ∀ J : Submodule (ZMod 2) D.V, (∀ γ ∈ D.img (l32nH T V), ∀ v ∈ J, γ v ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
  have h5 : G11.G1005Stmt := g10_5 G11.g10_3 (g10_4 G11.g10_3 G11.SzG11S.b49)
  rcases h5 D.V D.B _ _ _ _ _ C.g111.toG101Hyp with h | ⟨h4, -⟩
  · intro J hJ
    exact h.2.2 J hJ bot_le le_top
  · exact absurd h4 hd

theorem exists_model9 (h9 : G112Concl9 (D.img (l32nH T V))) :
    ∃ (b₁ b₂ : Bool) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)), ∀ φ : D.V ≃ₗ[ZMod 2] D.V,
      φ ∈ D.img (l32nH T V) ↔ ∃ γ ∈ L1442M.g5 b₁ b₂,
        ∀ v, e (φ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) :=
  L1442V.exists_model_of h9.1 (C.irr (by rw [h9.1]; norm_num)) h9.2

end Ctx

end L1442

theorem case1442FromConcl9_of (h12213 : Stmt12_2_13) :
    Case1442FromConcl9 := by
  intro G _ _ T L V V₂ g a D C c9
  obtain ⟨b₁, b₂, e, he⟩ := C.exists_model9 c9
  exact C.case5_of_model h12213 c9 he

end CFSG.Quasithin.H13
