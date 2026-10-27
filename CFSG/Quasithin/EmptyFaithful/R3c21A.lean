module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace R3c21

open E2

variable {G : Type} [Group G] [Finite G]

namespace S0

theorem isSolvable_biSup {Γ : Type*} [Group Γ] (I : Finset (Subgroup Γ))
    (hs : ∀ A ∈ I, Group.IsSolvable ↥A)
    (hn : ∀ A ∈ I, ∀ B ∈ I, A ≤ Subgroup.normalizer (B : Set Γ)) :
    Group.IsSolvable ↥(⨆ A ∈ I, A) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have h0 : (⨆ A ∈ (∅ : Finset (Subgroup Γ)), A) = ⊥ :=
      le_antisymm (iSup₂_le fun A hA => absurd hA (Finset.notMem_empty A)) bot_le
    rw [h0]
    infer_instance
  | insert a s ha ih =>
    rw [Finset.iSup_insert]
    have h1 := ih (fun A hA => hs A (Finset.mem_insert_of_mem hA))
      (fun A hA B hB => hn A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB))
    have h2 := hs a (Finset.mem_insert_self a s)
    have hle : (⨆ A ∈ s, A) ≤ Subgroup.normalizer (a : Set Γ) :=
      iSup₂_le fun A hA => hn A (Finset.mem_insert_of_mem hA) a (Finset.mem_insert_self a s)
    exact A3.isSolvable_sup_of_le_normalizer hle

theorem isSolvable_sl2_of_card_two {F : Type} [Field F] [Fintype F]
    (h : Fintype.card F = 2) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let f : Matrix.SpecialLinearGroup (Fin 2) F →* Equiv.Perm (Fin 2 → F) :=
    (MulAction.toPermHom ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (Fin 2 → F)).comp
      Matrix.SpecialLinearGroup.toLin'
  have hf : Function.Injective f := by
    intro A B hAB
    apply Matrix.SpecialLinearGroup.toLin'_injective
    ext v : 1
    have := congrArg (fun σ : Equiv.Perm (Fin 2 → F) => σ v) hAB
    simpa [f, MulAction.toPermHom_apply, LinearEquiv.smul_def] using this
  have h4 : Nat.card (Fin 2 → F) ≤ 4 := by
    simp [Nat.card_eq_fintype_card, h]
  have := Equiv.Perm.isSolvable h4
  exact Group.isSolvable_of_isSolvable_injective hf

end S0

end R3c21

end CFSG.Quasithin
