module

public import CFSG.Quasithin.H13.A5W1618l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem exists_conj_of_isSylowTwoOf_top {X : Type*} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem isSylowTwoOf_map_top {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (φ : A →* B) (hφ : Function.Surjective φ) {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map φ) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  refine ⟨le_top, hS.2.1.map φ, ?_⟩
  rw [show ((S.map φ).subgroupOf ⊤).index = (S.map φ).index from Subgroup.relIndex_top_right _]
  exact fun h => hidx (h.trans (Subgroup.index_map_dvd S hφ))

end CFSG.Quasithin.H13.A5
