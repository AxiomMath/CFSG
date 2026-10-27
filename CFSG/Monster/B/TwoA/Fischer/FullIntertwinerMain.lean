module

public import CFSG.Monster.B.TwoA.Fischer.FullIntertwiner
public import CFSG.Monster.B.TwoA.Fischer.CliqueModule

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

theorem full_clique_action_intertwiner'
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k)) :
    ∃ Φ : Y ≃ CFSG.Monster.B.Fischer.Y,
      IsCliqueIntertwiner act lab Y C x η φ α Φ ∧
      (∀ v : Y, (v : V) = x → Φ v = o) ∧
      (∀ T₀ : Finset C, T₀.image (fun z => (η z : Fin 24)) = B₀ →
        (∀ v : Y, (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          ∃ q : Q₀, Φ v = Sum.inr (Sum.inr (zMk 1 q))) ∧
        (∀ (r : Subgroup.closure (lab '' C)) (v w : Y) (q : Q₀),
          (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          (w : V) = act (r : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
          Φ w = Sum.inr (Sum.inr (zMk 1 (q + U₀.mkQ (φ (Additive.ofMul r)))))) ∧
        ∀ (k : setStab act lab Y C) (hk : θ k ∈ KB) (v w : Y) (q : Q₀), act (k : S) x = x →
          (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          (w : V) = act (k : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
          Φ w = Sum.inr (Sum.inr (zMk 1 (affA ⟨θ k, hk⟩ q)))) ∧
      ∀ Φ' : Y ≃ CFSG.Monster.B.Fischer.Y, IsCliqueIntertwiner act lab Y C x η φ α Φ' →
        Φ' = Φ :=
  hS.full_clique_action_intertwiner hC hx hη hθ hφ
    ((hS.clique_exact_binary_M22_module hC η θ hη hθ).2.2.1 φ hφ) hα

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
