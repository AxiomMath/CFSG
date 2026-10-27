module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4Aligned {G : Type} [Group G] [Finite G] (p k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (e : Fin 6 ≃ Λ),
    b₁ = e 0 ∧ b₂ = e 5 ∧ Nat.card Λa = k ∧
      ML = CoxeterMatrix.E₆.reindex e ∧ GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (k = 2 → ∃ eK : Fin 6 ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
        MK = CoxeterMatrix.E₆.reindex eK) ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧ (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))

@[expose] def GGDepED4Core {G : Type} [Group G] [Finite G] (p k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b₁ b₂ : Λ) {Λa : Type}
    [Fintype Λa] [DecidableEq Λa] (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (e : Fin 6 ≃ Λ)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (xV : V) : Prop :=
  b₁ = e 0 ∧ b₂ = e 5 ∧ Nat.card Λa = k ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
    (k = 2 → ∃ eK : Fin 6 ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
      MK = CoxeterMatrix.E₆.reindex eK) ∧
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    GGDepEFrame p (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV ∧
    (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
    (∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
    (∃ a : Λa, α (Sum.inr a) xV ≠ 0) ∧
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))

@[expose] def GGDepED4UpCfg {G : Type} [Group G] [Finite G] (p k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (e : Fin 6 ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV : V),
    GGDepED4Core p k Bs L J K b₁ b₂ MK CK ι e φ h α xV ∧ Module.finrank (ZMod p) V = 7

end CFSG.StandardType

end
