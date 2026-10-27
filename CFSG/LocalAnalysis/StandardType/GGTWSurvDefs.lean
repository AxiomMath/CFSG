module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGHLLines
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWHLAt {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs L : Subgroup G) (x : G) : Prop :=
  ∃ hxB : x ∈ Bs,
    ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ},
      GGIsWeylMatrix M → GGIntCartan M C →
      ∀ {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) → (∀ i, GGIsReflection p (φ i)) →
      (∀ i j, α i (h j) = (C i j : ZMod p)) → ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ∀ t ∈ ggInduced ⊤ Bs, GGIsReflection p t → t ⟨x, hxB⟩ = ⟨x, hxB⟩ →
        GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h)
          (ι (Additive.ofMul ⟨x, hxB⟩)) (ggLin (p := p) ι t)

@[expose] def GGTWAligned {G : Type} [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (pos : GGTWPos) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type)
    (_ : Fintype Λa) (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (e : Fin (N - 1) ≃ Λ),
    b₁ ≠ b₂ ∧ Nat.card Λa = k ∧
      (∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂)) ∧
      ML = (CoxeterMatrix.A (N - 1)).reindex e ∧ GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (k = 2 → ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
        MK = (CoxeterMatrix.A (N - 1)).reindex eK) ∧
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

@[expose] def GGTWVCfg (p N k : ℕ) [Fact p.Prime] : Prop :=
  ∃ (pos : GGTWPos) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (Λ : Type)
    (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (e : Fin (N - 1) ≃ Λ) (r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV yV : V),
    b₁ ≠ b₂ ∧ Nat.card Λa = k ∧
      (∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂)) ∧
      GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (k = 2 → ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
        MK = (CoxeterMatrix.A (N - 1)).reindex eK) ∧
      (∀ o w, r o w = w - α o w • h o) ∧
      GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV ∧
      Module.finrank (ZMod p) V = N - 1 ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∀ g ∈ Subgroup.closure (Set.range r),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      (∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
        GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g) ∧
      (∃ a : Λa, α (Sum.inr a) xV ≠ 0) ∧ yV ≠ 0 ∧
      (∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV) ∧
      (∀ a : Λa, r (Sum.inr a) yV = yV)

end CFSG.StandardType
