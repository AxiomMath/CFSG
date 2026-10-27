module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDeletedConnected2 {Λ : Type} (ML : CoxeterMatrix Λ) (b₁ b₂ : Λ) : Prop :=
  ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
    Relation.ReflTransGen (fun u v : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} => u ≠ v ∧ ML.M u v ≠ 2) i j

@[expose] def GGResTwoNodeDatum {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    b₁ ≠ b₂ ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 2 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      typ ML MK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      sel (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i)) (LinearIndependent (ZMod p) h) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnected2 ML b₁ b₂ ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j))

@[expose] def GGResTwoNodeSideDatum {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (M : CoxeterMatrix Λ)
    (C : Matrix Λ Λ ℤ) (MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂})
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    b₁ ≠ b₂ ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧ GGIsWeylMatrix MJ ∧
      (∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ.M j j' = M.M j j') ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs), ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j)

@[expose] def GGTBJTwoNodeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResRowAt ggRowTwoNode p J L → GGResTwoNodeSideDatum p Bs L J) ∧
      (GGResXDatum p Bs K → GGResRowAt ggRowTwoNode p J K → GGResTwoNodeSideDatum p Bs K J)

theorem ggResTwoNodeDatum_mono {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {sel sel' : Prop → Prop → Prop}
    {typ typ' : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResTwoNodeDatum p Bs L J K sel typ) (hsel : ∀ l a : Prop, sel l a → sel' l a)
    (htyp : ∀ {Λ Λ' : Type} (M : CoxeterMatrix Λ) (M' : CoxeterMatrix Λ'), typ M M' → typ' M M') :
    GGResTwoNodeDatum p Bs L J K sel' typ' := by
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hb, hc1, hc2, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hD
  exact ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hb, hc1, hc2, h1,
    h2, h3, h4, htyp _ _ h5, h6, h7, h8, h9, hsel _ _ h10, h11, h12, h13, h14, h15, h16⟩

end CFSG.StandardType
