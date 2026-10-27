module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggMaxRankEdge (apos : Bool) : Fin 8 ⊕ Fin 2 → Fin 8 ⊕ Fin 2 → Bool
  | .inl i, .inl j => (i.val + 1 == j.val) || (j.val + 1 == i.val)
  | .inl i, .inr k => (k.val == 0 && i.val == 2) || (k.val == 1 && i.val == (if apos then 5 else 2))
  | .inr k, .inl i => (k.val == 0 && i.val == 2) || (k.val == 1 && i.val == (if apos then 5 else 2))
  | .inr _, .inr _ => false

@[expose] def ggMaxRankPairing (p : ℕ) (u v : ZMod p) (apos : Bool) (o o' : Fin 8 ⊕ Fin 2) :
    ZMod p :=
  if o = o' then 2 else if ggMaxRankEdge apos o o' then -1 else
    if o = Sum.inr 1 ∧ o' = Sum.inr 0 then u else
      if o = Sum.inr 0 ∧ o' = Sum.inr 1 then v else 0

@[expose] def ggMaxRankMarks (j : Fin 8) : ℕ := if j.val % 3 = 0 then 2 else if j.val % 3 = 1 then 1 else 0

@[expose] def GGResMaxRankDatum {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (sel : Prop → Prop) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) (h : Fin 8 ⊕ Fin 2 → V)
    (α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V) (u v : ZMod p) (apos : Bool),
    p = 3 ∧ Module.finrank (ZMod p) V = 9 ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o') ∧
      (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod p) • h (Sum.inl j) = 0) ∧
      (∃ f : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs),
        ∀ i, (f ((CoxeterMatrix.A 8).simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Fin 8 => φ (Sum.inl j)) ∧
      ggAutomizer L Bs = Subgroup.closure
        (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 0)}) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 1)}) ∧
      (∃ fL : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, GGIsReflection p ((fL (CoxeterMatrix.E₈.simple i) : ↥(ggAutomizer L Bs)) :
          MulAut ↥Bs)) ∧
      (∃ fK : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer K Bs),
        ∀ i, GGIsReflection p ((fK (CoxeterMatrix.E₈.simple i) : ↥(ggAutomizer K Bs)) :
          MulAut ↥Bs)) ∧
      sel (h (Sum.inr 1) ∈ Submodule.span (ZMod p)
        (h '' {o : Fin 8 ⊕ Fin 2 | o ≠ Sum.inr 1}))

@[expose] def ggMaxRankSelI : Prop → Prop := fun P => ¬ P
@[expose] def ggMaxRankSelII : Prop → Prop := fun P => P
@[expose] def ggMaxRankSelAny : Prop → Prop := fun _ => True

theorem GGResMaxRankDatum.cases {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (hD : GGResMaxRankDatum p Bs L J K ggMaxRankSelAny) :
    GGResMaxRankDatum p Bs L J K ggMaxRankSelI ∨ GGResMaxRankDatum p Bs L J K ggMaxRankSelII := by
  obtain ⟨V, i1, i2, ι, φ, h, α, u, v, apos, hp, hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hD
  by_cases hmem : h (Sum.inr 1) ∈ Submodule.span (ZMod p) (h '' {o : Fin 8 ⊕ Fin 2 | o ≠ Sum.inr 1})
  · exact Or.inr ⟨V, i1, i2, ι, φ, h, α, u, v, apos, hp, hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      hmem⟩
  · exact Or.inl ⟨V, i1, i2, ι, φ, h, α, u, v, apos, hp, hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      hmem⟩

end CFSG.StandardType

end
