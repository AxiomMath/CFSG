module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGResConjWire

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDeletedConnectedS {Λ : Type} (ML : CoxeterMatrix Λ) (S : Finset Λ) : Prop :=
  ∀ i j : {i : Λ // i ∉ S},
    Relation.ReflTransGen (fun u v : {i : Λ // i ∉ S} => u ≠ v ∧ ML.M u v ≠ 2) i j

@[expose] def GGResLeviDatumLE3 {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    2 ≤ S.card ∧ S.card ≤ 3 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      typ ML MK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      sel (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i)) (LinearIndependent (ZMod p) h) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnectedS ML S ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))

@[expose] def GGResLeviSideDatumLE3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (M : CoxeterMatrix Λ)
    (C : Matrix Λ Λ ℤ) (MJ : CoxeterMatrix {j : Λ // j ∉ S})
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    2 ≤ S.card ∧ S.card ≤ 3 ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧ GGIsWeylMatrix MJ ∧
      (∀ j j' : {j : Λ // j ∉ S}, MJ.M j j' = M.M j j') ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs), ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ∉ S} => φ j) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : {j : Λ // j ∉ S} => φ j)

@[expose] def GGTBJInputR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨
      GGResRowAt ggRowNonLevi p J L) ∧
      (GGResXDatum p Bs K → GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨
        GGResRowAt ggRowNonLevi p J K)

@[expose] def GGResModelInputR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResLeviDatum p Bs L J K ggSelAny ggTypAny ∨ GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny ∨
      GGResRowAt ggRowNonLevi p J L ∨ GGResRowAt ggRowNonLevi p J K

@[expose] def ggRowCorank2C (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  p = 3 ∧ (J.tag = .B ∨ J.tag = .C) ∧ J.n = 1 ∧ (X.tag = .B ∨ X.tag = .C) ∧ X.n = 1 ∧
    X.rank = J.rank + 2

@[expose] def ggRowSUCorank2 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  p = 3 ∧ J.tag = .twA ∧ J.n = 1 ∧ X.tag = .twA ∧ X.n = 1 ∧ X.rank = J.rank + 2 ∧
    6 ≤ X.rank ∧ ¬ (3 ∣ X.rank + 1)

@[expose] def ggRowDCorank2 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  p = 3 ∧ (J.tag = .D ∨ J.tag = .twD) ∧ (X.tag = .D ∨ X.tag = .twD) ∧ J.n = 1 ∧ X.n = 1 ∧
    X.rank = J.rank + 2 ∧ 6 ≤ X.rank

@[expose] def ggRowSUCorank3 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  p = 3 ∧ J.tag = .twA ∧ J.n = 1 ∧ X.tag = .twA ∧ X.n = 1 ∧ X.rank = J.rank + 3 ∧
    8 ≤ X.rank ∧ 3 ∣ X.rank + 1

@[expose] def GGResCorank2CInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K

@[expose] def GGResSUCorank2Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K

@[expose] def GGResDCorank2Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowDCorank2 p J L ∨ GGResRowAt ggRowDCorank2 p J K

@[expose] def GGResSUCorank3Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowSUCorank3 p J L ∨ GGResRowAt ggRowSUCorank3 p J K

@[expose] def GGResMultiNodeRestInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    (GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResLeviDatumCard (k : ℕ) {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    S.card = k ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      typ ML MK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      sel (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i)) (LinearIndependent (ZMod p) h) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnectedS ML S ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))

section Datum

variable {G : Type} [Group G] [Finite G] {k p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
  {sel : Prop → Prop → Prop}
  {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}

theorem GGResLeviDatumCard.aj_le (hD : GGResLeviDatumCard k p Bs L J K sel typ) :
    ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgenL, hgenK, -, hgenJ⟩ := hD
  rw [hgenJ, hgenL, hgenK]
  refine le_inf (Subgroup.closure_mono ?_) (Subgroup.closure_mono ?_)
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact Or.inl ⟨j, rfl⟩

end Datum

abbrev GGResLeviDatumExact2 {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  GGResLeviDatumCard 2 p Bs L J K sel typ

abbrev GGResLeviDatumExact3 {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  GGResLeviDatumCard 3 p Bs L J K sel typ

theorem ggResLeviDatumLE3_iff_exact2_or_exact3 {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) :
    GGResLeviDatumLE3 p Bs L J K sel typ ↔
      (GGResLeviDatumExact2 p Bs L J K sel typ ∨
        GGResLeviDatumExact3 p Bs L J K sel typ) := by
  unfold GGResLeviDatumLE3 GGResLeviDatumExact2 GGResLeviDatumExact3 GGResLeviDatumCard
  constructor
  · intro h
    obtain ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
      hcard, hrest⟩ := h
    rcases (by omega : S.card = 2 ∨ S.card = 3) with hk | hk
    · exact Or.inl ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        hk, hrest.2⟩
    · exact Or.inr ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        hk, hrest.2⟩
  · intro h
    rcases h with h | h
    · obtain ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        hk, hrest⟩ := h
      exact ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        by omega, by omega, hrest⟩
    · obtain ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        hk, hrest⟩ := h
      exact ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V, hV, hVd, ι, φ, h, α,
        by omega, by omega, hrest⟩

@[expose] def ggReservedRows {G : Type} [Group G] (p : ℕ) (J L K : Subgroup G) : Prop :=
  GGResRowAt ggRowSUCorank3 p J L ∨ GGResRowAt ggRowSUCorank3 p J K ∨
    GGResRowAt ggRowDCorank2 p J L ∨ GGResRowAt ggRowDCorank2 p J K

@[expose] def GGResMultiNodeRestThreeOutsideRowsInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResMultiNodeRestTwoOnlyOutsideRowsInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    (GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

theorem ggResMultiNodeRestInput_of_reserved_two_three
    (hA : GGResSUCorank3Input)
    (hD : GGResDCorank2Input)
    (h2 : GGResMultiNodeRestTwoOnlyOutsideRowsInput)
    (h3 : GGResMultiNodeRestThreeOutsideRowsInput) :
    GGResMultiNodeRestInput := by
  intro G _ _ p B Bs x L D J y K hH hp hF hS hE hR
  by_cases hSU : GGResRowAt ggRowSUCorank3 p J L ∨ GGResRowAt ggRowSUCorank3 p J K
  · exact hA G p B Bs x L D J y K hH hF hS hE hSU
  by_cases hDrow : GGResRowAt ggRowDCorank2 p J L ∨ GGResRowAt ggRowDCorank2 p J K
  · exact hD G p B Bs x L D J y K hH hF hS hE hDrow
  have hres : ¬ ggReservedRows p J L K := by
    intro hr
    rcases hr with hr | hr | hr | hr
    · exact hSU (Or.inl hr)
    · exact hSU (Or.inr hr)
    · exact hDrow (Or.inl hr)
    · exact hDrow (Or.inr hr)
  have hsplit : (GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) ∨
      (GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
    rcases hR.1 with hL | hK
    · exact Or.inl ((ggResLeviDatumLE3_iff_exact2_or_exact3 (p := p) (Bs := Bs)
        (L := L) (J := J) (K := K) (sel := ggSelAny) (typ := ggTypAny)).mp hL)
    · exact Or.inr ((ggResLeviDatumLE3_iff_exact2_or_exact3 (p := p) (Bs := Bs)
        (L := K) (J := J) (K := L) (sel := ggSelAny) (typ := ggTypAny)).mp hK)
  by_cases h3L : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny
  · exact h3 G p B Bs x L D J y K hH hF hS hE
      ⟨Or.inl h3L, hres, hR.2.1, hR.2.2.1, hR.2.2.2⟩
  by_cases h3K : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny
  · exact h3 G p B Bs x L D J y K hH hF hS hE
      ⟨Or.inr h3K, hres, hR.2.1, hR.2.2.1, hR.2.2.2⟩
  refine h2 G p B Bs x L D J y K hH hF hS hE
    ⟨?_, not_or.mpr ⟨h3L, h3K⟩, hres, hR.2.1, hR.2.2.1, hR.2.2.2⟩
  rcases hsplit with (h2L | h3L') | (h2K | h3K')
  · exact Or.inl h2L
  · exact absurd h3L' h3L
  · exact Or.inr h2K
  · exact absurd h3K' h3K

end CFSG.StandardType
