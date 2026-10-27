module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggResIGlue {Λ : Type} [DecidableEq Λ] (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) :
    Matrix (Option Λ) (Option Λ) ℤ :=
  fun o o' => match o, o' with
  | some i, some j => CL i j
  | none, none => CK none none
  | none, some j => if hj : j = b then 0 else CK none (some ⟨j, hj⟩)
  | some i, none => if hi : i = b then 0 else CK (some ⟨i, hi⟩) none

@[expose] def GGResIForkShape {Λ : Type} [DecidableEq Λ] (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) : Prop :=
  ∃ c : {i : Λ // i ≠ b},
    (∀ i : {i : Λ // i ≠ b}, CL b i = if i = c then -1 else 0) ∧
    (∀ i : {i : Λ // i ≠ b}, CL i b = if i = c then -1 else 0) ∧
    (∀ i : {i : Λ // i ≠ b}, CK none (some i) = if i = c then -1 else 0) ∧
    (∀ i : {i : Λ // i ≠ b}, CK (some i) none = if i = c then -1 else 0)

@[expose] def GGTriLift (p : ℕ) (a : Fin 3 → Fin 3 → ZMod p) : Prop :=
  ∃ P01 P02 P12 τ : ℤ, 0 ≤ P01 ∧ P01 ≤ 4 ∧ 0 ≤ P02 ∧ P02 ≤ 4 ∧ 0 ≤ P12 ∧ P12 ≤ 4 ∧
    (P01 : ZMod p) = a 0 1 * a 1 0 ∧ (P02 : ZMod p) = a 0 2 * a 2 0 ∧
    (P12 : ZMod p) = a 1 2 * a 2 1 ∧
    (τ : ZMod p) = a 0 1 * a 1 2 * a 2 0 ∧ (τ : ZMod p) = a 0 2 * a 2 1 * a 1 0 ∧
    τ * τ = P01 * P02 * P12 ∧ 0 ≤ 4 - P01 - P02 - P12 + τ ∧
    ∀ i k : Fin 3, a i k = 0 ↔ a k i = 0

@[expose] def GGTriBad (p : ℕ) (a : Fin 3 → Fin 3 → ZMod p) : Prop :=
  ((a 1 2 * a 2 1 ≠ 0 ∧ a 1 2 * a 2 1 ≠ 4) ∨
      a 0 1 * a 1 2 * a 2 0 ≠ a 0 2 * a 2 1 * a 1 0 ∨ (a 1 2 = 0 ∧ a 2 1 ≠ 0) ∨
      (a 1 2 ≠ 0 ∧ a 2 1 = 0)) ∧ ¬ GGTriLift p a

@[expose] def ggTriMat {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (α₀ α₁ α₂ : Module.Dual (ZMod p) V) (h₀ h₁ h₂ : V) : Fin 3 → Fin 3 → ZMod p :=
  fun i k => (![α₀, α₁, α₂] i) (![h₀, h₁, h₂] k)

@[expose] def GGResO2aCell (p : ℕ) {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) (u v : ZMod p) : Prop :=
  p = 3 ∧ ∃ (j₀ j₁ : {i : Λ // i ≠ b}), j₀ ≠ j₁ ∧ (∀ i : Λ, i = j₀.1 ∨ i = j₁.1 ∨ i = b) ∧
    CL j₀ j₁ = -1 ∧ CL j₁ j₀ = -1 ∧ CL j₀ b = -1 ∧ CL b j₀ = -1 ∧ CL j₁ b = 0 ∧ CL b j₁ = 0 ∧
    ∃ c c' : {i : Λ // i ≠ b}, ((c = j₀ ∧ c' = j₁) ∨ (c = j₁ ∧ c' = j₀)) ∧
      CK (some c') none = 0 ∧ CK none (some c') = 0 ∧
      ((CK (some c) none = -1 ∧ CK none (some c) = -2 ∧ u = 1 ∧ v = 2) ∨
        (CK (some c) none = -2 ∧ CK none (some c) = -1 ∧ u = 2 ∧ v = 1))

@[expose] def GGResO2bCell (p : ℕ) {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) (u v : ZMod p) : Prop :=
  p = 3 ∧ ∃ (j₀ j₁ j₂ : {i : Λ // i ≠ b}), j₀ ≠ j₁ ∧ j₁ ≠ j₂ ∧ j₀ ≠ j₂ ∧
    (∀ i : Λ, i = j₀.1 ∨ i = j₁.1 ∨ i = j₂.1 ∨ i = b) ∧
    CL j₀ j₁ = -1 ∧ CL j₁ j₀ = -1 ∧ CL j₁ j₂ = -1 ∧ CL j₂ j₁ = -1 ∧ CL j₀ j₂ = 0 ∧
    CL j₂ j₀ = 0 ∧ CL j₁ b = -1 ∧ CL b j₁ = -1 ∧ CL j₀ b = 0 ∧ CL b j₀ = 0 ∧ CL j₂ b = 0 ∧
    CL b j₂ = 0 ∧
    CK (some j₁) none = 0 ∧ CK none (some j₁) = 0 ∧ CK (some j₂) none = 0 ∧
    CK none (some j₂) = 0 ∧
    ((CK (some j₀) none = -1 ∧ CK none (some j₀) = -2 ∧ u = 1 ∧ v = 2) ∨
      (CK (some j₀) none = -2 ∧ CK none (some j₀) = -1 ∧ u = 2 ∧ v = 1))

@[expose] def GGResLeviDatumCell {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop)
    (cell : ∀ {Λ : Type} (b : Λ), Matrix Λ Λ ℤ →
      Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ → ZMod p → ZMod p → Prop) :
    Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b : Λ) (ML : CoxeterMatrix Λ)
    (CL : Matrix Λ Λ ℤ) (MK : CoxeterMatrix (Option {i : Λ // i ≠ b}))
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Option Λ → MulAut ↥Bs) (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      typ ML MK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : Option {i : Λ // i ≠ b},
        α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)) ∧
      sel (LinearIndependent (ZMod p) fun i : Λ => h (some i)) (LinearIndependent (ZMod p) h) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (some i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}) ∧
      GGDeletedConnected ML b ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)) ∧
      cell b CL CK (α none (h (some b))) (α (some b) (h none))

theorem GGResLeviDatumCell.toDatum {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    {cell : ∀ {Λ : Type} (b : Λ), Matrix Λ Λ ℤ →
      Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ → ZMod p → ZMod p → Prop}
    (hD : GGResLeviDatumCell p Bs L J K sel typ cell) : GGResLeviDatum p Bs L J K sel typ := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, -⟩ := hD
  exact ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16⟩

theorem GGResLeviDatumCell.cell_mono
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    {cell cell' : ∀ {Λ : Type} (b : Λ), Matrix Λ Λ ℤ →
      Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ →
      ZMod p → ZMod p → Prop}
    (h : ∀ {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ)
      (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
      (u v : ZMod p), cell b CL CK u v → cell' b CL CK u v)
    (hD : GGResLeviDatumCell p Bs L J K sel typ cell) :
    GGResLeviDatumCell p Bs L J K sel typ cell' := by
  obtain ⟨Λ, iF, iD, b, ML, CL, MK, CK, V, iAC, iMod, ι, φ, hVec, α,
    h1, h2, h3, h4, h5, hφ, hrefl, hL, hK, hsel, hfL, hfK, hAL, hAK, hdel, hJ,
    hcell⟩ := hD
  exact ⟨Λ, iF, iD, b, ML, CL, MK, CK, V, iAC, iMod, ι, φ, hVec, α,
    h1, h2, h3, h4, h5, hφ, hrefl, hL, hK, hsel, hfL, hfK, hAL, hAK, hdel, hJ,
    h b CL CK _ _ hcell⟩

@[expose] def GGResCaseIQFourO2Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatumCell p Bs L J K ggSelI (ggTypRankLt 8)
        (fun b CL CK u v => GGResO2aCell p b CL CK u v) ∧
      ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L ∧ GGInnerDiagOnLabel GGLabQTwo p Bs K

end CFSG.StandardType
