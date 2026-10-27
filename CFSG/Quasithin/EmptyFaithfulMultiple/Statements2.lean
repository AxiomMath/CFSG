module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsSixTwoData (T M Y Y₁ Y₂ : Subgroup G) : Prop :=
  Y = Y₁ ⊔ Y₂ ∧ Y₁ = oTwoUpper Y₁ ∧ Y₂ = oTwoUpper Y₂ ∧
    (pCoreOf 2 Y₁).relIndex Y₁ = 3 ∧ (pCoreOf 2 Y₂).relIndex Y₂ = 3 ∧
    ⁅VZ T M, Y⁆ = ⁅VZ T M, Y₁⁆ ⊔ ⁅VZ T M, Y₂⁆ ∧ ⁅VZ T M, Y₁⁆ ⊓ ⁅VZ T M, Y₂⁆ = ⊥ ∧
    Nat.card (⁅VZ T M, Y₁⁆ : Subgroup G) = 4 ∧ Nat.card (⁅VZ T M, Y₂⁆ : Subgroup G) = 4 ∧
    ⁅Y₁, thompsonJ T⁆ = Y₁ ∧ ⁅Y₂, thompsonJ T⁆ = Y₂ ∧
    baum T ≤ Subgroup.normalizer (Y₁ : Set G) ∧ baum T ≤ Subgroup.normalizer (Y₂ : Set G) ∧
    (∃ t ∈ T, Y₂ = Y₁.map (MulAut.conj t).toMonoidHom) ∧
    (eCentOf T Y).relIndex (eOf T) = 4 ∧
    Y ≤ Subgroup.normalizer (Y₁ : Set G) ∧ Y ≤ Subgroup.normalizer (Y₂ : Set G)

theorem concl15412Six_iff {T M Y : Subgroup G} :
    Concl15412Six G T M Y ↔
      ((pCoreOf 2 Y).relIndex Y = 3 ∧ quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) ∧
          (eCentOf T Y).relIndex (eOf T) = 2) ∨
        ((pCoreOf 2 Y).relIndex Y = 9 ∧ quasithinO2QuotientIso (Y ⊔ T) wreathSThreeTwo ∧
          ∃ Y₁ Y₂ : Subgroup G, IsSixTwoData T M Y Y₁ Y₂) :=
  Iff.rfl

variable [Finite G]

variable (G) (T : Subgroup G)

structure Setting15419 where
  M₁ : Subgroup G
  M₂ : Subgroup G
  X : Subgroup G
  Y : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  Y₁ : Subgroup G
  Y₂ : Subgroup G
  L₁ : Subgroup G
  L₂ : Subgroup G
  inM₁ : InM T M₁
  inM₂ : InM T M₂
  ne : M₁ ≠ M₂
  famX : IsYFamily T X
  le_X : X ≤ M₁
  famY : IsYFamily T Y
  le_Y : Y ≤ M₂
  dataX : IsSixTwoData T M₁ X X₁ X₂
  dataY : IsSixTwoData T M₂ Y Y₁ Y₂
  choice₁ : L₁ = X₁ ∨ L₁ = X₂
  choice₂ : L₂ = Y₁ ∨ L₂ = Y₂

namespace Setting15419

variable {G T}

@[expose] def T₀ (s : Setting15419 G T) : Subgroup G :=
  T ⊓ Subgroup.normalizer (s.Y₁ : Set G) ⊓ Subgroup.normalizer (s.X₁ : Set G)

@[expose] def G₁ (s : Setting15419 G T) : Subgroup G := s.L₁ ⊔ s.T₀

@[expose] def G₂ (s : Setting15419 G T) : Subgroup G := s.L₂ ⊔ s.T₀

@[expose] def I (s : Setting15419 G T) : Subgroup G := s.G₁ ⊔ s.G₂

@[expose] def V₁ (s : Setting15419 G T) : Subgroup G := ⁅VZ T s.M₁, s.L₁⁆

@[expose] def V₂ (s : Setting15419 G T) : Subgroup G := ⁅VZ T s.M₂, s.L₂⁆

end Setting15419

@[expose] def Stmt15419 : Prop :=
  ∀ s : Setting15419 G T,
    eOf T ⊓ Subgroup.centralizer (s.I : Set G) ≠ ⊥ ∧
      eOf T ⊓ Subgroup.centralizer (s.I : Set G) ≤ centerOf s.I ∧ pCoreOf 2 s.I ≠ ⊥ ∧
      ¬ s.L₂ ≤ s.M₁ ∧ ¬ s.L₁ ≤ s.M₂ ∧
      quasithinOmegaOneCenter T ⊓ (centerOf s.I ⊔ s.V₁) ≠ ⊥

@[expose] def Stmt15420 : Prop :=
  ∀ s : Setting15419 G T, ∀ I₀ : Subgroup G, InH s.I I₀ → IsSylowTwoOf s.T₀ I₀

@[expose] def Stmt15421 : Prop :=
  ∀ s : Setting15419 G T, CharTwo s.I →
    s.I = s.L₁ ⊔ s.L₂ ⊔ s.T₀ ∧ s.I ≤ Subgroup.normalizer (s.L₁ : Set G) ∧
      s.I ≤ Subgroup.normalizer (s.L₂ : Set G)

@[expose] def Stmt15422 : Prop :=
  ∀ s : Setting15419 G T, ¬ CharTwo s.I →
    ∃ K : Subgroup G, K = oTwoUpper s.I ∧ s.I = K ⊔ s.T₀ ∧
      Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
      ∃ φ : s.I →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = (T ⊓ Subgroup.centralizer (K : Set G)).subgroupOf s.I

@[expose] def Stmt15423 : Prop := ∀ s : Setting15419 G T, ¬ CharTwo s.I

end CFSG.Quasithin.EmptyFaithfulMultiple
