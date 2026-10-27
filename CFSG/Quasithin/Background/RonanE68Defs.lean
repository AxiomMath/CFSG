module

public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.Background.E6EightMarkedRoots
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

namespace RonanE68

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Defs

variable {G : Type} [Group G]

@[expose] def autSubInduced (L X : Subgroup G) : Subgroup (MulAut ↥L) where
  carrier := {α | ∃ g ∈ X ⊓ Subgroup.normalizer (L : Set G),
    ∀ x : ↥L, ((α x : ↥L) : G) = g * (x : G) * g⁻¹}
  one_mem' := ⟨1, Subgroup.one_mem _, fun x => by simp⟩
  mul_mem' := by
    rintro α β ⟨g, hg, hα⟩ ⟨h, hh, hβ⟩
    refine ⟨g * h, Subgroup.mul_mem _ hg hh, fun x => ?_⟩
    rw [MulAut.mul_apply, hα, hβ]
    group
  inv_mem' := by
    rintro α ⟨g, hg, hα⟩
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, fun x => ?_⟩
    have h1 : ((α (α⁻¹ x) : ↥L) : G) = (x : G) := by simp
    rw [hα] at h1
    have h2 : (((α⁻¹ x : ↥L)) : G) = g⁻¹ * (x : G) * g := by
      calc (((α⁻¹ x : ↥L)) : G) = g⁻¹ * (g * ((α⁻¹ x : ↥L) : G) * g⁻¹) * g := by group
        _ = g⁻¹ * (x : G) * g := by rw [h1]
    rw [h2]
    simp

@[expose] def Case1P {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  ∃ n : ℕ,
    ((2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel ↥L 2 n) ∨
      (1 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 n) ∨
      (n = 2 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2 ∧
        IsPGroup 2 (Subgroup.center ↥L))) ∧
    L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
      Set G) ∧
    IsCyclic (autI hV (L ⊓ M)) ∧ Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1 ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V ∧ E3.mQuot ⁅V, L ⊓ M⁆ ⊥ = n)

@[expose] def Case2P (T M V U L : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ((2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n) ∨
      (n = 1 ∧ Nonempty (↥L ≃* alternatingGroup (Fin 6)))) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V) ∧
    ((L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ∧
      ((E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 2 * n ∧
          ∃ A : Subgroup G, U < A ∧ A < V ∧ E3.mQuot V A = n ∧
            ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M) ∨
        (n = 1 ∧ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1))) ∨
     (L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ≤ L ⊓ M ∧ L ⊓ M < L ∧
      (∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) ∧
      E6.IsMarkedSp4Root n (autSubInduced L (L ⊔ V)) (autSubInduced L V) ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n))

@[expose] def EqualityScope (M V U : Subgroup G) : Prop :=
  E3.mQuot V U = 1 ∨
    ∀ W : Subgroup G, W ∈ E6.gammaE64 V M → U ≤ W → W = U

@[expose] def Case3P (T M V U L : Subgroup G) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 4 2 1 ∧
    Nonempty ((↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⧸
      CFSG.pCore 2 ↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)))) ≃* Equiv.Perm (Fin 8)) ∧
    U ≤ V ⊓ Subgroup.centralizer (L : Set G) ∧
    (EqualityScope M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

@[expose] def Case5P (M V U L : Subgroup G) : Prop :=
  ((∃ p : ℕ, CFSG.QuasithinUnique.Ch1.IsFermatOrMersennePrime p ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 p 1) ∨
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1 ∨
      Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
    U ≤ V ⊓ Subgroup.centralizer (L : Set G) ∧
    (EqualityScope M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

@[expose] def OutP {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  Case1P hV T M U L ∨ Case2P T M V U L ∨ Case3P T M V U L ∨ E6.E68Case4 M V U L ∨
    Case5P M V U L

end Defs

end RonanE68

end CFSG.Quasithin
