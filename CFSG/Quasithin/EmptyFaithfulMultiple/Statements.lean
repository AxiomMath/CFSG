module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Families
public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def IsLThreeTwoOrASix (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 6))

@[expose] def wreathSThreeTwo : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∀ i j : Fin 6, (i.val / 3 = j.val / 3 ↔ (σ i).val / 3 = (σ j).val / 3)}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    exact (hτ i j).trans (hσ (τ i) (τ j))
  inv_mem' := by
    intro σ hσ i j
    have h := hσ (σ⁻¹ i) (σ⁻¹ j)
    have hi : σ (σ⁻¹ i) = i := (Equiv.eq_symm_apply σ).mp rfl
    have hj : σ (σ⁻¹ j) = j := (Equiv.eq_symm_apply σ).mp rfl
    rw [hi, hj] at h
    exact h.symm

variable {G : Type*} [Group G]

@[expose] def O2pOf (M : Subgroup G) (p : ℕ) : Subgroup G := (O2p (↥M) p).map M.subtype

@[expose] def eOf (T : Subgroup G) : Subgroup G := omegaOneCenterOf (thompsonJ T)

@[expose] def eYOf (T Y : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) ⊓ Subgroup.centralizer (Y : Set G)

@[expose] def eCentOf (T Y : Subgroup G) : Subgroup G :=
  eOf T ⊓ Subgroup.centralizer (Y : Set G)

variable (G) [Finite G] (T : Subgroup G)

@[expose] def Stmt1542One : Prop := ∀ L : Subgroup G, ¬ quasithinIsLocal T L

@[expose] def Stmt1542Two : Prop := ∀ M : Subgroup G, InM T M → Group.IsSolvable M

@[expose] def Stmt1542Three : Prop :=
  ∀ X : Subgroup G, IsXi T X →
    ⁅quasithinOmegaOneCenter T, X⁆ ≠ ⊥ ∧ IsXiStarF T X ∧ ¬ IsXiPlus T X ∧
      ((∃ k : ℕ, (pCoreOf 2 X).relIndex X = 3 ^ k) ∨ ∃ k : ℕ, (pCoreOf 2 X).relIndex X = 5 ^ k)

@[expose] def Stmt1542Four : Prop :=
  ∀ M₀ M V : Subgroup G, InH T M₀ → IsUniqueM M₀ M → V ≠ ⊥ → ∀ hV : IsTwoReducedIn M₀ V,
    T ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (M₀ ⊓ Subgroup.centralizer (V : Set G)) →
    V ≤ pCoreOf 2 M → qhatInt M₀ V hV.2.2.1 ≤ 2

@[expose] def Stmt1543 : Prop :=
  ∀ (X : Subgroup G) (p : ℕ), IsSmallXi T X → (pCoreOf 2 X).relIndex X = p →
    (∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ p) → 3 < p →
    IsSmallXiStar T X ∧
      (∀ M : Subgroup G, InM (X ⊔ T) M → X ≤ O2pOf M p ∧ pCoreOf 2 X ≤ pCoreOf 2 M) ∧
      ⁅quasithinOmegaOneCenter T, X⁆ ≠ ⊥ ∧ IsSmallXiF T X ∧ p = 5

@[expose] def Stmt1544 : Prop :=
  ∀ M : Subgroup G, InM T M → ∀ q : ℕ, q.Prime → q ∣ Nat.card M → q = 2 ∨ q = 3 ∨ q = 5

@[expose] def Stmt1545 : Prop :=
  ∀ q : ℕ, q.Prime →
    q ∣ Nat.card (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) → q = 2 ∨ q = 3

@[expose] def Stmt1546 : Prop :=
  ∀ M : Subgroup G, IsOrdMaximal T M → ⁅VZ T M, thompsonJ T⁆ = ⊥ →
    ∀ M' : Subgroup G, InM T M' → OrdLE T M' M

@[expose] def Stmt1547 : Prop :=
  Nat.card (quasithinOmegaOneCenter T) = 2 →
    (∃ C₂ Mf : Subgroup G, C₂ ≠ ⊥ ∧ C₂ ≤ baum T ∧ (C₂.subgroupOf (baum T)).Characteristic ∧
      IsUniqueM (Subgroup.normalizer (C₂ : Set G)) Mf ∧ InM T Mf ∧
      ∀ M : Subgroup G, InM T M → OrdLE T M Mf) ∨
    IsLThreeTwoOrASix G

@[expose] def Stmt1548 : Prop := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = T

@[expose] def IsXFamily1548 (X : Subgroup G) : Prop :=
  IsSmallXi T X ∧ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (X : Set G)

@[expose] def Stmt1549 : Prop :=
  Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≠ T →
    ∃ X : Subgroup G, IsXFamily1548 G T X

@[expose] def Stmt15410 : Prop :=
  ∀ X : Subgroup G, IsXFamily1548 G T X → ∀ M : Subgroup G, InM (X ⊔ T) M →
    X ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G)

@[expose] def Stmt15411 : Prop :=
  ∀ M : Subgroup G, InM T M →
    pCoreOf 2 M = M ⊓ Subgroup.centralizer (VZ T M : Set G) ∧ IsOrdMaximal T M ∧
      (¬ ∃ M₀ : Subgroup G, InM T M₀ ∧ ∀ M' : Subgroup G, InM T M' → OrdLE T M' M₀) ∧
      ⁅VZ T M, thompsonJ T⁆ ≠ ⊥

@[expose] def Concl15412Six (M Y : Subgroup G) : Prop :=
  ((pCoreOf 2 Y).relIndex Y = 3 ∧ quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) ∧
      (eCentOf T Y).relIndex (eOf T) = 2) ∨
    ((pCoreOf 2 Y).relIndex Y = 9 ∧ quasithinO2QuotientIso (Y ⊔ T) wreathSThreeTwo ∧
      ∃ Y₁ Y₂ : Subgroup G, Y = Y₁ ⊔ Y₂ ∧ Y₁ = oTwoUpper Y₁ ∧ Y₂ = oTwoUpper Y₂ ∧
        (pCoreOf 2 Y₁).relIndex Y₁ = 3 ∧ (pCoreOf 2 Y₂).relIndex Y₂ = 3 ∧
        ⁅VZ T M, Y⁆ = ⁅VZ T M, Y₁⁆ ⊔ ⁅VZ T M, Y₂⁆ ∧ ⁅VZ T M, Y₁⁆ ⊓ ⁅VZ T M, Y₂⁆ = ⊥ ∧
        Nat.card (⁅VZ T M, Y₁⁆ : Subgroup G) = 4 ∧ Nat.card (⁅VZ T M, Y₂⁆ : Subgroup G) = 4 ∧
        ⁅Y₁, thompsonJ T⁆ = Y₁ ∧ ⁅Y₂, thompsonJ T⁆ = Y₂ ∧
        baum T ≤ Subgroup.normalizer (Y₁ : Set G) ∧ baum T ≤ Subgroup.normalizer (Y₂ : Set G) ∧
        (∃ t ∈ T, Y₂ = Y₁.map (MulAut.conj t).toMonoidHom) ∧
        (eCentOf T Y).relIndex (eOf T) = 4 ∧
        Y ≤ Subgroup.normalizer (Y₁ : Set G) ∧ Y ≤ Subgroup.normalizer (Y₂ : Set G))

@[expose] def Stmt15412 : Prop :=
  ∀ M : Subgroup G, InM T M →
    (∃ Y : Subgroup G, IsYFamily T Y ∧ Y ≤ M) ∧
    ∀ Y : Subgroup G, IsYFamily T Y → Y ≤ M →
      M ≤ Subgroup.normalizer (Y : Set G) ∧
      M = Subgroup.normalizer (Y : Set G) ∧ IsUniqueM (Y ⊔ T) M ∧
      (∃ s : ℕ, (s = 1 ∨ s = 2) ∧ (pCoreOf 2 Y).relIndex Y = 3 ^ s ∧
        (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) ∧ Nat.card (⁅VZ T M, Y⁆ : Subgroup G) = 4 ^ s) ∧
      IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧
      (twoReducedJoin (Y ⊔ T) = ⁅VZ T M, Y⁆ ⊔ eYOf T Y ∧ ⁅VZ T M, Y⁆ ⊓ eYOf T Y = ⊥ ∧
        eOf T = eCentOf T Y ⊔ (⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ∧
        eCentOf T Y ⊓ (⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥) ∧
      Concl15412Six G T M Y ∧
      ∃ N : Subgroup G, MinParabolic (Y ⊔ T) T N

@[expose] def Stmt15413 : Prop :=
  ∀ Y : Subgroup G, IsYFamily T Y →
    IsEmpty (↥(Y ⊔ T) ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Stmt15414 : Prop :=
  ¬ IsLThreeTwoOrASix G →
    (∀ Y : Subgroup G, IsYFamily T Y →
      (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (Y : Set G)).relIndex
        (quasithinOmegaOneCenter T) = 2) ∧
    Nat.card (quasithinOmegaOneCenter T) = 4

@[expose] def Stmt15415 : Prop :=
  ¬ IsLThreeTwoOrASix G →
    ∀ M₁ M₂ Y₁ Y₂ : Subgroup G, InM T M₁ → InM T M₂ →
      IsYFamily T Y₁ → Y₁ ≤ M₁ → (pCoreOf 2 Y₁).relIndex Y₁ = 3 →
      IsYFamily T Y₂ → Y₂ ≤ M₂ → (pCoreOf 2 Y₂).relIndex Y₂ = 3 → M₁ = M₂

@[expose] def Stmt15416 : Prop :=
  ∀ M : Subgroup G, InM T M → Subgroup.normalizer (baum T : Set G) ≤ M

@[expose] def Stmt15417 : Prop :=
  ∀ B H I : Subgroup G, B ≠ ⊥ → B ≤ T →
    B ⊔ Subgroup.centralizer (B : Set G) ≤ H → H ≤ Subgroup.normalizer (B : Set G) →
    IsSylowTwoOf (T ⊓ H) H → T ⊓ H ≤ I → I ≤ H →
    (∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 → ∀ Mz : Subgroup G,
      InM (Subgroup.centralizer ({z} : Set G)) Mz → Lemma115Hyp I (T ⊓ H) Mz z) ∧
    (quasithinOmegaOneCenter T ⊓ pCoreOf 2 I ≠ ⊥ → CharTwo I)

@[expose] def Stmt15418 : Prop :=
  ¬ IsLThreeTwoOrASix G → ∀ Y : Subgroup G, IsYFamily T Y → (pCoreOf 2 Y).relIndex Y = 9

end CFSG.Quasithin.EmptyFaithfulMultiple
