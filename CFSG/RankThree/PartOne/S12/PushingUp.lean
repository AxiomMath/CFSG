module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped commutatorElement Pointwise

@[expose] def oResidualTwo (X : Type*) [Group X] : Subgroup X :=
  sInf {N : Subgroup X | ∃ _ : N.Normal, IsPGroup 2 (X ⧸ N)}

@[expose] def shortU (L : Type*) [Group L] : Subgroup L :=
  ⁅pCore 2 L, (⊤ : Subgroup L)⁆

@[expose] def shortC (L : Type*) [Group L] : Subgroup L :=
  shortU L ⊓ Subgroup.center L

structure IsShortGroup (L : Type) [Group L] [Finite L] : Prop where
  fitting_eq : generalizedFitting L = pCore 2 L
  residual_eq : oResidualTwo L = ⊤
  quotient_type : IsQuasisimple (L ⧸ pCore 2 L) ∨ (Nat.card (L ⧸ pCore 2 L)).Prime
  U_le_center : shortU L ≤ (Subgroup.center (pCore 2 L)).map (pCore 2 L).subtype
  nonzero : shortC L < shortU L
  irreducible : ∀ N : Subgroup L, N.Normal → N ≤ shortU L → shortC L ≤ N →
    N = shortC L ∨ N = shortU L

@[expose] def permActionTwo {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : Fin m → ZMod 2) :
    Fin m → ZMod 2 :=
  fun i => v (σ⁻¹ i)

@[expose] def IsNaturalAltModule (L : Type) [Group L] (n : ℕ) : Prop :=
  ∃ (φ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1)))
    (ψ : ↥(shortU L) →* Multiplicative (Fin (2 * n + 1) → ZMod 2)),
    (∀ u, ∑ i, Multiplicative.toAdd (ψ u) i = 0) ∧
    (∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 → ∃ u, ψ u = Multiplicative.ofAdd v) ∧
    ψ.ker = (shortC L).subgroupOf (shortU L) ∧
    ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd (permActionTwo
        ((φ (l : L ⧸ pCore 2 L) : alternatingGroup (Fin (2 * n + 1))) : Equiv.Perm _)
        (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

@[expose] def IsNaturalSLTwoModule (L : Type) [Group L] (n : ℕ) : Prop :=
  ∃ (φ : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : ↥(shortU L) →* Multiplicative (Fin 2 → GaloisField 2 n)),
    Function.Surjective ψ ∧ ψ.ker = (shortC L).subgroupOf (shortU L) ∧
    ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd
        ((φ (l : L ⧸ pCore 2 L) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

@[expose] def InClassX (L : Type) [Group L] [Finite L] : Prop :=
  IsShortGroup L ∧ ((∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule L n) ∨
    (∃ n : ℕ, 1 ≤ n ∧ IsNaturalSLTwoModule L n))

@[expose] def IsBlockInX {G : Type} [Group G] [Finite G] (L : Subgroup G) : Prop :=
  L.IsSubnormal ∧ InClassX L

structure InClassG (S : Type) [Group S] (H : Type) [Group H] [Finite H] (ι : S →* H) : Prop where
  injective : Function.Injective ι
  sylow : IsSylowOf 2 ι.range ⊤
  fitting_eq : generalizedFitting H = pCore 2 H
  quotient : ∃ n : ℕ, 1 ≤ n ∧ ∃ K : Subgroup H, ∃ _ : K.Normal,
    Nonempty ((H ⧸ K) ≃* projSL 2 (GaloisField 2 n)) ∧
    ∀ Y : Subgroup H, Y < ⊤ → Y ⊔ K = ⊤ → ¬ pCore 2 H ≤ Y

@[expose] def tripleE (H : Type) [Group H] : Subgroup H :=
  inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) (pCore 2 H)

@[expose] def tripleV (H : Type) [Group H] : Subgroup H :=
  ⁅(⊤ : Subgroup H), tripleE H⁆

@[expose] def CampbellTheoremAsPrinted : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    Subgroup.centralizer (elemThompsonCenterTorsion S 2 : Set S) = ⊤ →
    ∀ (H : Type) [Group H] [Finite H] (ι : S →* H), InClassG S H ι →
    ∀ (H₀ : Type) [Group H₀] [Finite H₀] (ι₀ : S →* H₀), InClassG S H₀ ι₀ →
      ⁅(⊤ : Subgroup H₀), (omegaOne 2 (Subgroup.center S)).map ι₀⁆ ≠ ⊥ →
      ((⨆ α : MulAut S, ((tripleE H₀).comap ι₀).map α.toMonoidHom).map ι).Normal ∨
      (⨆ α : MulAut S,
        (((tripleV H₀ ⊓ Subgroup.centralizer (ι₀.range : Set H₀)).comap ι₀).map
          α.toMonoidHom)).map ι ≤ Subgroup.center H ∨
      ((∃ α : MulAut S, ⁅tripleV H,
          (((tripleV H₀).comap ι₀).map α.toMonoidHom).map ι⁆ ≠ ⊥) ∧
        InClassX ↥(oResidualTwo H) ∧ InClassX ↥(oResidualTwo H₀))

@[expose] def pushingUpS {G : Type} [Group G] (T : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer
    ((inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) T : Subgroup G) : Set G)

@[expose] def omegaOneCenterIn {G : Type} [Group G] (T : Subgroup G) : Subgroup G :=
  omegaOne 2 ((Subgroup.center T).map T.subtype)

@[expose] def PushingUpWhenever {G : Type} [Group G] (S T₁ T₂ : Subgroup G) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ι : ↥S →* H), InClassG ↥S H ι →
    ¬ InClassX ↥(oResidualTwo H) →
      ((T₁.subgroupOf S).map ι).Normal ∨ (T₂.subgroupOf S).map ι ≤ Subgroup.center H

@[expose] def PushingUpTheoremThreeAsPrinted : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.IsCharTwoType G → ∀ T : Sylow 2 G,
    ∀ T₁ T₂ : Subgroup G, T₁ ≤ pushingUpS (T : Subgroup G) →
      (T₁.subgroupOf (pushingUpS (T : Subgroup G))).Characteristic →
      T₂ ≤ omegaOneCenterIn (T : Subgroup G) →
      PushingUpWhenever (pushingUpS (T : Subgroup G)) T₁ T₂ →
      Subgroup.centralizer (T₂ : Set G) ⊔ Subgroup.normalizer (T₁ : Set G) ≠ ⊤ →
      (pCore 2 G ≠ ⊥ → ∃ (n : ℕ) (L : Fin n → Subgroup G), (∀ i, IsBlockInX (L i)) ∧
        Subgroup.centralizer (T₂ : Set G) ⊔ Subgroup.normalizer (T₁ : Set G) ⊔ ⨆ i, L i = ⊤) ∧
      (IsSimpleGroup G →
        (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
          Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
          Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
        (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
          Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
        ∀ P : Subgroup G, IsPGroup 2 P →
          ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P)

@[expose] def KFCGTList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], CFSG.Assembly.IsCharTwoType G →
    ((∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
      (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
        Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group))) →
    CFSG.Assembly.evenRank G ≤ 2

end CFSG.RankThree.PartOne
