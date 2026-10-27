module

public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Defs

variable {G : Type} [Group G]

@[expose] def uHi (T M H Hi : Subgroup G) : Subgroup G :=
  ⁅conjClosure (VZ T M) H, Hi⁆ ⊔ quasithinOmegaOneCenter T

@[expose] def uK (T M H : Subgroup G) : Subgroup G := ⁅conjClosure (VZ T M) H, H⁆

@[expose] def SecIso (A Q : Subgroup G) (X : Type*) [Group X] : Prop :=
  ∃ _ : (Q.subgroupOf A).Normal, Nonempty ((↥A ⧸ Q.subgroupOf A) ≃* X)

structure IsRedCE (T M H PQ : Subgroup G) (p : ℕ) : Prop where
  isHTM : IsHTM T M H
  prime : p.Prime
  odd : p ≠ 2
  le : PQ ≤ H
  lt : pCoreOf 2 H < PQ
  pSec : ∀ x ∈ PQ, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H
  eq : H = PQ ⊔ T
  normal : H ≤ Subgroup.normalizer (PQ : Set G)
  minimal : ∀ N : Subgroup G, pCoreOf 2 H ≤ N → N ≤ PQ → H ≤ Subgroup.normalizer (N : Set G) →
    N = pCoreOf 2 H ∨ N = PQ

@[expose] def PMaximal (T M : Subgroup G) (p : ℕ) : Prop :=
  ∀ H₀ : Subgroup G, IsHTM T M H₀ → ∀ q : ℕ, q.Prime → q ≠ 2 →
    CFSG.pCore q (OTwoQuot H₀) ≠ ⊥ → q ≤ p

structure IsDec12 (T M H : Subgroup G) (p : ℕ) (H₀ H₁ H₂ : Subgroup G) (t : G) : Prop where
  le : H₀ ≤ H
  index : H₀.relIndex H = 2
  Q₁ : pCoreOf 2 H ≤ H₁
  Q₂ : pCoreOf 2 H ≤ H₂
  le₁ : H₁ ≤ H₀
  le₂ : H₂ ≤ H₀
  sup : H₀ = H₁ ⊔ H₂
  inf : H₁ ⊓ H₂ = pCoreOf 2 H
  comm : ⁅H₁, H₂⁆ ≤ pCoreOf 2 H
  dihedral₁ : SecIso H₁ (pCoreOf 2 H) (DihedralGroup p)
  dihedral₂ : SecIso H₂ (pCoreOf 2 H) (DihedralGroup p)
  t_mem : t ∈ T
  t_not : t ∉ Subgroup.normalizer (H₁ : Set G)
  conj : H₂ = conjSub t H₁
  dir_inf : uHi T M H H₁ ⊓ uHi T M H H₂ = quasithinOmegaOneCenter T
  dir_sup : uHi T M H H₁ ⊔ uHi T M H H₂ = uK T M H ⊔ quasithinOmegaOneCenter T
  cent₁ : ⁅uHi T M H H₁, H₂⁆ ≤ quasithinOmegaOneCenter T
  cent₂ : ⁅uHi T M H H₂, H₁⁆ ≤ quasithinOmegaOneCenter T
  rank₁ : (p = 5 → mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4) ∧
    (p = 3 → mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 ∨
      mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4)
  rank₂ : (p = 5 → mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 4) ∧
    (p = 3 → mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 2 ∨
      mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 4)

@[expose] def IsOFourPlusOn (T M H : Subgroup G) : Prop :=
  IsOFourPlusAction (tildeOf (quasithinOmegaOneCenter T) H)
      (tildeOf (quasithinOmegaOneCenter T) (uK T M H)) ∧
    centralizerMod (quasithinOmegaOneCenter T) H (uK T M H) = pCoreOf 2 H

end Defs

@[expose] def Stage14612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      (p = 3 ∨ p = 5) ∧ (∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDec12 T M H p H₀ H₁ H₂ t) ∧
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
          quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ∧
            quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper H₂⁆

@[expose] def Stage14613 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∃ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t ∧
        ((p = 3 ∧ IsOFourPlusOn T M H ∧ ∃ g : G, g ∉ mcOf T ∧
            ¬ ⁅uHi T M H H₁, conjSub g⁻¹ (conjClosure (VZ T M) H)⁆ ≤ quasithinOmegaOneCenter T ∧
            conjSub g⁻¹ (conjClosure (VZ T M) H) ≤ H ⊓ Subgroup.normalizer (uHi T M H H₁ : Set G) ∧
            conjClosure (VZ T M) H ≤ conjSub g⁻¹ H) ∨
          ((p = 3 ∨ p = 5) ∧ mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8 ∧
            ∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
              F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
              F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
                F8.Uγ (VZ T M) H (g : G) ∧
              F8.Uγ (VZ T M) H (g : G) ≤ H₁ ∧
              F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁ ∧
              quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₁)))

@[expose] def Stage14614 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      (conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H ∧
          (p = 3 → ∀ r : ℕ, r.Prime → r ∣ Nat.card (mcOf T) → r = 2 ∨ r = 3)) ∨
      (p = 3 ∧ conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T) ∧
          ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (OTwoQuot (mcOf T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) ∨
      (p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
          (Nonempty (OTwoQuot (mcOf T) ≃* (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) ∨
            Nonempty (OTwoQuot (mcOf T) ≃*
              (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2))))) ∨
      (p = 5 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
          mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
          (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 ∧
          Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))

@[expose] def Stage14615 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3

@[expose] def Stage14616 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (T ⊓ Subgroup.normalizer (H₁ : Set G)).relIndex T = 2 ∧
          Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T = T

@[expose] def Stage14617 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      IsOFourPlusOn T M H ∧
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
          (∀ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
              F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g →
              ¬ F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁) ∧
          (∀ u : G, u ∈ uK T M H → (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) →
              u ∉ quasithinOmegaOneCenter T →
              T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u → IsInvU T M H u) ∧
          (∀ u : G, u ∈ uK T M H → (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) →
              u ∉ quasithinOmegaOneCenter T →
              T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u →
              IsI T M u (Subgroup.centralizer ({u} : Set G))) ∧
          Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

@[expose] def Stage14611Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsOFourPlusOn T M H →
      4 < (pCoreOf 2 H).relIndex T ∧
        mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) = 4

end CFSG.Quasithin
