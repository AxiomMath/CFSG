module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt
public import CFSG.Quasithin.Vol2.Ch3Sec3NFFacts
public import CFSG.Milestones.ASVolI.F7

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

section Notation

variable {G : Type} [Group G]

abbrev a2K0 (K T : Subgroup G) : Subgroup G := conjClosure K T

abbrev a2G1 (L T : Subgroup G) : Subgroup G := L ⊔ T

abbrev a2G2 (K T : Subgroup G) : Subgroup G := conjClosure K T ⊔ T

abbrev a2G0 (L K T : Subgroup G) : Subgroup G := (L ⊔ T) ⊔ (conjClosure K T ⊔ T)

abbrev a2TC (K T : Subgroup G) : Subgroup G := pCoreOf 2 (conjClosure K T ⊔ T)

abbrev a2N0 (K T : Subgroup G) : Subgroup G := pCoreOf 2 (conjClosure K T)

abbrev a2Q (L T : Subgroup G) : Subgroup G := pCoreOf 2 (L ⊔ T)

abbrev a2R (H : Subgroup G) : Subgroup G := pCoreOf 2 H

abbrev a2Z (T : Subgroup G) : Subgroup G := quasithinOmegaOneCenter T

abbrev a2V (L T : Subgroup G) : Subgroup G := vPlus L T

abbrev a2Vp (L T H : Subgroup G) : Subgroup G := ⁅vPlus L T, oTwoUpper H⁆

abbrev a2UH (L T H K : Subgroup G) : Subgroup G :=
  conjClosure ⁅vPlus L T, oTwoUpper H⁆ (conjClosure K T ⊔ T)

noncomputable abbrev a2Off (Z U S : Subgroup G) : ℕ := mIdx U (centralizerMod Z U S)

end Notation

structure A2Cfg (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ) : Prop where
  nf : NFConfig G T M L D H K
  site : Site3321a2 G T M L D H
  inner : InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K
  q_prime : q.Prime
  q_mod : q % 24 = 11 ∨ q % 24 = 13
  model : StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1

@[expose] def Leaf_G1 : Prop :=
  ∀ q : ℕ, q.Prime → (q % 24 = 11 ∨ q % 24 = 13) →
  ∀ (Kb : Type) [Group Kb], StatedClassicalModel Kb .PSL 2 q 1 →
  ∀ (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] (ρ : Kb →* (X ≃ₗ[ZMod 2] X)),
    (∃ k, ρ k ≠ 1) → 10 ≤ Module.finrank (ZMod 2) X

@[expose] def Leaf_G2 : Prop :=
  ∀ q : ℕ, q.Prime → (q % 24 = 11 ∨ q % 24 = 13) →
  ∀ (Kb : Type) [Group Kb], StatedClassicalModel Kb .PSL 2 q 1 →
  ∀ (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] (ρ : Kb →* (X ≃ₗ[ZMod 2] X)),
    (∀ x : X, (∀ k, ρ k x = x) → x = 0) → ∀ i : Kb, orderOf i = 2 →
      Module.finrank (ZMod 2) X ≤
        3 * Module.finrank (ZMod 2) (LinearMap.range ((ρ i).toLinearMap - LinearMap.id))

@[expose] def Leaf_G3 : Prop :=
  ∀ q : ℕ, q.Prime → (q % 24 = 11 ∨ q % 24 = 13) →
  ∀ (Kb : Type) [Group Kb], StatedClassicalModel Kb .PSL 2 q 1 →
  ∀ (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : (Kb × Kb) →* (X ≃ₗ[ZMod 2] X)),
    (∀ x : X, (∀ k, ρ k x = x) → x = 0) → ∀ i : Kb, orderOf i = 2 →
      Module.finrank (ZMod 2) X ≤
        4 * Module.finrank (ZMod 2) (LinearMap.range ((ρ (i, i)).toLinearMap - LinearMap.id))

@[expose] def Leaf_G4 : Prop :=
  ∀ q : ℕ, q.Prime → (q % 24 = 11 ∨ q % 24 = 13) →
  ∀ (Kb : Type) [Group Kb], StatedClassicalModel Kb .PSL 2 q 1 →
  ∀ (E F : Subgroup Kb) (a : Kb), Nat.card E = 12 → Nonempty (↥E ≃* DihedralGroup 6) →
    a ∈ E → (∀ e ∈ E, a * e = e * a) → orderOf a = 2 → E ≤ F → F ≠ ⊤ →
      F ≤ Subgroup.centralizer {a} ∧ ∀ z ∈ F, (∀ f ∈ F, z * f = f * z) → z = 1 ∨ z = a

@[expose] def Leaf_P9L2 : Prop :=
  ∀ q : ℕ, q.Prime → (q % 24 = 11 ∨ q % 24 = 13) → (9 : ℤ) ∣ (q : ℤ) - sgn4 q →
  ∀ (Kb : Type) [Group Kb], StatedClassicalModel Kb .PSL 2 q 1 →
  ∀ a : Kb, orderOf a = 2 →
    ∃ w : Kb, orderOf w = 9 ∧ a * w = w * a ∧
      ∀ x : Kb, orderOf x = 3 → a * x = x * a → x ∈ Subgroup.zpowers (w ^ 3)

structure CritPair {G : Type} [Group G] (G₀ G₁ G₂ V : Subgroup G) (g : ↥G₀) : Prop where
  critical : IsCriticalVertex G₀ G₁ G₂ V (g • γ₁ G₀ G₁ G₂)
  nbr : g • γ₁ G₀ G₁ G₂ ∈ nbrs (g • γ₀ G₀ G₁ G₂)
  geodesic : CosetGeom.dist (γ₁ G₀ G₁ G₂) (g • γ₀ G₀ G₁ G₂) + 2 = critDist G₀ G₁ G₂ V

section Concl

variable {G : Type} [Group G]

@[expose] def E1Concl (L K T : Subgroup G) : Prop :=
  coreIn (a2G1 L T ⊓ a2G2 K T) (a2G1 L T) = a2Q L T ∧
    coreIn (a2G1 L T ⊓ a2G2 K T) (a2G2 K T) = a2TC K T

@[expose] def E5aConcl (L K T H : Subgroup G) : Prop := ⁅a2UH L T H K, a2TC K T⁆ ≤ a2Z T

@[expose] def E5bConcl (L K T H : Subgroup G) : Prop :=
  centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) = a2TC K T

@[expose] def E5cConcl (L K T H : Subgroup G) : Prop :=
  a2G2 K T ⊓ Subgroup.centralizer (a2Vp L T H : Set G) ≤ Subgroup.centralizer (a2V L T : Set G)

@[expose] def E6iConcl (L K T H : Subgroup G) : Prop :=
  ∀ g : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g →
    ¬ ⁅conjSub (g : G) (a2UH L T H K), a2V L T⁆ ≤ conjSub (g : G) (a2Z T)

@[expose] def E6iiConcl (L K T : Subgroup G) : Prop :=
  ∀ g : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g →
    conjSub (g : G) (a2Z T) ≠ a2Z T

@[expose] noncomputable def E7Concl (L K T H : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ a2R H ∧ ¬ B ≤ a2TC K T ∧
    a2Off (a2Z T) (a2UH L T H K) B ≤ 2 * mIdx (B ⊔ a2TC K T) (a2TC K T)

end Concl

structure CaseAFacts (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ) : Prop where
  cfg : A2Cfg G T M L D H K q
  VTC : a2V L T ≤ a2TC K T
  amalgam : AmalgamHypV (a2G0 L K T) (a2G1 L T) (a2G2 K T) T (a2V L T)
  V_ne : a2V L T ≠ ⊥
  b_odd : Odd (critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T))
  b_three : 3 ≤ critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T)
  e1 : E1Concl L K T
  e5a : E5aConcl L K T H
  e5b : E5bConcl L K T H
  e5c : E5cConcl L K T H

@[expose] def Leaf_LS1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q → a2G1 L T ⊓ a2G2 K T = H

@[expose] def Leaf_LSCV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q →
      (L ⊔ T) ⊓ Subgroup.centralizer (a2V L T : Set G) ≤ pCoreOf 2 (L ⊔ T)

@[expose] def Leaf_C1 : Prop :=
  Leaf_G1 → Leaf_G3 →
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q →
      ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
        ∀ c ∈ a2R H, c ∉ a2TC K T ⊔ K → c ∉ a2TC K T ⊔ conjSub t K →
          5 ≤ mIdx (a2N0 K T) (a2N0 K T ⊓ Subgroup.centralizer ({c} : Set G))

@[expose] def Leaf_E5c : Prop :=
  Leaf_G1 → Leaf_G4 →
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q → E5cConcl L K T H

@[expose] def Leaf_E6ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    CaseAFacts G T M L D H K q → E6iiConcl L K T

@[expose] def Leaf_E7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    CaseAFacts G T M L D H K q → E6iConcl L K T H → E6iiConcl L K T → E7Concl L K T H

@[expose] def Leaf_KS1 : Prop :=
  Leaf_G1 → Leaf_G2 → Leaf_G3 →
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q → E5aConcl L K T H →
      ∀ c ∈ a2R H, c ∉ a2TC K T →
        3 ≤ a2Off (a2Z T) (a2UH L T H K) (Subgroup.zpowers c)

@[expose] def Leaf_KS2 : Prop :=
  Leaf_G1 → Leaf_G2 → Leaf_G3 →
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q → E5aConcl L K T H →
      5 ≤ a2Off (a2Z T) (a2UH L T H K) (a2R H)

end CFSG.Quasithin.H13.NFa2
