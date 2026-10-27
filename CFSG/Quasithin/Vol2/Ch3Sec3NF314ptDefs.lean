module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative commutatorElement

structure Cfg (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) : Prop where
  nf : NFConfig G T M L D H K
  site : Site3314pt G T M L D H
  inner : InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K

structure FCfg (G : Type) [Group G] [Finite G] (T M L D H K TL L2 : Subgroup G) (e : G) :
    Prop where
  nf : NFConfig G T M L D H K
  TL_le : TL ≤ T
  TL_idx : Nat.card T ≤ 2 * Nat.card TL
  e_T : e ∈ T
  e_ne : e ≠ 1
  e_sq : e ^ 2 = 1
  K0_e : conjClosure K T ≤ Subgroup.centralizer ({e} : Set G)
  T_e : T ⊓ Subgroup.centralizer ({e} : Set G) = TL
  L2_e : L2 ≤ Subgroup.centralizer ({e} : Set G)
  L2_notM : ¬ L2 ≤ Subgroup.normalizer (conjClosure K T : Set G)

@[expose] def LeafYO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), NFConfig G T M L D H K →
    InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K →
    ⁅pCoreOf 2 (oTwoUpper H), oTwoUpper H⁆ ≤ pCoreOf 2 (conjClosure K T)

@[expose] def LeafVY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Cfg G T M L D H K →
    vPlus L T = ⁅vPlus L T, oTwoUpper H⁆

@[expose] def LeafYsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Cfg G T M L D H K →
    ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      ∃ y ∈ oTwoUpper H, Odd (orderOf y) ∧ y ^ 3 = 1 ∧
        y ∈ Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) ∧
        y ∉ Subgroup.centralizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G)

@[expose] def LeafS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), NFConfig G T M L D H K →
    ∀ e : G, e ∈ pCoreOf 2 (conjClosure K T ⊔ T) → e ^ 2 = 1 →
      (∀ x ∈ pCoreOf 2 (conjClosure K T ⊔ T), x * e = e * x) →
      conjClosure K T ≤ Subgroup.centralizer ({e} : Set G)

@[expose] def LeafF2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K TL L2 : Subgroup G) (e : G),
    FCfg G T M L D H K TL L2 e →
    (∃ g : G, g⁻¹ * e * g ∈ quasithinOmegaOneCenter T) → False

@[expose] def LeafF3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K TL L2 : Subgroup G) (e : G),
    FCfg G T M L D H K TL L2 e →
    quasithinIsLocal TL L2 → TL ≤ Subgroup.normalizer (L2 : Set G) →
    IsPSL 3 2 1 (↥L2 ⧸ CFSG.pCore 2 ↥L2) →
    (⁅conjClosure K T, L2⁆ ≤ pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) → False) →
    (¬ ∃ g : G, g⁻¹ * e * g ∈ quasithinOmegaOneCenter T) → False

@[expose] def LeafA312 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (B₁ B₂ J : Subgroup Q) (q : ℕ), q.Prime →
    (q % 24 = 11 ∨ q % 24 = 13) → IsPSL 3 2 1 (↥B₁ ⧸ CFSG.pCore 2 ↥B₁) →
    IsPSL 2 q 1 (↥B₂ ⧸ CFSG.pCore 2 ↥B₂) → B₁ ≤ J → B₂ ≤ J →
    (B₁ = J ∨ A312Case B₁ J ∨ A312Nonquasi B₁ J) →
    (B₂ = J ∨ A312Case B₂ J ∨ A312Nonquasi B₂ J) → False

end CFSG.Quasithin.H13.NF314pt
