module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Set

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups

@[expose] noncomputable def radE0 (F : Type) [Field F] : Subgroup ↥(StatedSL 3 F) :=
  ((leviHom F).ker.map (stabE0 F).subtype).map
    (specialLinearGroupEquivStatedSL 3 F).toMonoidHom

@[expose] def Step4314 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G)
    (m : ℕ) (F : Type) [Field F] [Fintype F] (α : ↥K →* ↥(StatedSL 3 F))
    (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F))
    (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G) (KZ : Subgroup G),
    Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y →
    KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)) →
    Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G) → K₂ ≤ KZ →
    KZ ≤ Subgroup.centralizer (ZS : Set G) →
      Subgroup.normalizer (R₂ : Set G) ≤ H ⊓ Subgroup.normalizer (K₂ : Set G) ∧
      R₂ = pCoreOf 2 ((KZ ⊔ T) ⊓ Subgroup.normalizer (R₂ : Set G)) ∧
      pCoreOf 2 (KZ ⊔ T) ≤ R₂ ∧
      R₂ = ((radE0 F).comap α).map K.subtype

@[expose] def Insp4316 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → A23List ↥S → Subgroup.centralizer (S : Set X) = ⊥ →
    ∀ (n : ℕ) (F : Type) [Field F] [Fintype F], 2 ≤ n → Fintype.card F = 2 ^ n →
    ∀ (R K : Subgroup X), R ≠ ⊥ → IsPGroup 2 ↥R → K ≤ S → ⁅K, K⁆ = K →
      K ≤ Subgroup.normalizer (R : Set X) →
      Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X) →
      (∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
        CFSG.Open.pRank p S ≤ 1 ∨
          (p = 3 ∧ ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
            IsPSLEps3q s q ↥S)) →
      pCoreOf 2 K ≤ R →
      ∀ x : X, x ^ (2 ^ n - 1) = 1 → x ∈ Subgroup.normalizer (R : Set X) →
        (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) →
        R ≤ ⁅R, Subgroup.zpowers x⁆ ⊔ pCoreOf 2 K →
        (n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)) ∨
          (x = 1 ∧ (n = 2 → ¬ (IsElemAbelian 2 R ∧ Nat.card ↥R = 2 ^ 4 ∧
            ∀ R' : Subgroup X, R' ≤ R → K ≤ Subgroup.normalizer (R' : Set X) →
              R' = ⊥ ∨ R' = R)))

@[expose] def Step43L34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G)
    (m : ℕ) (F : Type) [Field F] [Fintype F] (α : ↥K →* ↥(StatedSL 3 F))
    (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F))
    (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G) (KZ : Subgroup G),
    Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y →
    KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)) →
    Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G) → K₂ ≤ KZ →
    KZ ≤ Subgroup.centralizer (ZS : Set G) → Fintype.card F = 4 → IsPSL 3 2 2 (ModO2 KZ) →
    Subgroup.normalizer (R₂ : Set G) ≤ H ⊓ Subgroup.normalizer (K₂ : Set G) →
    pCoreOf 2 (KZ ⊔ T) ≤ R₂ → R₂ = ((radE0 F).comap α).map K.subtype →
    A318Case2 (starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) →
      ∃ (Γ A B : Subgroup G) (α' : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
        (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
        Config43L34 G T M L n I H K t F ZS K₂ R₂ (Subgroup.zpowers y) KZ Γ A B α' P

end CFSG.Quasithin.H13.Ch4
