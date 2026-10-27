module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsNatL2Section (K C W₁ W₀ : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ α : K →* Matrix.SpecialLinearGroup (Fin 2) F,
      α.ker = C.subgroupOf K ∧
      α.range = commutator (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ β : W₁ →* Multiplicative (Fin 2 → F),
        Function.Surjective β ∧ β.ker = W₀.subgroupOf W₁ ∧
        ∀ (k : K) (u v : W₁), (v : G) = k * u * k⁻¹ →
          Multiplicative.toAdd (β v) =
            (α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

@[expose] noncomputable def fstarAut (H V : Subgroup G) : Subgroup (MulAut ↥V) :=
  (CFSG.generalizedFitting ↥(autOn H V)).map (autOn H V).subtype

@[expose] noncomputable def fstarPre (H V : Subgroup G) : Subgroup G :=
  H ⊓ ((fstarAut H V).comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

@[expose] def HasNaturalFstar (H V : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    IsNatL2Section (fstarPre H V) (Subgroup.centralizer (V : Set G)) ⁅V, fstarPre H V⁆
      (⁅V, fstarPre H V⁆ ⊓ Subgroup.centralizer (fstarPre H V : Set G)) n

structure InClassG (H S : Subgroup G) : Prop where
  isSylow : IsSylowTwoOf S H
  charTwo : CharTwo H
  minParabolic : IsMinParabolicOf H H
  natural : HasNaturalFstar H (VZ S H)

@[expose] def IsL2OrA3Block (X L : Subgroup G) : Prop :=
  IsBlock2 X L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3)

@[expose] def IsC118Pair (S C₁ C₂ : Subgroup G) : Prop :=
  C₁ ≠ ⊥ ∧ C₁ ≤ omegaOneCenterOf S ∧ (C₁.subgroupOf S).Characteristic ∧
    C₂ ≠ ⊥ ∧ C₂ ≤ baum S ∧ (C₂.subgroupOf (baum S)).Characteristic ∧
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (H : Subgroup Ω) (ι : ↥(baum S) →* Ω),
      Function.Injective ι → InClassG H ι.range →
        (C₁.subgroupOf (baum S)).map ι ≤ centerOf H ∨
        H ≤ Subgroup.normalizer (((C₂.subgroupOf (baum S)).map ι : Subgroup Ω) : Set Ω) ∨
        IsL2OrA3Block H (twoResidual H)

@[expose] def TheoremC118 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω), IsPGroup 2 S → S ≠ ⊥ →
    ∃ C₁ C₂ : Subgroup Ω, IsC118Pair S C₁ C₂

end CFSG.Quasithin
