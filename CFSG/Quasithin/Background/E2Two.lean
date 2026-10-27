module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

instance kerIn_subgroupOf_normal (M H : Subgroup Γ) : ((kerIn M H).subgroupOf H).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H g.2) _).mp hn

abbrev StarQuot (M H : Subgroup Γ) : Type := ↥H ⧸ (kerIn M H).subgroupOf H

@[expose] def star (M H X : Subgroup Γ) : Subgroup (StarQuot M H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H))

@[expose] def IsBorelIn {Y : Type} [Group Y] (X B : Subgroup Y) : Prop :=
  ∃ S : Subgroup Y, IsSylowTwoOf S X ∧ B = X ⊓ Subgroup.normalizer (S : Set Y)

@[expose] noncomputable def autCard {Y : Type} [Group Y] (X K : Subgroup Y) : ℕ :=
  ((X ⊓ Subgroup.normalizer (K : Set Y)) ⊓ Subgroup.centralizer (K : Set Y)).relIndex
    (X ⊓ Subgroup.normalizer (K : Set Y))

@[expose] def IsDiagramNontrivial {Y : Type} [Group Y] (X L S : Subgroup Y) : Prop :=
  ∀ P : Subgroup Y, IsMaxParabolic2 L P → L ⊓ Subgroup.normalizer (S : Set Y) ≤ P →
    ¬ X ≤ Subgroup.normalizer (P : Set Y)

@[expose] def InducesOuter {Y : Type} [Group Y] (X K : Subgroup Y) : Prop :=
  ∃ x ∈ X, x ∈ Subgroup.normalizer (K : Set Y) ∧
    ∀ k ∈ K, ∃ y ∈ K, x * y * x⁻¹ ≠ k * y * k⁻¹

@[expose] def IsSp4Prime (n : ℕ) (X : Type) [Group X] : Prop :=
  if n = 1 then IsAlt 6 X else IsPSp4 2 n X

@[expose] def IsBenderOf (n : ℕ) (X : Type) [Group X] : Prop :=
  2 ≤ n ∧ (IsPSL 2 2 n X ∨ IsSz n X ∨ IsPSU 3 2 n X)

@[expose] def E22Cases (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ((∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs ∧
        E1.nParam H = n) ∨
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ 8 < autCard Ts Ks ∧
        E1.nParam H = 1))) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs ∧ E1.nParam H = n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs ∧ E1.nParam H = n) ∨
      (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
        IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧
        8 < autCard Ts Ks ∧ E1.nParam H = 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ E1.nParam H = 1)))

@[expose] def E22Statement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H →
    (∃ K : Subgroup Γ, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E22Cases H T M K) ∧
    SQTKGroup (StarQuot M H)

end E2

end CFSG.Quasithin
