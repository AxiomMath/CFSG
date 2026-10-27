module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def LieF2n (Q : Type) [Group Q] (n : ℕ) : Prop :=
  IsPSL 2 2 n (Q ⧸ Subgroup.center Q) ∨ IsPSL 3 2 n (Q ⧸ Subgroup.center Q) ∨
    IsPSU 3 2 n (Q ⧸ Subgroup.center Q) ∨ IsPSp4 2 n (Q ⧸ Subgroup.center Q) ∨
    IsG2 2 n (Q ⧸ Subgroup.center Q)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def X13820 (_ : Setting4 G T L V) : Subgroup G := by
  classical
  exact if IsHatA6 L then l1plus T L V else L₁Of L (fsuV1 T V)

@[expose] def Ctx13820 (S : Setting4 G T L V) (H K : Subgroup G) (n : ℕ) : Prop :=
  S.Hyp138 ∧ H ∈ S.Hz ∧ K ∈ cComp H ∧ H ≤ Subgroup.normalizer (K : Set G) ∧
    H = K ⊔ (S.L1 ⊔ T) ∧ 2 ≤ n ∧ LieF2n ↥(S.KSt H K) n

@[expose] def Case13820aHyp (S : Setting4 G T L V) (H K : Subgroup G) : Prop :=
  ¬ S.X13820 ≤ K ∧ (∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧
    H ≤ Subgroup.normalizer (S.X13820 : Set G) ∧
    ∃ t ∈ H, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧
      ∀ x ∈ S.X13820, t * x * t⁻¹ * x ∈ pCoreOf 2 S.X13820

@[expose] def Case13820bHyp (S : Setting4 G T L V) (H K : Subgroup G) : Prop :=
  (IsPSL 2 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
      IsPSL 3 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
      IsPSU 3 2 3 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) ∧
    ∃ t ∈ T ⊓ L, (∀ x ∈ S.X13820, t * x * t⁻¹ * x ∈ pCoreOf 2 S.X13820) ∧
      ∀ k ∈ K, ∃ y ∈ K, (t * k⁻¹) * y * (t * k⁻¹)⁻¹ * y⁻¹ ∉ pCoreOf 2 K

end Setting4

@[expose] def Fact13820Aut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V)
    (H K : Subgroup G) (n : ℕ), S.Ctx13820 H K n →
    (Group.IsSolvable ↥(K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) →
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G)) →
    S.Case13820aHyp H K ∨ S.Case13820bHyp H K

@[expose] def Case13820a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V)
    (H K : Subgroup G) (n : ℕ), S.Ctx13820 H K n → ¬ S.Case13820aHyp H K

@[expose] def Case13820bSL34U38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V)
    (H K : Subgroup G) (n : ℕ), S.Ctx13820 H K n → S.Case13820bHyp H K →
    ¬ IsPSL 2 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) → False

@[expose] def Case13820L24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V)
    (H K : Subgroup G) (n : ℕ), S.Ctx13820 H K n → S.Case13820bHyp H K →
    IsPSL 2 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) → False

end CFSG.Quasithin.H13.A6
