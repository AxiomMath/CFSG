module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22CasesNoN (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ((∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs) ∨
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ 8 < autCard Ts Ks))) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs) ∨
      (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
        IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧
        8 < autCard Ts Ks) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)))))

@[expose] def E22StatementNoN : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H →
    (∃ K : Subgroup Γ, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E22CasesNoN H T M K) ∧
    SQTKGroup (StarQuot M H)

end E2

end CFSG.Quasithin
