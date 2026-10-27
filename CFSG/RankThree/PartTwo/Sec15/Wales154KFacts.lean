module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def KS154A7E9 : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* alternatingGroup (Fin 7)) →
    ∀ K : Subgroup Q, 5 ∣ Nat.card K → ¬ 9 ∣ Nat.card K →
      ∀ E : Subgroup (MulAut Q), IsPGroup 3 E → 9 ≤ Nat.card E →
        (∀ e ∈ E, ∀ k ∈ K, e k ∈ K) → False

@[expose] def KS154A7Seven : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* alternatingGroup (Fin 7)) →
    ∀ K : Subgroup Q, 7 ∣ Nat.card K →
      ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
        (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) → P = ⊥

@[expose] def KS154A10Aut : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* alternatingGroup (Fin 10)) →
    ∀ K : Subgroup Q, 7 ∣ Nat.card K →
      ∀ E : Subgroup (MulAut Q), IsPGroup 3 E → 27 ≤ Nat.card E →
        (∀ e ∈ E, ∀ k ∈ K, e k ∈ K) →
        ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
          (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) →
          E ≤ Subgroup.normalizer (P : Set (MulAut Q)) → P = ⊥

@[expose] def KS1543A6 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) →
      ∀ K : Subgroup Q, K ≠ ⊥ → Group.IsPerfect K →
        ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
          (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) → P = ⊥

@[expose] def KS154M22A7 : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M22) →
    ∀ K : Subgroup Q, Group.IsPerfect K → 35 ∣ Nat.card K →
      ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
        (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) → P = ⊥

@[expose] def KS154U35A7 : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (Q : Type) [Group Q],
    Nonempty (Q ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1) →
    ∀ K : Subgroup Q, 7 ∣ Nat.card K →
      ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
        (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) → P = ⊥

@[expose] def KS154ONCore : Prop :=
  ∀ (Γ : Type) [Group Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.ON) →
    ∀ (V : Subgroup Γ) (g : Γ), Group.IsPerfect V → 5 ∣ Nat.card V → orderOf g = 3 →
      V ≤ Subgroup.centralizer ({g} : Set Γ) →
        ∀ P : Subgroup Γ, IsPGroup 2 P → V ≤ Subgroup.normalizer (P : Set Γ) →
          g ∈ Subgroup.normalizer (P : Set Γ) → P = ⊥

@[expose] def KS154ON : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON →
      ∀ K : Subgroup Q, Group.IsPerfect K → 5 ∣ Nat.card K →
        ∀ α : MulAut Q, orderOf α = 3 → (∀ k ∈ K, α k ∈ K) →
          (∀ k ∈ K, α k * k⁻¹ ∈ (CFSG.pCore 2 ↥K).map K.subtype) →
          ∀ P : Subgroup (MulAut Q), IsPGroup 2 P →
            (∀ k ∈ K, MulAut.conj k ∈ Subgroup.normalizer (P : Set (MulAut Q))) →
            α ∈ Subgroup.normalizer (P : Set (MulAut Q)) → P = ⊥

@[expose] def KL3a : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (f : ℕ), 1 ≤ f → IsLThreeEpsAt Q 2 f →
    ∀ Xb : Subgroup Q, Group.IsPerfect Xb → ∀ n : ℕ, 1 ≤ n →
      IsLThreeEpsAt (↥Xb ⧸ CFSG.pCore 2 ↥Xb) 2 n →
        CFSG.pCore 2 ↥Xb = ⊥ ∧
          ∀ P : Subgroup Q, IsPGroup 2 P → Xb ≤ Subgroup.normalizer (P : Set Q) → P = ⊥

@[expose] def KL3c : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (f n : ℕ), 1 ≤ f → 1 ≤ n → IsLThreeEpsAt Q 2 f →
    ∀ Xb : Subgroup Q, IsLThreeEpsAt ↥Xb 2 n →
      ∀ τ : MulAut Q, τ ∉ (MulAut.conj : Q →* MulAut Q).range → τ * τ = 1 →
        (∀ x ∈ Xb, τ x = x) →
          Nonempty (Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 f)) ∧ 2 * n ∣ f

end CFSG.RankThree.PartTwo.Sec15.Wales154
