module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Ctx
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

structure Main513 (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G)
    (n : ℕ) : Prop where
  hyp : Hyp5_1_8 G T M L H n
  nota : IsNotation5_1_9 T M L H B D
  module : IsCh5Module T L V
  comp : quasithinIsCComponent K₁ H
  closure : oTwoUpper H = conjClosure K₁ T
  inH : InH H X
  hat : IsHatComp X K₁ Kh₁
  lt : oTwoUpper H < conjClosure Kh₁ T
  not_le : ¬ D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G)

theorem Main513.toEmb512 {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G}
    {n k : ℕ} (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hk : IsFieldParam510 T H k) :
    Emb512 G T M L H B D K₁ X Kh₁ n k :=
  ⟨m.hyp, m.nota, hk, m.comp, m.closure, m.inH, m.hat, m.lt⟩

section Vocabulary

variable {G : Type} [Group G]

@[expose] def Case5_512 (T H X Kh₁ : Subgroup G) : Prop :=
  LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
    ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
    A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T))

@[expose] def Type513 (T D X Kh K : Subgroup G) : Prop :=
  (Nonempty (O2Q Kh ≃* alternatingGroup (Fin 7)) ∨ Nonempty (O2Q Kh ≃* NativeSporadic.J2) ∨
      Nonempty (O2Q Kh ≃* NativeSporadic.M23)) ∧
    Kh = oThreePrimeResidual X ∧
    ∃ D₃ : Subgroup G, D₃ ≤ D ⊓ Kh ∧ Nat.card D₃ = 3 ∧
      ¬ D₃ ≤ Subgroup.normalizer (K : Set G) ∧ D ⊓ Kh ≤ D₃ ∧
      ∃ t ∈ T ⊓ Kh, ∀ d ∈ D₃, t * d * t⁻¹ = d⁻¹

end Vocabulary

@[expose] def Stmt5_1_13_c2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → K₁ < oTwoUpper H → LieModel (O2Q K₁) .PSL 2 2 2 →
    (IsSporadic .J1 (O2Q Kh₁) ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (O2Q Kh₁)) →
    False

@[expose] def Stmt5_1_13_type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
      Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H)

@[expose] def Stmt5_1_13_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
      conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Stmt5_1_13_mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    X = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      n = 2 ∧ IsA5ModuleSum L V

end CFSG.Quasithin.H13
