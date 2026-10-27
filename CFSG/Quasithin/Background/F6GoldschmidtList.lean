module

public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.Recognition.GoldschmidtTriple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace F6

@[expose] def IsAmalgamIso {D E : Type*} [Group D] [Group E] (H₁ H₂ : Subgroup D)
    (K₁ K₂ : Subgroup E) : Prop :=
  ∃ (φ₁ : ↥H₁ ≃* ↥K₁) (φ₂ : ↥H₂ ≃* ↥K₂),
    (∀ (x : D) (hx₁ : x ∈ H₁) (hx₂ : x ∈ H₂), (φ₁ ⟨x, hx₁⟩ : E) = φ₂ ⟨x, hx₂⟩) ∧
      ∀ (y : E) (hy₁ : y ∈ K₁) (hy₂ : y ∈ K₂), (φ₁.symm ⟨y, hy₁⟩ : D) = φ₂.symm ⟨y, hy₂⟩

@[expose] def IsTwoLocalAmalgam {W : Type*} [Group W] (K₁ K₂ : Subgroup W) : Prop :=
  quasithinIsMaxTwoLocal K₁ ∧ quasithinIsMaxTwoLocal K₂ ∧ K₁ ≠ K₂ ∧
    ∃ S : Sylow 2 W, (S : Subgroup W) = K₁ ⊓ K₂

@[expose] def IsYAmalgam (IsY : ∀ (W : Type) [Group W], Prop) {D : Type*} [Group D]
    (H₁ H₂ : Subgroup D) : Prop :=
  ∃ (W : Type) (_ : Group W) (_ : Finite W) (K₁ K₂ : Subgroup W),
    IsY W ∧ IsTwoLocalAmalgam K₁ K₂ ∧ IsAmalgamIso H₁ H₂ K₁ K₂

@[expose] def IsL32 (W : Type) [Group W] : Prop := StatedClassicalModel W .PSL 3 2 1

@[expose] def IsSp42 (W : Type) [Group W] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
    Nonempty (W ≃* StatedProj (StatedSp 2 K))

@[expose] def IsG22 (W : Type) [Group W] : Prop :=
  CFSG.Blueprint.UntwistedChevalleyModel W CFSG.Blueprint.Chevalley.Tag.G2 2

@[expose] def IsG22Prime (W : Type) [Group W] : Prop :=
  ∃ (V : Type) (_ : Group V), IsG22 V ∧ Nonempty (W ≃* ↥(commutator V))

@[expose] def IsM12 (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* ↥CFSG.Blueprint.NativeSporadic.M12)

@[expose] def IsAutM12 (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12)

@[expose] def IsExtensionOf (X : Type*) [Group X] (A N : Type*) [Group A] [Group N] : Prop :=
  ∃ φ : X →* A, Function.Surjective φ ∧ Nonempty (↥φ.ker ≃* N)

@[expose] def IsCentralProduct₂ (R : Type*) [Group R] (A B : Type*) [Group A] [Group B] : Prop :=
  ∃ A' B' : Subgroup R, A' ⊔ B' = ⊤ ∧ (∀ a ∈ A', ∀ b ∈ B', a * b = b * a) ∧
    Nonempty (↥A' ≃* A) ∧ Nonempty (↥B' ≃* B) ∧ Nat.card ↥(A' ⊓ B') = 2

@[expose] def IsCentralProduct₃ (R : Type*) [Group R] (A B C : Type*) [Group A] [Group B]
    [Group C] : Prop :=
  ∃ A' B' C' : Subgroup R, A' ⊔ B' ⊔ C' = ⊤ ∧ (∀ a ∈ A', ∀ b ∈ B', a * b = b * a) ∧
    (∀ a ∈ A', ∀ c ∈ C', a * c = c * a) ∧ (∀ b ∈ B', ∀ c ∈ C', b * c = c * b) ∧
    Nonempty (↥A' ≃* A) ∧ Nonempty (↥B' ≃* B) ∧ Nonempty (↥C' ≃* C) ∧
    A' ⊓ C' = A' ⊓ B' ∧ B' ⊓ C' = A' ⊓ B' ∧ Nat.card ↥(A' ⊓ B') = 2

@[expose] def IsSpecialTwoOnePlusFour (R : Type*) [Group R] : Prop :=
  Nat.card R = 2 ^ 5 ∧ Nat.card ↥(Subgroup.center R) = 2 ∧
    commutator R = Subgroup.center R ∧ frattini R = Subgroup.center R

variable {D : Type*} [Group D]

@[expose] def F112Convention (H₁ H₂ : Subgroup D) : Prop :=
  (centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₁ : Set D) ∨
      centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₂ : Set D)) →
    centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₁ : Set D)

@[expose] def QuotientPCoreIsL22 (H : Subgroup D) : Prop :=
  Nonempty (↥H ⧸ Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))

@[expose] def IsGoldCaseI (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥H₁ ≃* Equiv.Perm (Fin 3)) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2)) ∧ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 3))

@[expose] def IsGoldCaseII (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥H₁ ≃* DihedralGroup 6) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    Nonempty (↥H₂ ≃* DihedralGroup 6)

@[expose] def IsGoldCaseIII (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥H₁ ≃* DihedralGroup 12) ∧ Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4))

@[expose] def IsGoldCaseIV (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥H₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) ∧
    IsExtensionOf ↥H₂ (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

@[expose] def IsGoldCaseV (H₁ H₂ : Subgroup D) : Prop :=
  Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) ∧
    Nonempty (↥H₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4)

@[expose] def IsGoldCaseL32 (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsL32 H₁ H₂ ∧ F112Convention H₁ H₂ ∧
    Nonempty (↥H₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 4))

@[expose] def IsGoldCaseSp42 (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsSp42 H₁ H₂ ∧ F112Convention H₁ H₂ ∧
    Nonempty (↥H₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
    Nonempty (↥H₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))

@[expose] def IsGoldCaseG22 (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsG22 H₁ H₂ ∧ F112Convention H₁ H₂ ∧ QuotientPCoreIsL22 H₁ ∧
    QuotientPCoreIsL22 H₂ ∧ IsSpecialTwoOnePlusFour ↥(pCoreOf 2 H₁) ∧
    Nat.card ↥(pCoreOf 2 H₂) = 2 ^ 5

@[expose] def IsGoldCaseG22Prime (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsG22Prime H₁ H₂ ∧ F112Convention H₁ H₂ ∧ QuotientPCoreIsL22 H₁ ∧
    QuotientPCoreIsL22 H₂ ∧
    IsCentralProduct₂ ↥(pCoreOf 2 H₁) (Multiplicative (ZMod 4)) (QuaternionGroup 2) ∧
    Nonempty (↥(pCoreOf 2 H₂) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

@[expose] def IsGoldCaseM12 (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsM12 H₁ H₂ ∧ F112Convention H₁ H₂ ∧ QuotientPCoreIsL22 H₁ ∧
    QuotientPCoreIsL22 H₂ ∧
    IsCentralProduct₂ ↥(pCoreOf 2 H₁) (QuaternionGroup 2) (QuaternionGroup 2) ∧
    Nat.card ↥(pCoreOf 2 H₂) = 2 ^ 5

@[expose] def IsGoldCaseAutM12 (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsAutM12 H₁ H₂ ∧ F112Convention H₁ H₂ ∧ QuotientPCoreIsL22 H₁ ∧
    QuotientPCoreIsL22 H₂ ∧
    IsCentralProduct₃ ↥(pCoreOf 2 H₁) (Multiplicative (ZMod 4)) (QuaternionGroup 2)
      (QuaternionGroup 2) ∧
    Nat.card ↥(pCoreOf 2 H₂) = 2 ^ 6

@[expose] def IsGoldCaseVI (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseL32 H₁ H₂ ∨ IsGoldCaseSp42 H₁ H₂ ∨ IsGoldCaseG22 H₁ H₂ ∨
    IsGoldCaseG22Prime H₁ H₂ ∨ IsGoldCaseM12 H₁ H₂ ∨ IsGoldCaseAutM12 H₁ H₂

@[expose] def IsGoldCaseOriented (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
    IsGoldCaseV H₁ H₂ ∨ IsGoldCaseVI H₁ H₂

@[expose] def IsGoldCase (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseOriented H₁ H₂ ∨ IsGoldCaseOriented H₂ H₁

theorem isGoldCase_comm {H₁ H₂ : Subgroup D} : IsGoldCase H₁ H₂ ↔ IsGoldCase H₂ H₁ :=
  or_comm

end F6

@[expose] def F6.GoldschmidtS3List : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    F6.IsGoldCase G₁ G₂

end CFSG.Quasithin
