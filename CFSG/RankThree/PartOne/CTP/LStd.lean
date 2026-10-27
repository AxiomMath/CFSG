module

public import CFSG.RankThree.PartOne.CTP.IStd
public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

@[expose] def e3 : Fin 3 → Fin 5 := Fin.castLE (by omega)

structure LFam (L B : Subgroup G) (f₀ : ℕ) (b : G) (K : Subgroup G) where
  W : Equiv.Perm (Fin 5) →* G
  J : Fin 5 → Fin 5 → Subgroup G
  W_L : ∀ σ, W σ ∈ L
  W_B : ∀ σ, W σ ∈ Subgroup.normalizer (B : Set G)
  J_symm : ∀ a b, J a b = J b a
  J_equiv : ∀ σ a b, J (σ a) (σ b) = conjBy (W σ) (J a b)
  J_model : ∀ a b, a ≠ b → StatedClassicalModel ↥(J a b) .PSL 2 2 f₀
  B_elem : IsElementaryAbelian 5 B
  B_card : Nat.card B = 5 ^ 3
  line_card : ∀ a b, a ≠ b → Nat.card ↥(B ⊓ J a b) = 5
  hyper_ne : ∀ a b d e : Fin 5, a ≠ b → d ≠ e → ¬ ((a = d ∧ b = e) ∨ (a = e ∧ b = d)) →
    B ⊓ Subgroup.centralizer (J a b : Set G) ≠ B ⊓ Subgroup.centralizer (J d e : Set G)
  B_gen : B = (B ⊓ J 0 1) ⊔ (B ⊓ J 1 2) ⊔ (B ⊓ J 2 3) ⊔ (B ⊓ J 3 4)
  disj : ∀ a b d e : Fin 5, a ≠ b → d ≠ e → a ≠ d → a ≠ e → b ≠ d → b ≠ e →
    J a b ≤ Subgroup.centralizer (J d e : Set G)
  K_eq : K = J 0 1 ⊔ J 1 2
  b_mem : b ∈ B ⊓ J 3 4
  b_ne : b ≠ 1
  BK_card : Nat.card ↥(B ⊓ K) = 25
  hyper_eq : ∀ x y : Fin 3, x ≠ y →
    B ⊓ Subgroup.centralizer (J (e3 x) (e3 y) : Set G) =
      (B ⊓ K ⊓ Subgroup.centralizer (J (e3 x) (e3 y) : Set G)) ⊔ Subgroup.zpowers b
  std : StdTriangle f₀ K (fun a b => J (e3 a) (e3 b)) (B ⊓ K)

@[expose] def LStd (hGA h107 h109 : Prop) : Prop :=
  hGA → h107 → h109 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G 5 A c L E → ∀ f₀ : ℕ, 1 ≤ f₀ → 5 ∣ 2 ^ f₀ + 1 → ¬ 25 ∣ 2 ^ f₀ + 1 →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f₀ →
        ∀ (b : G) (K I : Subgroup G), Layer1212 5 A c L E b K I →
          Nonempty (LFam L (E ⊓ L) f₀ b K)

end CFSG.RankThree.PartOne.CTP
