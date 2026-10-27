module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.U4Blk

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.LocalCores
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G]

@[expose] def StdTriangle (f₀ : ℕ) (K : Subgroup G) (J : Fin 3 → Fin 3 → Subgroup G)
    (BK : Subgroup G) : Prop :=
  ∃ (Kq : Type) (_ : Field Kq) (h : UnitaryFieldData 2 f₀ Kq)
    (φ : ↥K ≃* ↥(unitarySU 2 f₀ Kq 3)),
    (∀ (a b : Fin 3) (hab : a ≠ b), J a b ≤ K ∧ ∀ x : ↥K, (x : G) ∈ J a b ↔
      ((φ x : ↥(unitarySU 2 f₀ Kq 3)) : GL (Fin 3) Kq) ∈ blk h hab) ∧
    BK ≤ K ∧ ∀ x : ↥K, (x : G) ∈ BK ↔
      ((φ x : ↥(unitarySU 2 f₀ Kq 3)) : GL (Fin 3) Kq) ∈ torusSU 5 3 Kq

@[expose] def pairLayer (I BK Jab : Subgroup G) : Subgroup G :=
  inSubgroup perfectResidual
    (I ⊓ Subgroup.centralizer ((BK ⊓ Subgroup.centralizer (Jab : Set G) : Subgroup G) : Set G))

structure IConfig (c : G) (f₀ : ℕ) (I K BK : Subgroup G) (J : Fin 3 → Fin 3 → Subgroup G) :
    Prop where
  f_two : 2 ≤ f₀
  dvd5 : 5 ∣ 2 ^ f₀ + 1
  ndvd25 : ¬ 25 ∣ 2 ^ f₀ + 1
  model : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 3 2 (5 * f₀)
  perfect : Group.IsPerfect I
  c_norm : c ∈ Subgroup.normalizer (I : Set G)
  c_pow : c ^ 5 = 1
  c_outer : c ∉ I ⊔ Subgroup.centralizer (I : Set G)
  K_eq : K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))
  K_le : K ≤ I
  triangle : StdTriangle f₀ K J BK

structure IFacts (c : G) (f₀ : ℕ) (I K BK : Subgroup G) (J : Fin 3 → Fin 3 → Subgroup G) :
    Prop where
  I_model : StatedClassicalModel I .PSU 3 2 (5 * f₀)
  K_perfect : Group.IsPerfect K
  K_ne_bot : K ≠ ⊥
  J_le_K : ∀ a b : Fin 3, a ≠ b → J a b ≤ K
  M_model : ∀ a b : Fin 3, a ≠ b →
    StatedClassicalModel ↥(pairLayer I BK (J a b)) .PSL 2 2 (5 * f₀)
  M_quasi : ∀ a b : Fin 3, a ≠ b → CFSG.IsQuasisimple ↥(pairLayer I BK (J a b))
  J_le_M : ∀ a b : Fin 3, a ≠ b → J a b ≤ pairLayer I BK (J a b)
  M_le : ∀ a b : Fin 3, a ≠ b → pairLayer I BK (J a b) ≤ I
  c_norm_M : ∀ a b : Fin 3, a ≠ b → c ∈ Subgroup.normalizer (pairLayer I BK (J a b) : Set G)
  c_outer_M : ∀ a b : Fin 3, a ≠ b →
    c ∉ pairLayer I BK (J a b) ⊔ Subgroup.centralizer (pairLayer I BK (J a b) : Set G)
  M_sup : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
    pairLayer I BK (J a b) ⊔ pairLayer I BK (J a d) = I
  K_sup_M : ∀ a b : Fin 3, a ≠ b → K ⊔ pairLayer I BK (J a b) = I
  generation : ∀ a b : Fin 3, a ≠ b → ∃ x t : G, x ∈ pairLayer I BK (J a b) ∧ orderOf x = 25 ∧
    Subgroup.zpowers (x ^ 5) = BK ⊓ J a b ∧ t ∈ J a b ∧ orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ ∧
    pairLayer I BK (J a b) = J a b ⊔ Subgroup.zpowers x
  inv_centralizes : ∀ t : G, t ∈ Subgroup.normalizer (I : Set G) → t ^ 2 = 1 →
    (∀ k ∈ K, t * k = k * t) → ∀ u ∈ I, t * u = u * t

@[expose] def IStd (hGA : Prop) : Prop :=
  hGA → ∀ (G : Type) [Group G] [Finite G] (c : G) (f₀ : ℕ) (I K BK : Subgroup G)
    (J : Fin 3 → Fin 3 → Subgroup G), IConfig c f₀ I K BK J → IFacts c f₀ I K BK J

end CFSG.RankThree.PartOne.CTP
