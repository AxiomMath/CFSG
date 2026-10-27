module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Matrix

section Vocab

variable {V : Type} [CommGroup V]

@[expose] def fixQuot (A : Subgroup (MulAut V)) (Z : Subgroup V) : Subgroup V where
  carrier := {v | ∀ a ∈ A, a v * v⁻¹ ∈ Z}
  one_mem' := fun a _ => by rw [map_one, one_mul, inv_one]; exact Z.one_mem
  mul_mem' := fun {x y} hx hy a ha => by
    have e : a (x * y) * (x * y)⁻¹ = a x * x⁻¹ * (a y * y⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    rw [e]
    exact Z.mul_mem (hx a ha) (hy a ha)
  inv_mem' := fun {x} hx a ha => by
    have e : a x⁻¹ * x⁻¹⁻¹ = (a x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv]
    rw [e]
    exact Z.inv_mem (hx a ha)

theorem mem_fixQuot {A : Subgroup (MulAut V)} {Z : Subgroup V} {v : V} :
    v ∈ fixQuot A Z ↔ ∀ a ∈ A, a v * v⁻¹ ∈ Z := Iff.rfl

end Vocab

section Omega5

variable (F : Type) [Field F]

@[expose] def sp4Quad (x : Fin 2 ⊕ Fin 2 → F) : F :=
  x (Sum.inl 0) * x (Sum.inr 0) + x (Sum.inl 1) * x (Sum.inr 1)

@[expose] def omega5Act (g : ↥(StatedSp 2 F)) (y : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)) :
    Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) :=
  Multiplicative.ofAdd
    ((((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        *ᵥ (Multiplicative.toAdd y).1),
      (Multiplicative.toAdd y).2 + sp4Quad F (Multiplicative.toAdd y).1 +
        sp4Quad F ((((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *ᵥ (Multiplicative.toAdd y).1))

@[expose] def omega5Rad : Subgroup (Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)) :=
  AddSubgroup.toSubgroup
    { carrier := {y | y.1 = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Prod.fst_add] at ha hb ⊢
        rw [ha, hb, add_zero]
      zero_mem' := rfl
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Prod.fst_neg] at ha ⊢
        rw [ha, neg_zero] }

@[expose] def FFModel.omega5 (Z : Subgroup (Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F))) :
    FFModel where
  Gam := ↥(StatedSp 2 F)
  Amb := Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)
  act := omega5Act F
  sec := ⊤
  ker := Z

end Omega5

@[expose] def zornWeylQuot {F : Type} [Field F]
    (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F))
    (Z : Subgroup (Multiplicative (quasithinZorn F))) : FFModel where
  Gam := ↥Γ
  Amb := Multiplicative (quasithinZorn F)
  act := zornAct Γ
  sec := zornO0 F
  ker := Z

section Statement

variable {V : Type} [CommGroup V] [Finite V]

structure MS15Hyp (X K : Subgroup (MulAut V)) : Prop where
  le : K ≤ X
  le_normalizer : X ≤ Subgroup.normalizer (K : Set (MulAut V))
  quasisimple : CFSG.IsQuasisimple ↥K
  sqtk : SQTKGroup ↥K
  rankTwo : IsRankTwoLie2Derived (↥K ⧸ Subgroup.center ↥K)
  cent : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1
  two : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K
  comm : commV K = ⊤
  fix_ne : fixV K ≠ ⊥
  irr : XMod.IsIrrSec ↥K (fixV K) ⊤
  ff : ∃ A : Subgroup (MulAut V), A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K))

@[expose] def MS15CaseL3 (X K : Subgroup (MulAut V)) : Prop :=
  X = K ∧ BinaryNaturalSL K ⊤ (fixV K) 3 1 ∧
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (↥K ≃* ↥(StatedSL 3 F))) ∧
    Nat.card (fixV X) = 2 ∧
    ∀ S : Subgroup (MulAut V), IsSylowTwoOf S X →
      (∀ t ∈ S, t ≠ 1 → fixV X ≤ commV (Subgroup.zpowers t)) ∧
      ∀ Y : Subgroup (MulAut V), Y ≤ S →
        2 * Nat.card (fixV K) < Nat.card ↥(commV Y ⊔ fixV K) → fixV Y = fixV X

@[expose] def MS15CaseSp4 (K : Subgroup (MulAut V)) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSp4 K ⊤ (fixV K) n ∧ Nat.card (fixV K) ≤ 2 ^ n ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ Z ≤ omega5Rad F, (FFModel.omega5 F Z).Realizes K ⊤ ⊥) ∨
  (AlternatingNatural K ⊤ (fixV K) 6 ∧ Nat.card (fixV K) = 2 ∧ Nat.card V = 2 ^ 5 ∧
    (H13.altCoreModel 6).Realizes K ⊤ ⊥)

@[expose] def MS15CaseG2 (X K : Subgroup (MulAut V)) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ G2Natural K ⊤ (fixV K) n ∧ Nat.card (fixV K) ≤ 2 ^ n ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ Z ≤ zornR F, (zornWeylQuot (quasithinG2 F) Z).Realizes K ⊤ ⊥) ∨
  (G2NaturalDerived K ⊤ (fixV K) 1 ∧ X ≠ K ∧ G2Natural X ⊤ (fixV K) 1 ∧
    Nat.card (fixV K) = 2 ∧ Nat.card V = 2 ^ 7 ∧ H13.G2WeylDerived K)

@[expose] def MS15Conclusion (X K : Subgroup (MulAut V)) : Prop :=
  MS15CaseL3 X K ∨ MS15CaseSp4 K ∨ MS15CaseG2 X K

end Statement

@[expose] def MS15AS : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X K : Subgroup (MulAut V), MS15Hyp X K → MS15Conclusion X K

@[expose] def MS15G2Comm : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X K : Subgroup (MulAut V), MS15Hyp X K → MS15CaseG2 X K →
      ∀ A : Subgroup (MulAut V), A ≤ X → A ≠ ⊥ → IsElemAbelian2 A →
        Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K)) →
          ∀ v : V, (v ∈ fixV K ∧ v ≠ 1) ↔ (v ∈ commV A ∧ ∀ a ∈ A, ∀ w : V, a w * w⁻¹ ≠ v)

end CFSG.Quasithin.MS93
