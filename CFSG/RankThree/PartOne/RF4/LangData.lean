module

public import CFSG.RankThree.PartOne.RF4.Closure
public import CFSG.RankThree.PartOne.RF4.Regularity
public import CFSG.RankThree.PartOne.RF4.Independence
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups


theorem reeF4_lang_data {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {a b p : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hbp : (2 * b + 1) * p = 2 * a + 1) :
    ∃ S₀ : MulAut (adjointGroup Tag.F4 L),
      (∀ m, ∃ h, m = h⁻¹ * S₀ h) ∧
      (∀ u, S₀ (adjointBaseChangeHom Tag.F4 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.F4 (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ (2 * b + 1)) u)) ∧
      (∀ u, (S₀ ^ p) (adjointBaseChangeHom Tag.F4 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.F4 (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ (2 * a + 1)) u)) ∧
      ∃ Frq : L →+* L, (∀ c, Frq c = c ^ Nat.card K) ∧
        ∀ y, (((S₀ ^ p) ((S₀ ^ p) y) : adjointGroup Tag.F4 L) : ModGL Tag.F4 L) =
          Units.map (entrywiseHom Frq) (y : ModGL Tag.F4 L) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hL2 : CharP L ReeTag.F4.prime :=
    charP_of_injective_algebraMap (algebraMap K L).injective ReeTag.F4.prime
  have : CharP L 2 := hL2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) L := by
    have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    have : IsScalarTower (ZMod 2) K L := IsScalarTower.of_algebraMap_eq fun c =>
      (RingHom.ext_zmod (algebraMap (ZMod 2) L) ((algebraMap K L).comp
        (algebraMap (ZMod 2) K))) ▸ rfl
    have : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
    exact Algebra.IsAlgebraic.trans (ZMod 2) K L
  obtain ⟨Φ, hΦ⟩ := exists_reeClosureAut (L := L)
  obtain ⟨⟨Fr, hFr⟩, -⟩ := (exceptional_Lang_root_coordinate_surjectivity 2 L).1 Tag.F4 1 le_rfl
  have hli := linearIndependent_pinnedE_tangentH_F4 (F := L)
  have hLang : ∀ m, ∃ h, m = h⁻¹ * (Φ * Fr ^ b) h := fun m =>
    ree_lang_exceptional (t := ReeTag.F4) hΦ hli Fr hFr b m
  have hFrtw : ∀ y, Fr y = frobeniusTwist Tag.F4 L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (hFr y)
  have hΦΦ : Φ * Φ = Fr := MulEquiv.ext fun y => by
    rw [MulAut.mul_apply, hFrtw]
    exact DFunLike.congr_fun hΦ.comp_self y
  have hS₀pow : Φ * Fr ^ b = Φ ^ (2 * b + 1) := by
    rw [← hΦΦ, ← sq, ← pow_mul, ← pow_succ']
  have hS₀p : (Φ * Fr ^ b) ^ p = Φ ^ (2 * a + 1) := by rw [hS₀pow, ← pow_mul, hbp]
  have hΦnι : ∀ (n : ℕ) (u : adjointGroup Tag.F4 K),
      (Φ ^ n) (adjointBaseChangeHom Tag.F4 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.F4 (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ n) u) := fun n u =>
    hΦ.map_baseChange_pow (algebraMap K L) n u
  refine ⟨Φ * Fr ^ b, hLang, fun u => by rw [hS₀pow, hΦnι], fun u => by rw [hS₀p, hΦnι],
    iterateFrobenius L 2 (2 * a + 1), fun c => by rw [iterateFrobenius_def, hK], fun y => ?_⟩
  rw [← MulAut.mul_apply, hS₀p, ← pow_add, show 2 * a + 1 + (2 * a + 1) = 2 * (2 * a + 1) by
    ring, pow_mul, sq, hΦΦ]
  exact coe_pow_apply_of_entrywise_frobenius 2 Fr hFr _ y

end CFSG.RankThree.PartOne.RF4
