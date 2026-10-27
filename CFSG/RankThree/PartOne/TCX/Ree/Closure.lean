module

public import CFSG.RankThree.PartOne.KLR.Embedding

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR

section Closure

variable (L : Type) [Field L] [CharP L 2]

structure ReeClosure where
  Φ : MulAut (adjointGroup ReeTag.F4.tag L)
  Fr : MulAut (adjointGroup ReeTag.F4.tag L)
  isExc : IsReeExceptional ReeTag.F4 L Φ
  fr_apply : ∀ y : adjointGroup ReeTag.F4.tag L,
    ((Fr y : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      Units.map (entrywiseHom (iterateFrobenius L 2 1)) (y : ModGL ReeTag.F4.tag L)
  sq : Φ * Φ = Fr

variable {L}

theorem exists_reeClosure {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L]
    [IsAlgClosure K L] : Nonempty (ReeClosure L) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
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
  have hFrtw : ∀ y, Fr y = frobeniusTwist Tag.F4 L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (hFr y)
  have hΦΦ : Φ * Φ = Fr := MulEquiv.ext fun y => by
    rw [MulAut.mul_apply, hFrtw]
    exact DFunLike.congr_fun hΦ.comp_self y
  exact ⟨⟨Φ, Fr, hΦ, hFr, hΦΦ⟩⟩

end Closure

section Frame

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem ReeClosure.exists_frame (C : ReeClosure L) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] [Algebra K L] [IsAlgClosure K L] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ D : ReeFrameData K L a, D.F = C.Φ ^ (2 * a + 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hli := linearIndependent_pinnedE_tangentH_F4 (F := L)
  have hFrtw : ∀ y, C.Fr y = frobeniusTwist Tag.F4 L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (C.fr_apply y)
  have hLang : ∀ m, ∃ h, m = h⁻¹ * (C.Φ * C.Fr ^ a) h := fun m =>
    ree_lang_exceptional (t := ReeTag.F4) C.isExc hli C.Fr C.fr_apply a m
  have hS₀pow : C.Φ * C.Fr ^ a = C.Φ ^ (2 * a + 1) := by
    rw [← C.sq, ← _root_.sq, ← pow_mul, ← pow_succ']
  have hΦnι : ∀ (n : ℕ) (u : adjointGroup ReeTag.F4.tag K),
      (C.Φ ^ n) (adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) u) =
        adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ n) u) := fun n u =>
    C.isExc.map_baseChange_pow (algebraMap K L) n u
  have hsq : ∀ y : adjointGroup ReeTag.F4.tag L,
      (((C.Φ * C.Fr ^ a) ((C.Φ * C.Fr ^ a) y) : adjointGroup ReeTag.F4.tag L) :
        ModGL ReeTag.F4.tag L) =
        Units.map (entrywiseHom (iterateFrobenius L 2 (2 * a + 1)))
          (y : ModGL ReeTag.F4.tag L) :=
    fun y => by
      rw [← MulAut.mul_apply, hS₀pow, ← pow_add, show 2 * a + 1 + (2 * a + 1) = 2 * (2 * a + 1) by
        ring, pow_mul, _root_.sq, C.sq]
      exact coe_pow_apply_of_entrywise_frobenius 2 C.Fr C.fr_apply _ y
  refine ⟨⟨C.Φ * C.Fr ^ a, isReeFrob_of_exceptional C.isExc hFrtw a, hLang,
    fun u => by rw [hS₀pow]; exact hΦnι _ u,
    iterateFrobenius L 2 (2 * a + 1), fun c => by rw [iterateFrobenius_def, hK], hsq⟩, hS₀pow⟩

end Frame

end CFSG.RankThree.PartOne.TCX.Ree
