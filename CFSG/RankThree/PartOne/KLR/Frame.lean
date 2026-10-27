module

public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.RankThree.PartOne.RF4.Closure
public import CFSG.RankThree.PartOne.RF4.Independence
public import CFSG.RankThree.PartOne.RF4.Regularity

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4

variable {L : Type} [Field L]

@[expose] def IsReeFrob (a : ℕ) (F : MulAut (adjointGroup ReeTag.F4.tag L)) : Prop :=
  ∀ (i : Fin ReeTag.F4.tag.rank) (c : L),
    F (xElement i c) = xElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a i) ∧
    F (yElement i c) = yElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a i)

theorem isReeFrob_of_exceptional {Φ Fr : MulAut (adjointGroup ReeTag.F4.tag L)} [CharP L 2]
    (hΦ : IsReeExceptional ReeTag.F4 L Φ)
    (hFr : ∀ y, Fr y = frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 1) y) (a : ℕ) :
    IsReeFrob a (Φ * Fr ^ a) := by
  have hx : ∀ (n : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : L),
      (Fr ^ n) (xElement i c) = xElement i (c ^ 2 ^ n) ∧
        (Fr ^ n) (yElement i c) = yElement i (c ^ 2 ^ n) := by
    intro n
    induction n with
    | zero => intro i c; simp
    | succ n ih =>
      intro i c
      rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply, (ih i c).1, (ih i c).2, hFr, hFr,
        frobeniusTwist_xElement, frobeniusTwist_yElement, iterateFrobenius_def]
      have : (c ^ 2 ^ n) ^ 2 ^ 1 = c ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_one, pow_succ]
      rw [this]
      exact ⟨rfl, rfl⟩
  intro i c
  have hexp : ReeTag.F4.relationExponent a i = 2 ^ a * ReeTag.F4.exponent i :=
    (ReeTag.relationExponent_eq ReeTag.F4 a i).symm.symm
  rw [MulAut.mul_apply, MulAut.mul_apply, (hx a i c).1, (hx a i c).2, (hΦ i _).1, (hΦ i _).2, hexp,
    ← pow_mul]
  exact ⟨rfl, rfl⟩

theorem reeFrame_exists {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ F : MulAut (adjointGroup ReeTag.F4.tag L), IsReeFrob a F ∧ (∀ m, ∃ h, m = h⁻¹ * F h) ∧
      (∀ u, F (adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) u) =
        adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ (2 * a + 1)) u)) ∧
      ∃ Frq : L →+* L, (∀ c, Frq c = c ^ Nat.card K) ∧
        ∀ y, ((F (F y) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
          Units.map (entrywiseHom Frq) (y : ModGL ReeTag.F4.tag L) := by
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
  have hLang : ∀ m, ∃ h, m = h⁻¹ * (Φ * Fr ^ a) h := fun m =>
    ree_lang_exceptional (t := ReeTag.F4) hΦ hli Fr hFr a m
  have hFrtw : ∀ y, Fr y = frobeniusTwist Tag.F4 L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (hFr y)
  have hΦΦ : Φ * Φ = Fr := MulEquiv.ext fun y => by
    rw [MulAut.mul_apply, hFrtw]
    exact DFunLike.congr_fun hΦ.comp_self y
  have hS₀pow : Φ * Fr ^ a = Φ ^ (2 * a + 1) := by
    rw [← hΦΦ, ← sq, ← pow_mul, ← pow_succ']
  have hΦnι : ∀ (n : ℕ) (u : adjointGroup Tag.F4 K),
      (Φ ^ n) (adjointBaseChangeHom Tag.F4 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.F4 (algebraMap K L)
          ((ReeTag.F4.finiteExceptionalAut K ^ n) u) := fun n u =>
    hΦ.map_baseChange_pow (algebraMap K L) n u
  have hsq : ∀ y : adjointGroup Tag.F4 L,
      (((Φ * Fr ^ a) ((Φ * Fr ^ a) y) : adjointGroup Tag.F4 L) : ModGL Tag.F4 L) =
        Units.map (entrywiseHom (iterateFrobenius L 2 (2 * a + 1))) (y : ModGL Tag.F4 L) :=
    fun y => by
      rw [← MulAut.mul_apply, hS₀pow, ← pow_add, show 2 * a + 1 + (2 * a + 1) = 2 * (2 * a + 1) by
        ring, pow_mul, sq, hΦΦ]
      exact coe_pow_apply_of_entrywise_frobenius 2 Fr hFr _ y
  exact ⟨Φ * Fr ^ a, isReeFrob_of_exceptional hΦ hFrtw a, hLang,
    fun u => by rw [hS₀pow]; exact hΦnι _ u,
    iterateFrobenius L 2 (2 * a + 1), fun c => by rw [iterateFrobenius_def, hK], hsq⟩

end CFSG.RankThree.PartOne.KLR
