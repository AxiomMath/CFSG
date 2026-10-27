module

public import CFSG.RankThree.PartOne.K133B.Defs

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327T
open scoped IsMulCommutative

theorem card_mulAut_dvd_480 {X : Type} [Group X] [Finite X] [IsElementaryAbelian 5 X]
    (hcard : Nat.card X = 5 ^ 2) : Nat.card (MulAut X) ∣ 480 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Module.Finite (ZMod 5) (Additive X) := Module.Finite.of_finite
  have : Fintype X := Fintype.ofFinite X
  have hfin : Module.finrank (ZMod 5) (Additive X) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 5) (V := Additive X)
    rw [ZMod.card] at h1
    have h2 : Fintype.card (Additive X) = 5 ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    exact Nat.pow_right_injective (a := 5) (by norm_num) (h1.symm.trans h2)
  let b := Module.finBasisOfFinrankEq (ZMod 5) (Additive X) hfin
  let toLin : MulAut X →* Module.End (ZMod 5) (Additive X) :=
    { toFun := fun f => (MonoidHom.toAdditive f.toMonoidHom).toZModLinearMap 5
      map_one' := by ext x; rfl
      map_mul' := by intro f g; ext x; rfl }
  let ι : MulAut X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
      (MonoidHom.toHomUnits toLin)
  have hι : Function.Injective ι := by
    intro f g hfg
    have h1 := (Units.map_injective (LinearMap.toMatrixAlgEquiv b).toRingEquiv.injective) hfg
    have h2 : toLin f = toLin g := by simpa using congrArg Units.val h1
    ext x
    have h3 := LinearMap.congr_fun h2 (Additive.ofMul x)
    exact h3
  have := Subgroup.card_dvd_of_injective ι hι
  rw [Matrix.card_GL_field, ZMod.card] at this
  simpa [Fin.prod_univ_two] using this

theorem oddOrderOneOrThree_of_five {X : Type} [Group X] [Finite X] [IsElementaryAbelian 5 X]
    (hcard : Nat.card X = 5 ^ 2) (W : Subgroup (MulAut X)) (h5 : ¬ 5 ∣ Nat.card W) :
    OddOrderOneOrThree ↥W := by
  have h1 : Nat.card W ∣ 480 :=
    (Subgroup.card_subgroup_dvd_card W).trans (card_mulAut_dvd_480 hcard)
  have h2 : Nat.Coprime (Nat.card W) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
  have h3 : Nat.card W ∣ 2 ^ 5 * 3 := by
    have : Nat.card W ∣ (2 ^ 5 * 3) * 5 := by norm_num; exact h1
    exact h2.dvd_of_dvd_mul_right this
  exact OddOrderOneOrThree.of_card_dvd h3

theorem row8OddConcl_five {Q : Type} [Group Q] [Finite Q] {g : ℕ} {Ē : Subgroup Q}
    (h : Row8Conf 5 g Q Ē) : Row8OddConcl 5 Q Ē := by
  intro h5
  have : IsElementaryAbelian 5 ↥Ē := h.elem
  exact oddOrderOneOrThree_of_five h.card _ h5

end CFSG.RankThree.PartOne.K133B
