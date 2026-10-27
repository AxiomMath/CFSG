module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLine
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.Quasithin.SteinbergCGA7ListedActorSupport
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovArith
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SymmetricGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Matrix

open CFSG.Quasithin.RonanF13

private theorem s16c11_fr_O_two_eq_O4 : S16C11FrO 2 = SmallOmegaFour.O4 :=
  Subgroup.closure_eq SmallOmegaFour.O4

private noncomputable def s16c11_fr_O_two_equiv_perm5 :
    ↥(S16C11FrO 2) ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.subgroupCongr s16c11_fr_O_two_eq_O4).trans SmallOmegaFour.o4MulEquivPerm

private theorem s16c11_fr_selfNormSylow_two : SelfNormSylow ↥(S16C11FrO 2) := by
  intro T hT hodd
  let e := s16c11_fr_O_two_equiv_perm5
  have hX : Nat.card ↥(S16C11FrO 2) = 2 ^ 3 * 15 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F53.card_perm5]
    norm_num
  have hcardT : Nat.card T = 8 := by
    have h := CFSG.Quasithin.H13.card_two_subgroup_of_card_cv (X := ↥(S16C11FrO 2))
      T hT hodd (e := 3) (m := 15) hX (by norm_num)
    simpa using h
  have hP : Nat.card (T.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, hcardT]
  have hN : Subgroup.normalizer (T.map e.toMonoidHom : Set (Equiv.Perm (Fin 5))) =
      T.map e.toMonoidHom :=
    CFSG.Quasithin.F53.normalizer_eq_of_card_eight _ hP
  have hmap : (Subgroup.normalizer (T : Set ↥(S16C11FrO 2))).map e.toMonoidHom =
      Subgroup.normalizer (T.map e.toMonoidHom : Set (Equiv.Perm (Fin 5))) :=
    Subgroup.map_equiv_normalizer_eq T e
  rw [hN] at hmap
  exact Subgroup.map_injective e.injective hmap

private theorem s16c11_fr_O_one_eq_top : S16C11FrO 1 = ⊤ := by
  have h : ∀ A : Matrix.GeneralLinearGroup (S16C11FrIdx 1) (ZMod 2),
      ∀ v : S16C11FrIdx 1 → ZMod 2,
        S16C11FrQ 1 (Matrix.mulVec
          (A : Matrix (S16C11FrIdx 1) (S16C11FrIdx 1) (ZMod 2)) v) = S16C11FrQ 1 v := by
    decide +kernel
  apply le_antisymm le_top
  intro A _
  exact Subgroup.subset_closure (h A)

private noncomputable def s16c11_fr_gl_one_equiv_perm3 :
    Matrix.GeneralLinearGroup (S16C11FrIdx 1) (ZMod 2) ≃* Equiv.Perm (Fin 3) := by
  have hcard1 : Fintype.card (S16C11FrIdx 1) = 2 := by decide
  let e : S16C11FrIdx 1 ≃ Fin 2 := Fintype.equivFinOfCardEq hcard1
  have hGL : Matrix.GeneralLinearGroup (S16C11FrIdx 1) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e).toRingEquiv.toMulEquiv
  exact hGL.trans (Classical.choice
    (TauCeti.nonempty_mulEquiv_permFinThree (F := ZMod 2) (by decide)))

private noncomputable def s16c11_fr_O_one_equiv_perm3 :
    ↥(S16C11FrO 1) ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.subgroupCongr s16c11_fr_O_one_eq_top).trans
    (Subgroup.topEquiv.trans s16c11_fr_gl_one_equiv_perm3)

private theorem s16c11_fr_selfNormSylow_one : SelfNormSylow ↥(S16C11FrO 1) := by
  intro T hT hodd
  let e := s16c11_fr_O_one_equiv_perm3
  have hX : Nat.card ↥(S16C11FrO 1) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num [Nat.factorial]
  have hcardT : Nat.card T = 2 := by
    have h := CFSG.Quasithin.H13.card_two_subgroup_of_card_cv (X := ↥(S16C11FrO 1))
      T hT hodd (e := 1) (m := 3) hX (by norm_num)
    simpa using h
  have hP : Nat.card (T.map e.toMonoidHom) = 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hcardT]
  have hN : Subgroup.normalizer (T.map e.toMonoidHom : Set (Equiv.Perm (Fin 3))) =
      T.map e.toMonoidHom :=
    CFSG.Quasithin.SteinbergCG.normalizer_eq_of_card_two_perm_three hP
  have hmap : (Subgroup.normalizer (T : Set ↥(S16C11FrO 1))).map e.toMonoidHom =
      Subgroup.normalizer (T.map e.toMonoidHom : Set (Equiv.Perm (Fin 3))) :=
    Subgroup.map_equiv_normalizer_eq T e
  rw [hN] at hmap
  exact Subgroup.map_injective e.injective hmap

theorem s16c11_fr_sylow_normalizer {m : ℕ} (hm : m = 1 ∨ m = 2) :
    ∀ D : Subgroup ↥(S16C11FrO m), IsPGroup 2 ↥D → ¬ 2 ∣ D.index →
      Subgroup.normalizer (D : Set ↥(S16C11FrO m)) = D := by
  rcases hm with rfl | rfl
  · exact s16c11_fr_selfNormSylow_one
  · exact s16c11_fr_selfNormSylow_two

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
