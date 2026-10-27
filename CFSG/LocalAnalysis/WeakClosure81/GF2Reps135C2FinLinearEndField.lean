module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem card_endField_eq_two_of_card_eq_two {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {n : ℕ} (hn : 2 ≤ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) K) W)
    (hirr : ρ.IsIrreducible) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) K))
      ρ.asModule) = 2 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  haveI : ρ.IsIrreducible := hirr
  haveI : Finite (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)).Group :=
    CFSG.LieType.RootSystem.finite_group (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  let D := CFSG.LieType.SpecialLinear.curtisDatum m K 2
  have hH : ∀ h ∈ D.H, h = 1 := by
    intro h hh
    have hmem : h ∈ ⨆ k, CFSG.LieType.Universal.SpecialLinear.torus m K k := hh
    have hpow := CFSG.LieType.SpecialLinear.iSup_torus_pow_card_sub_one m K hmem
    have hcard : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    rw [hcard] at hpow
    simpa using hpow
  haveI : (CFSG.endFieldRep ρ).IsIrreducible := CFSG.endFieldRep_isIrreducible ρ
  have hsimple : CFSG.Quasithin.SmithCurtis.IsSimpleRep (CFSG.endFieldRep ρ) :=
    CFSG.HardMathSupport.GuralnickMalle.isSimpleRep_of_isIrreducible (CFSG.endFieldRep ρ)
  have hsplit : CFSG.Quasithin.SmithCurtis.SplitOver (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) D.H := by
    intro h hh
    exact ⟨1, by rw [hH h hh, one_pow], [1], by simp⟩
  obtain ⟨y, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hsimple
  exact CFSG.HardMathSupport.GuralnickMalle.card_endField_eq_two_of_isCurtisType ρ D hH ht

end CFSG.LocalAnalysis.WeakClosure81
