module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.QuotientCentralizer
public import CFSG.RankThree.PartTwo.KFacts.K426A6
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Sporadic.Schreier (j3P)
open CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Quasithin.Kleidman.ThreeLocal

theorem map_centralizer_of_injective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (a : A) :
    (Subgroup.centralizer ({a} : Set A)).map f =
      Subgroup.centralizer ({f a} : Set B) ⊓ f.range := by
  ext b
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← map_mul, ← map_mul, hx]
  · rintro ⟨hb, x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hb ⊢
    apply hf
    rw [map_mul, map_mul, hb]

theorem centralizer_pow_eq {P : Type*} [Group P] {c : P} (hc : c ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({c ^ e} : Set P) = Subgroup.centralizer ({c} : Set P) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hc4 : c = c ^ 2 * c ^ 2 := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hc, one_mul, pow_one]
      calc x * c = x * (c ^ 2 * c ^ 2) := by rw [← hc4]
        _ = c ^ 2 * c ^ 2 * x := by
          rw [← mul_assoc, hx, mul_assoc, hx, mul_assoc]
        _ = c * x := by rw [← hc4]
    · intro hx
      rw [pow_two, ← mul_assoc, hx, mul_assoc, hx, mul_assoc]

end CFSG.Quasithin.Kleidman
