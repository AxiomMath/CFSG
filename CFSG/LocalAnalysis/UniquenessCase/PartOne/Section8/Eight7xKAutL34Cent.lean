module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem card_centralizer_of_orderOf_three_psl_three_four {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) {x : L} (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set L)) = 9 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite K := LinearFieldFour.finite_of_card_eq_four hK4
  have : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hK4]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy : orderOf (φ x) = 3 := (MulEquiv.orderOf_eq φ x).trans hx
  have hy1 : φ x ≠ 1 := by
    intro h
    rw [h] at hy
    exact (by norm_num : (1 : ℕ) ≠ 3) (by simp at hy)
  have hp : IsPGroup 3 (Subgroup.zpowers (φ x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 K)) = 9 := by
    rw [Sylow.card_eq_multiplicity, CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hK4]
    norm_num
  have hcent : Subgroup.centralizer ({φ x} : Set (projectiveSL 3 K)) = S :=
    CFSG.RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hK4 hS9
      (hS (Subgroup.mem_zpowers (φ x))) hy1
  have hcardP : Nat.card (Subgroup.centralizer ({φ x} : Set (projectiveSL 3 K))) = 9 := by
    rw [hcent, hS9]
  have hmap : (Subgroup.centralizer ({x} : Set L)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set (projectiveSL 3 K)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      apply (Subgroup.mem_centralizer_singleton_iff).mpr
      have hw' : x * w = w * x := Subgroup.mem_centralizer_iff.mp hw x (Set.mem_singleton x)
      change φ.toMonoidHom w * φ.toMonoidHom x = φ.toMonoidHom x * φ.toMonoidHom w
      rw [← map_mul, ← map_mul, hw']
    · intro hz
      refine ⟨φ.symm z, ?_, ?_⟩
      · apply (Subgroup.mem_centralizer_singleton_iff).mpr
        have hz' : φ x * z = z * φ x :=
          Subgroup.mem_centralizer_iff.mp hz (φ x) (Set.mem_singleton (φ x))
        apply φ.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hz'.symm
      · simp
  have hcard := Subgroup.card_map_of_injective (K := Subgroup.centralizer ({x} : Set L))
    (f := φ.toMonoidHom) φ.injective
  rw [← hcard, hmap]
  exact hcardP

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
