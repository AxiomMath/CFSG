module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOUniBlock
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h

section Assembly

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem unitary_inner_a5_false {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) (hℓ2 : ℓ ≠ 2)
    (hn : n ∣ 3) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A)))
    (hZ : Subgroup.center ↥T = ⊥)
    (hL : Nonempty ((↥T ⧸ Subgroup.center ↥T) ≃* alternatingGroup (Fin 5))) : False := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have H := primaryData_toLin' h A.2 hp hpℓ hA
  obtain ⟨a, ha⟩ := exists_good_primaryFactor_of_component hq A rfl H T hT
  have hSle : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let F : Subgroup ↥(gramSU h (idGram K n)) :=
    (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])).comap (toLinSU h n)
  have hFmap : F.map (toLinSU h n) = specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X]) :=
    Subgroup.map_comap_eq_self hSle
  let ε : ↥(specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])) ≃* ↥F :=
    ((Subgroup.equivMapOfInjective F (toLinSU h n) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)).symm
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  haveI : Finite ↥F := inferInstance
  subst ha
  have hmem : ∀ u : ↥(specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X])),
      ((π.subgroupMap F).comp ε.toMonoidHom) u = 1 →
      ((ε u : ↥F) : ↥(gramSU h (idGram K n))) ∈
        normOneScalars h (gramSU h (idGram K n)) n := fun u hu => by
    rw [MonoidHom.comp_apply] at hu
    have h1 : π (ε u : ↥(gramSU h (idGram K n))) = 1 := congrArg Subtype.val hu
    exact (QuotientGroup.eq_one_iff _).1 h1
  refine good_block_a5_false H a.1 a.2 hℓ2 ((π.subgroupMap F).comp ε.toMonoidHom)
    ((MonoidHom.subgroupMap_surjective π F).comp ε.surjective) (fun u hu => ?_) (fun u hu => ?_)
    hZ hL
  · have h2 := hmem u hu
    have h3 := normOneScalars_le_center h _ n h2
    rw [Subgroup.mem_center_iff]
    intro w
    apply ε.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.1 h3 _
  · obtain ⟨c', -, hc'n, hc'⟩ := hmem u hu
    have hc3 : c' ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := hn
      rw [hk, pow_mul, hc'n, one_pow]
    apply ε.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, hc', ← map_pow, hc3, map_one]
    rfl

end Assembly

end CFSG.RankThree.PartTwo.Sec21.FF79
