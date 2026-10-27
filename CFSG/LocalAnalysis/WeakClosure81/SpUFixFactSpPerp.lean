module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRoot
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixed
import CFSG.ClassicalGroups.Alternating.I4SpInvolBlock

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.ClassicalGroups.Alternating

variable {k : ℕ} {F : Type} [Field F]

@[expose] noncomputable def spUFixGspHomSp (k : ℕ) (F : Type) [Field F] :
    ↥(StatedSp k F) →* Gsp (spForm k F) where
  toFun g := ⟨spLin k F g, by
    rw [CFSG.RankThree.PartOne.KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup]
    exact spLin_mem g⟩
  map_one' := Subtype.ext (map_one (spLin k F))
  map_mul' a b := Subtype.ext (map_mul (spLin k F) a b)

theorem spUFixGspHomSp_injective :
    Function.Injective (spUFixGspHomSp k F) := by
  intro a b h
  exact spLin_injective (congrArg Subtype.val h)

theorem exists_mul_pow_three_spUFixRootSp [CharP F 2] {v w : Fin k ⊕ Fin k → F}
    (hvw : spForm k F v w ≠ 0) :
    ∃ x ∈ spUFixRootSp v, ∃ y ∈ spUFixRootSp w, (x * y) ^ 3 = 1 ∧ x * y ≠ 1 := by
  have hB : (spForm k F).IsAlt := spForm_isAlt
  let d : F := (spForm k F v w)⁻¹
  have hmemv : spTransvection v d ∈ spUFixRootSp v :=
    Subgroup.subset_closure (Set.mem_range_self d)
  have hmemw : spTransvection w d ∈ spUFixRootSp w :=
    Subgroup.subset_closure (Set.mem_range_self d)
  have hmapv : spUFixGspHomSp k F (spTransvection v d) = Tsp hB v d :=
    Subtype.ext (spLin_spTransvection v d)
  have hmapw : spUFixGspHomSp k F (spTransvection w d) = Tsp hB w d :=
    Subtype.ext (spLin_spTransvection w d)
  have horder : orderOf (spTransvection v d * spTransvection w d) = 3 := by
    have hmap : spUFixGspHomSp k F (spTransvection v d * spTransvection w d)
        = Tsp hB v d * Tsp hB w d := by
      rw [map_mul, hmapv, hmapw]
    have h1 : orderOf (spUFixGspHomSp k F (spTransvection v d * spTransvection w d)) = 3 := by
      rw [hmap]
      exact orderOf_Tsp_mul_Tsp hB hvw
    have h2 : orderOf (spUFixGspHomSp k F (spTransvection v d * spTransvection w d))
        = orderOf (spTransvection v d * spTransvection w d) :=
      orderOf_injective (spUFixGspHomSp k F) spUFixGspHomSp_injective _
    rwa [h2] at h1
  refine ⟨spTransvection v d, hmemv, spTransvection w d, hmemw, ?_, ?_⟩
  · have h : (spTransvection v d * spTransvection w d) ^
        orderOf (spTransvection v d * spTransvection w d) = 1 := pow_orderOf_eq_one _
    rwa [horder] at h
  · intro hcon
    rw [hcon, orderOf_one] at horder
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
