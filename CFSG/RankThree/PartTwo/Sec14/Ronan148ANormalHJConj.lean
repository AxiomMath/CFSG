module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartTwo.Sec14.Ronan148VOmega6
import CFSG.RankThree.PartTwo.Sec14.LBNatural
import CFSG.RankThree.PartTwo.Sec14.Closure
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_img148_deltaZero {A Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] :
    Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
      Subgroup.normalizer (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  intro t ht
  obtain ⟨w, hwA, rfl⟩ := Ronan148V.exists_normalizer_lift148 hA3 ht
  have hwY : (w : G) ∈ Subgroup.normalizer (Y : Set G) :=
    (sup_le Subgroup.le_normalizer hY.2 : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G)) w.2
  have hwX := Sec14.mem_normalizer_deltaZero (isNaturalFamily_lB A) hwA hwY
  exact img148_le_normalizer (A := A) (Y := Y) (Subgroup.zpowers_le.mpr hwX)
    (mem_img148_iff.mpr ⟨w, w.2, Subgroup.mem_zpowers _, rfl⟩)

theorem false_of_map_conj_normalizer148 {A Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] {t : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (ht : t ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {T K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hT : T ≤ img148 A Y (deltaZero A (lB A) Y))
    (hK : IsComponent K) (hKT : K = T.map (MulAut.conj t).toMonoidHom)
    (hKC : K ≤ Subgroup.centralizer
      (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have htX := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_img148_deltaZero hA3 hY ht)
  have hKX : K ≤ img148 A Y (deltaZero A (lB A) Y) := by
    rw [hKT, ← htX]
    exact Subgroup.map_mono hT
  have hKK : K ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hKC.trans (Subgroup.centralizer_le hKX)
  have hcomm : IsMulCommutative ↥K := Subgroup.le_centralizer_iff_isMulCommutative.mp hKK
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isMulCommutative ↥K hcomm

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
