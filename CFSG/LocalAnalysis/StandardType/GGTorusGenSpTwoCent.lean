module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCentFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial

theorem centralizer_le_of_selfCent_spTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} {E : Subgroup (StatedSp m K)} (hE : IsElemAbelian 3 E)
    (hEsc : ∀ Z : StatedSp m K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E) :
    Subgroup.centralizer (E : Set (StatedSp m K)) ≤ E := by
  classical
  set e₂ : ↥(StatedSp m K) ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin) with he₂
  set E' : Subgroup ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    E.map e₂.toMonoidHom with hE'
  have hE'el : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE _
  have hsc' : ∀ Z : ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)),
      (∀ Y ∈ E', Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E' := by
    intro Z hZ hZ3
    obtain ⟨z, rfl⟩ := e₂.surjective Z
    rw [hE']
    refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
    refine hEsc z ?_ ?_
    · intro Y hY
      apply e₂.injective
      rw [map_mul, map_mul]
      exact hZ (e₂ Y) (Subgroup.mem_map.mpr ⟨Y, hY, rfl⟩)
    · apply e₂.injective
      rw [map_pow, hZ3, map_one]
  have hcent := SpNS.centralizer_le_of_selfCent_spForm hK
    CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate
    E' hE'el hsc'
  intro z hz
  have hz' : e₂ z ∈ Subgroup.centralizer (E' : Set _) := by
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro y hy
    obtain ⟨Y, hY, rfl⟩ := Subgroup.mem_map.mp hy
    simpa using congrArg e₂ (hz Y hY)
  have hzE' : e₂ z ∈ E' := hcent hz'
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzE'
  rwa [← e₂.injective hyz]

theorem ggTorusCentSC_spTwo {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (m : ℕ) : GGTorusCentSC 3 (LargeEvenProj (LargeEvenSpGroup K m)) := by
  by_cases hm : m = 0
  · subst hm
    intro E _ h3 _ c _ _
    exfalso
    have h1 : Nat.card E ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr
        (Subsingleton.intro fun a b =>
          Subtype.ext (Subsingleton.elim (a : LargeEvenProj (LargeEvenSpGroup K 0)) b))
    omega
  · have : NeZero m := ⟨hm⟩
    refine ggTorusCentSC_of_mulEquiv (TableBSymp.spProjEquivSp (K := K) (m := m)) ?_
    intro E hE h3 hEsc c hc _
    exact centralizer_le_of_selfCent_spTwo (K := K) hK (m := m) (E := E) hE hEsc
      (Subgroup.mem_centralizer_iff.mpr fun e he => (hc e he).symm)

end CFSG.StandardType
