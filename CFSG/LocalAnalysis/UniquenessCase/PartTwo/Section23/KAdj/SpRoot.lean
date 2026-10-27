module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.StabSp
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.NormalClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped commutatorElement
open KTabD (lineStab)

theorem isSLn_longRootSp2 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (m : ℕ) : IsSLn ↥(longRootSp2 K (m + 2) 1) 2 n := by
  refine ⟨K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective (longBlock_injective (K := K) (n := m + 2) 1)).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)

theorem longRootSp2_le_lineStab {K : Type} [Field K] (m : ℕ) :
    longRootSp2 K (m + 2) 1 ≤ lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
  intro x hx
  have hx' : x ∈ suppGroup (K := K) (coords (1 : Fin (m + 2))) := by
    rwa [longRootSp2, range_longBlock] at hx
  rw [KTabD.mem_lineStab]
  refine ⟨1, ?_⟩
  rw [one_smul]
  exact mulVec_eq_self_of_isSupp hx' (fun t ht => by
    rcases mem_coords.mp ht with rfl | rfl <;> simp [Pi.single_apply])

theorem commutator_longRootSp2 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) (m : ℕ) :
    ⁅longRootSp2 K (m + 2) 1, longRootSp2 K (m + 2) 1⁆ = longRootSp2 K (m + 2) 1 := by
  have hq := CFSG.AGLEmbedding.LeviBlock.isQuasisimple_SL_of_four_le (K := K) hK (m := 2) le_rfl
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ := hq.1
  rw [longRootSp2, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

theorem not_isPGroup_longRootSp2 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) (m : ℕ) :
    ¬ IsPGroup 2 ↥(longRootSp2 K (m + 2) 1) := by
  intro hp
  haveI : Group.IsNilpotent ↥(longRootSp2 K (m + 2) 1) := hp.isNilpotent
  have hq := CFSG.AGLEmbedding.LeviBlock.isQuasisimple_SL_of_four_le (K := K) hK (m := 2) le_rfl
  haveI hqs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := hq.2
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (QuotientGroup.mk_surjective
      (s := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).nontrivial
  let e := MonoidHom.ofInjective (longBlock_injective (K := K) (n := m + 2) 1)
  haveI : Nontrivial ↥(longRootSp2 K (m + 2) 1) := e.injective.nontrivial
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := Group.isPerfect_def.mpr hq.1
  haveI : Group.IsPerfect ↥(longRootSp2 K (m + 2) 1) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact (IsSolvable.commutator_lt_top_of_nontrivial
    ↥(longRootSp2 K (m + 2) 1)).ne (Group.isPerfect_def.mp inferInstance)

theorem isQuasisimple_bar2_hinf_lineStab_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (m : ℕ) :
    CFSG.Open.IsQuasisimple
      (Bar2 (Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)))) := by
  obtain ⟨e⟩ := KTabD.nonempty_bar2_hinf_lineStab_statedSp K hK (m + 1) (by omega)
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e
    (CFSG.AGLEmbedding.LeviBlock.spFlag_isQuasisimple_Sp (by omega) (Or.inl hK))

theorem longRootSp2_le_hinf_lineStab {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (m : ℕ) :
    longRootSp2 K (m + 2) 1 ≤
      Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) :=
  CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual (commutator_longRootSp2 hK m)
    (longRootSp2_le_lineStab m)

theorem normal_closure_longRootSp2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (m : ℕ) (N : Subgroup (StatedSp (m + 2) K))
    (hNK : N ≤ Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)))
    (hnorm : Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) ≤
      Subgroup.normalizer (N : Set (StatedSp (m + 2) K)))
    (hX : longRootSp2 K (m + 2) 1 ≤ N) :
    N = Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) := by
  refine normal_closure_top_of_perfect
    (Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)))
    ?_ (isQuasisimple_bar2_hinf_lineStab_sp hK m) (longRootSp2 K (m + 2) 1)
    (longRootSp2_le_hinf_lineStab hK m) (commutator_longRootSp2 hK m)
    (not_isPGroup_longRootSp2 hK m) N hNK hnorm hX
  exact CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
