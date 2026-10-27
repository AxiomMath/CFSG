module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private noncomputable def statedSpOneEquiv :
    ↥(StatedSp 1 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  ((Subgroup.equivMapOfInjective (StatedSp 1 K)
      (CFSG.RankThree.GF2n.Stroth80.reindexGL CFSG.RankThree.GF2n.Stroth80.sumFinTwo).toMonoidHom
      (CFSG.RankThree.GF2n.Stroth80.reindexGL CFSG.RankThree.GF2n.Stroth80.sumFinTwo).injective).trans
    (MulEquiv.subgroupCongr CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)).trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm

omit [Finite K] [CharP K 2] in
private theorem spFlagPrev_singleton (b : ℕ) : spFlagPrev ({b} : Set ℕ) b = 0 := by
  rcases spFlagPrev_mem ({b} : Set ℕ) b with h | h
  · exact h
  · have := spFlagPrev_le ({b} : Set ℕ) b
    rw [Set.mem_singleton_iff] at h
    omega

theorem nonempty_bar2_hinf_spFlagStab_three_two (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {2})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hI : ∀ i ∈ ({2} : Set ℕ), i ≤ 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have hI1 : ∀ i ∈ ({2} : Set ℕ), 1 ≤ i := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have htI : (2 : ℕ) ∈ ({2} : Set ℕ) := rfl
  have hmax : ∀ c ∈ ({2} : Set ℕ), c ≤ 2 := fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 2 → j ≠ 0 → spFlagLeviBlock (K := K) hI 2 j = ⊥ := by
    intro j hj2 hj0
    refine spFlagLeviBlock_of_not_mem hI (fun h => hj0 (Fin.ext h)) fun h => hj2 (Fin.ext ?_)
    simpa using h
  have hlen : ((2 : Fin (3 + 1)) : ℕ) - spFlagPrev ({2} : Set ℕ) ((2 : Fin (3 + 1)) : ℕ) = 2 := by
    change 2 - spFlagPrev ({2} : Set ℕ) 2 = 2
    rw [spFlagPrev_singleton]
  have hcomm_top : commutator (StatedSp (3 - 2) K) = ⊤ :=
    (spFlag_isQuasisimple_Sp (K := K) (m := 3 - 2) (by norm_num) (Or.inl hK)).1
  let e₀ : ↥(spFlagLeviBlock (K := K) hI 2 2) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (spFlagLeviBlockMemEquiv (K := K) hI 2 (j := 2) (by decide) htI).trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen)
  let e₁ : ↥(spFlagLeviBlock (K := K) hI 2 0) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((spFlagLeviBlockZeroEquiv (K := K) hI 2 (j := 0) rfl).trans
      ((MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv)).trans statedSpOneEquiv
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  exact nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_two _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) (by decide) (spFlagLeviBlock (K := K) hI 2) hB
    (pi_le_range_spFlagLeviHom hI htI hmax) (commutator_range_spFlagLeviHom_le hI htI) e₀ e₁
    hperf hperf (pCore_specialLinearGroup_eq_bot 2) (pCore_specialLinearGroup_eq_bot 2)

theorem nonempty_bar2_hinf_spFlagStab_three_three :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {3})) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have hI : ∀ i ∈ ({3} : Set ℕ), i ≤ 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have hI1 : ∀ i ∈ ({3} : Set ℕ), 1 ≤ i := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have htI : (3 : ℕ) ∈ ({3} : Set ℕ) := rfl
  have hmax : ∀ c ∈ ({3} : Set ℕ), c ≤ 3 := fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 3 → spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
    intro j hj3
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviBlock_of_eq_zero hI hj0]
      have : Subsingleton ↥(StatedSp (3 - 3) K) := ⟨fun a b => Subtype.ext (Units.ext
        (Matrix.ext fun i _ => i.elim (fun i => i.elim0) fun i => i.elim0))⟩
      rw [Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, -, rfl⟩
      rw [Subsingleton.elim x 1, map_one]
    · exact spFlagLeviBlock_of_not_mem hI hj0 fun h => hj3 (Fin.ext (by simpa using h))
  have hlen : ((3 : Fin (3 + 1)) : ℕ) - spFlagPrev ({3} : Set ℕ) ((3 : Fin (3 + 1)) : ℕ) = 3 := by
    change 3 - spFlagPrev ({3} : Set ℕ) 3 = 3
    rw [spFlagPrev_singleton]
  let e : ↥(spFlagLeviBlock (K := K) hI 3 3) ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (spFlagLeviBlockMemEquiv (K := K) hI 3 (j := 3) (by decide) htI).trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen)
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 3 (spFlagLeviBlock (K := K) hI 3) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl)
    (pCore_specialLinearGroup_eq_bot 3)
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
