module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpHall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpAct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open SymplecticFlag (borelSubgroup unipotent)
open SymplecticHigher (flagStabilizer)
open KTabD (lineStab)

theorem kAdj_model_sp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (m : ℕ) {r : ℕ} (hr : Odd r)
    {t : StatedSp (m + 2) K}
    (ht : t ∈ Hinf (flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))) ⊓
      lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1))
    (hord : orderOf t = r) :
    KAdjConcl (Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1))) t r n := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right' (a := 2) (by norm_num) hn
  obtain ⟨htα, ht0⟩ := Subgroup.mem_inf.mp ht
  have htQα : t ∈ flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) :=
    Subgroup.map_subtype_le _ htα
  have htB : t ∈ borelSubgroup (m + 2) K := by
    rw [← flagStabilizer_inf_eq_borelSubgroup m K]
    exact ⟨htQα, by rwa [← lineStab_statedSp_eq_flagStabilizer]⟩
  have hodd : ¬ 2 ∣ orderOf t := by
    rw [hord]
    exact hr.not_two_dvd_nat
  obtain ⟨e, he, hconj⟩ := exists_conj_eq_torusHom_diagHom_sp htB hodd
  obtain ⟨c, hc⟩ := exists_diagHom_eq_coroot_of_mem_hinf_sp m htα htB
  have h1 : e * t * e⁻¹ = coorootSp m c := by
    rw [hconj, hc]
    rfl
  have hord' : orderOf c = r := by
    rw [← orderOf_coorootSp m c, ← h1, ← hord]
    exact orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective t
  have hXK := longRootSp2_le_hinf_lineStab (K := K) hK4 m
  have hmain : KAdjConcl
      (Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)))
      (coorootSp m c) r n := by
    refine ⟨longRootSp2 K (m + 2) 1, longRootSp2 K (m + 2) 1, hXK, hXK, ?_, ?_⟩
    · intro N hN hnorm hX1 _
      exact normal_closure_longRootSp2 hK4 m N hN hnorm hX1
    · rintro Y (rfl | rfl) <;>
        exact ⟨isSLn_longRootSp2 hK m, coorootSp_mem_normalizer_longRootSp2 m c,
          rootDiagSp m c, rootDiagSp_mem_longRootSp2 m c, by rw [orderOf_rootDiagSp, hord'],
          fun x hx => coorootSp_mul_mul_inv_eq m c hx⟩
  rw [← h1] at hmain
  exact kAdjConcl_conj e (unipotent_le_normalizer_hinf_lineStab m K he) hmain

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
