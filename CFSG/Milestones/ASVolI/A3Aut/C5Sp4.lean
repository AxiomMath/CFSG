module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBSp4
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section C5Sp4

variable {K : Type} [Field K] [Finite K]

theorem burnsideAut_c5Sp4_map_fieldAut_U [CharP K 2] (σ : K ≃+* K) :
    (SymplecticFlag.projUnipotent 2 K).map (SymplecticHigher.fieldAut 2 K σ).toMonoidHom =
      SymplecticFlag.projUnipotent 2 K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (CFSG.Quasithin.Sp4.fieldAut_mem_projUnipotent_iff σ y).2 hy
  · intro hx
    refine ⟨(SymplecticHigher.fieldAut 2 K σ).symm x, ?_, MulEquiv.apply_symm_apply _ _⟩
    change _ ∈ SymplecticFlag.projUnipotent 2 K
    rw [← CFSG.Quasithin.Sp4.fieldAut_mem_projUnipotent_iff σ, MulEquiv.apply_symm_apply]
    exact hx

theorem burnsideAut_c5Sp4_isSylow [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (SymplecticFlag.projUnipotent 2 K) ⊤ := by
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_projUnipotent (r := 2) (K := K) 2 (by norm_num)
  rw [← hP]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem burnsideAut_c5Sp4_fieldAut_injective :
    Function.Injective (SymplecticHigher.fieldAut 2 K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff (r := 2) (K := K)
    (by norm_num)).1 ⟨1, by rw [hσ, map_one]⟩

theorem burnsideAut_c5Sp4_inn_inf_field :
    (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ⊓
      (SymplecticHigher.fieldAut 2 K).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hφI, ⟨σ, rfl⟩⟩
  have h1 := (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff (r := 2) (K := K)
    (by norm_num)).1 (CFSG.RankThree.PartTwo.KFacts.innAut_le_range_spConjAut 2 K hφI)
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem burnsideAut_c5Sp4_odd_mem [CharP K 2] {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ⊔
      (SymplecticHigher.fieldAut 2 K).range := by
  obtain ⟨A, σ, hAσ⟩ := (SymplecticHigher.mem_spSemilinearAutGroup_iff (r := 2) (K := K)).1
    (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow hα (pow_orderOf_eq_one α))
  rw [hAσ]
  exact Subgroup.mul_mem_sup (CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A)
    ⟨σ, rfl⟩

theorem burnsideAut_a315_Sp4 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hn : 2 ≤ n)
    (hL : CFSG.Quasithin.IsPSp4 2 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L := Or.inr (Or.inr (Or.inr (Or.inl hL)))
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hL
  haveI : CharP K 2 := burnsideA26_charP_two hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUsyl := burnsideAut_c5Sp4_isSylow (K := K)
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow e₀
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hMZ := burnsideAut_c5_center_eq_bot h e
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  refine burnsideAut_case5_of_model2 h n hn hLie hMZ e he hUsyl
    (IM := (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range)
    (ΦM := (SymplecticHigher.fieldAut 2 K).range) le_rfl ?_ ?_ ?_ ?_
    burnsideAut_c5Sp4_inn_inf_field ?_ ?_ (burnsideAut_solvBorel_projSp4 hK4) ?_
  · exact burnsideAut_inn_relIndex_self _
  · exact burnsideAut_map_inn_le_innDiag e
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  · haveI := burnsideAut_inn_normal' (StatedProj (StatedSp 2 K))
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rintro _ ⟨σ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (burnsideAut_c5Sp4_map_fieldAut_U σ)
  · intro b hb
    exact burnsideAut_c5Sp4_odd_mem (burnsideAut_c5_odd_orderOf h e hb)
  · intro ε hε F hF _ _
    obtain ⟨hcyc, hdvd, σ, -, hpin⟩ := burnsideAut_pinned_of_field
      (SymplecticHigher.fieldAut 2 K) burnsideAut_c5Sp4_fieldAut_injective hcard.2
      (MulEquiv.refl _) hUsyl burnsideAut_c5Sp4_map_fieldAut_U
      (fun σ mg => ChA.IsProjFieldAut (StatedSp 2 K) σ mg)
      (fun σ g => ⟨SymplecticHigher.fieldSp 2 K σ g, rfl, rfl⟩) ε hε F hF
    refine ⟨hcyc, ?_, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨K, inferInstance, inferInstance, ε.trans (MulEquiv.refl _), σ, hK, hpin⟩)))⟩
    rwa [hcard.1] at hdvd

end C5Sp4

end CFSG.ASVolI
