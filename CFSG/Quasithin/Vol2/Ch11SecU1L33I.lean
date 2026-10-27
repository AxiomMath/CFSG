module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33H
public import CFSG.Quasithin.Vol2.Ch11SecU1L33C
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IZ

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.A38c15
  CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_one_of_psl3_three (hirr : SL3OddIrr)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 3 3 1 ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) (hTL : ¬ T ≤ CFSG.generalizedFitting G) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  set L := CFSG.generalizedFitting G with hLdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 hF
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := L3I.exists_ne_comm_psl3 (p := 3)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT hFT
  have := hAS.normal
  have := hAS.simple
  have hGL : ∃ t : G, t ∉ L := by
    obtain ⟨t, -, ht⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
    exact ⟨t, ht⟩
  obtain ⟨M⟩ := exists_model hAS.centralizer_eq e hGL
  have hO2 := pCoreOf_top_eq_bot_of_normal_simple L hAS.nonabelian hAS.centralizer_eq
  have hT₀ := M.isSylow_T0
  obtain ⟨z, -, hzc⟩ := M.exists_mem tl_facts z0_check.1
  have hzL : z ∈ L := (M.mem_iff_code z).mpr (by rw [hzc]; exact z0_check.2.2.2.2.1)
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      exact M.code_inj (by rw [Model.code_mul, hzc, Model.code_one]; exact z0_check.2.2.1)
    · intro h
      apply z0_check.2.2.2.1
      rw [← hzc, h, Model.code_one]
  have hTz : M.T0 ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (M.commute_of_code (by rw [hzc]; exact z0_check.2.1 _ ht))
  have hD := L3I.isCoatom_centralizer_L3 hirr (by norm_num) hAS e hGL hzL hz2
  have hDn := E1.solvable_nParam_le_one (isSolvable_centralizer hAS e hzL hz2)
  have h := SecU1.inEFor_top_of_coatom_nParam_conj hT₀ hTz hDn hD
    (fun A hAT hA2 => isE_one_top_of_almostSimple L M.T0 A hAS.nonabelian hAS.centralizer_eq hT₀
      (L3I.sup_eq_top_of_almostSimple hAS hT₀) hAT hA2)
    (fun A hAT hA hA4 => M.exists_member hO2 hzc hAT hA hA4)
  have h1 := (nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT₀).mpr h)
  simpa using h1

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
