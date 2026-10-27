module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Nobq

variable {G : Type} [Group G] [Finite G]

theorem outTwoCyclic_of_centerQuotient {K : Type*} [Group K] [Group.IsPerfect K]
    (h : Nobq.OutTwoCyclic (K ⧸ Subgroup.center K)) : Nobq.OutTwoCyclic K := by
  intro P hP
  have hP' : IsPGroup 2 (P.map (centerQuotientOuterHom K)) :=
    hP.map (centerQuotientOuterHom K)
  have hcyc : IsCyclic (P.map (centerQuotientOuterHom K)) := h _ hP'
  haveI : IsCyclic (P.map (centerQuotientOuterHom K)) := hcyc
  exact isCyclic_of_injective_hom
    (Subgroup.equivMapOfInjective P (centerQuotientOuterHom K)
      (centerQuotient_outer_injective K)).toMonoidHom
    (Subgroup.equivMapOfInjective P (centerQuotientOuterHom K)
      (centerQuotient_outer_injective K)).injective

theorem outTwoCyclic_bar2_of_isU5 {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (h : IsU5 (BarInf L) n) : Nobq.OutTwoCyclic (Bar2 L) := by
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  have hsm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (BarInf L) .PSU 5 2 n :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5L5U5.statedClassicalModel_of_lieModel_psu h
  have hodd : Odd (Nat.gcd 5 (2 ^ n + 1)) :=
    (by decide : Odd 5).of_dvd_nat (Nat.gcd_dvd_left 5 _)
  have hout : Nobq.OutTwoCyclic (BarInf L) :=
    CFSG.ClassicalInvolution.Q3.TA3.outTwoCyclic_PSU hsm hodd
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  exact outTwoCyclic_of_centerQuotient (Nobq.OutTwoCyclic.of_mulEquiv e.symm hout)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
