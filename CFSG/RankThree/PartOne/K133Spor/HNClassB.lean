module

public import CFSG.RankThree.PartOne.K133Spor.RhoPlane
public import CFSG.RankThree.PartOne.K133Spor.HNHom
public import CFSG.RankThree.PartOne.K133Spor.HNKlein

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.K133 Subgroup

noncomputable def psi4 :
    Subgroup.centralizer ({t4J} : Set JH) →* rho4.range :=
  rho4.rangeRestrict.comp
    (MonoidHom.codRestrict (jR.comp (Subgroup.subtype _)) C4 fun g => jR_mem_C4 g.2)

theorem psi4_ker
    (y : Subgroup.centralizer ({t4J} : Set JH)) (h : psi4 y = 1) :
    (y : JH) = 1 ∨ (y : JH) = t4J := by
  have h1 : rho4 (⟨jR y, jR_mem_C4 y.2⟩ : C4) = 1 := congrArg Subtype.val h
  have hz : (⟨jR y, jR_mem_C4 y.2⟩ : C4) ∈ rho4.ker := h1
  rw [ker_rho4] at hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hmod : t4C ^ (k % 2) = t4C ^ k := by
    have := zpow_mod_orderOf t4C k
    rwa [orderOf_t4C, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    rw [h0, zpow_zero] at hmod
    have e : jR (y : JH) = 1 := by
      have := congrArg Subtype.val (hk.symm.trans hmod.symm)
      exact this
    exact jR_injective (by rw [e, map_one])
  · right
    rw [h0, zpow_one] at hmod
    have e : jR (y : JH) = jR t4J := by
      have := congrArg Subtype.val (hk.symm.trans hmod.symm)
      exact this
    exact jR_injective e

theorem hnClass_t4J :
    HNClass t4J :=
  hnClass_of_hom t4J (by rw [sq]; exact t4J_sq) t4J_ne_one psi4 psi4_ker rho4_planeFree

end CFSG.RankThree.PartOne.K133Spor
