module

public import CFSG.Quasithin.EmptyFaithful.E22SRoot
public import CFSG.Quasithin.EmptyFaithful.E22SGen
public import CFSG.Quasithin.EmptyFaithful.E22PTypeII

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1
  CFSG.Quasithin.A1b
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem projectiveSL_three_nonabelian : ∃ a b : projectiveSL 3 K, a * b ≠ b * a := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ rootImg (1 : SL(3, K)) h02, z ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one (rootImg (1 : SL(3, K)) h02) with h | h
    · exact absurd h (rootImg_ne_bot h02)
    · exact h
  obtain ⟨t, rfl⟩ := (mem_rootImg h02).mp hz
  refine ⟨proj 3 K (Matrix.SpecialLinearGroup.transvection h01 t),
    proj 3 K (Matrix.SpecialLinearGroup.transvection h12 1), fun hab => hz1.elim ?_⟩
  have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection h01 h12 h02 t (1 : K)
  rw [mul_one] at hc
  have : ⁅proj 3 K (Matrix.SpecialLinearGroup.transvection h01 t),
      proj 3 K (Matrix.SpecialLinearGroup.transvection h12 1)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hab
  rw [← map_commutatorElement, hc] at this
  simpa using this

theorem nParam_projectiveSL_three_le_one [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) [IsSimpleGroup (projectiveSL 3 K)] :
    nParam (⊤ : Subgroup (projectiveSL 3 K)) ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (projectiveSL 3 K))
  have : IsSimpleGroup ↥(⊤ : Subgroup (projectiveSL 3 K)) :=
    (Subgroup.topEquiv (G := projectiveSL 3 K)).isSimpleGroup
  have hnc : ∃ a b : ↥(⊤ : Subgroup (projectiveSL 3 K)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := projectiveSL_three_nonabelian (K := K)
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hC : Subgroup.centralizer ((⊤ : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) =
      ⊥ := by
    have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL 3 K))
        with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := projectiveSL_three_nonabelian (K := K)
        have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b
        exact hab this.symm
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
  have hO2 := pCoreOf_top_eq_bot_of_normal_simple ⊤ hnc hC
  refine nParam_top_le_one_of_generation hT ?_ ?_
  · intro A hAT hA
    exact isE_one_top_of_almostSimple ⊤ T A hnc hC hT (top_sup_eq _) hAT hA
  · intro A hAT hAab hA4
    exact iSup_isE_one_eq_top hp2 hT hAT hAab hA4 hO2

end CFSG.Quasithin.E22S
