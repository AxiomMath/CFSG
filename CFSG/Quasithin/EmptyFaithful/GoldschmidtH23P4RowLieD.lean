module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieA
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics

public section

namespace CFSG.Quasithin.H23P4

open Matrix CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic

theorem isSylowTwoOf_unitriangular_zmod {n : ℕ} (hn : 1 ≤ n) :
    IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  rw [isSylowTwoOf_top_iff, ← hP]
  exact ⟨P.isPGroup', P.not_dvd_index⟩

theorem eq_zero_of_relIndex_unitriangular {n : ℕ}
    {Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hUY : unitriangular n (ZMod 2) ≤ Y)
    {b : ℕ} (hb : (unitriangular n (ZMod 2)).relIndex Y = 5 ^ b) : b = 0 := by
  by_cases h : ∃ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n), reflection n (ZMod 2) j hj hjn ∈ Y
  · exfalso
    obtain ⟨j, hj, hjn, hr⟩ := h
    have hM : flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) ≤ Y := by
      rw [parabolic_eq_closure hj hjn, Subgroup.closure_le]
      rintro g (hg | hg)
      · exact hUY hg
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hr
    have h3 : 3 ∣ (unitriangular n (ZMod 2)).relIndex Y := by
      have e := Subgroup.relIndex_mul_relIndex _ _ _ (unitriangular_le_flagStabilizer _) hM
      rw [relIndex_parabolic hj hjn] at e
      exact Dvd.intro _ e
    rw [hb] at h3
    have h35 : 3 ∣ 5 := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  · have hY := (borel_overgroups Y (by rw [upperTriangular_eq_unitriangular]; exact hUY)).1
    have hcuts : Set.Icc 1 (n - 1) ⊆ borelOvergroupCuts Y := by
      intro i hi
      obtain ⟨hi1, hin⟩ := hi
      exact ⟨hi1, by omega, fun hr => h ⟨i, hi1, by omega, hr⟩⟩
    have hYU : Y ≤ unitriangular n (ZMod 2) :=
      calc Y = flagStabilizer n (ZMod 2) (borelOvergroupCuts Y) := hY
        _ ≤ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1)) := flagStabilizer_anti hcuts
        _ = unitriangular n (ZMod 2) := flagStabilizer_Icc
    rw [le_antisymm hYU hUY, Subgroup.relIndex_self] at hb
    exact (Nat.pow_eq_one.mp hb.symm).resolve_left (by norm_num)

theorem noFiveIndex_specialLinear_two {n : ℕ} (hn : 1 ≤ n) :
    NoFiveIndex (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  NoFiveIndex.of_sylow (isSylowTwoOf_unitriangular_zmod hn) fun _ hU _ hb =>
    eq_zero_of_relIndex_unitriangular hU hb

theorem center_eq_bot_specialLinear_two {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin] at hz
  obtain ⟨r, hr, hrz⟩ := hz
  have hr1 : r = 1 := by
    rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
    · rw [zero_pow (by omega)] at hr
      exact absurd hr zero_ne_one
    · rfl
  apply Subtype.ext
  rw [← hrz, hr1]
  simp

end CFSG.Quasithin.H23P4
