module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelK1

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def N1 : VM := mkV (ex 1) (ex 1)
@[expose] def N2 : VM := mkV (ex 1) (ex 1 + ex 2)
@[expose] def N4 : VM := mkV (ex 2) (ex 1 + ex 2)
@[expose] def N5 : VM := mkV (ex 1 + ex 2) (ex 1)
@[expose] def N6 : VM := mkV (ex 1 + ex 2) (ex 2)

@[expose] def Ev12 : VM := mkV (ex 1 + ex 2) 0
@[expose] def F12 : VM := mkV 0 (ex 1 + ex 2)
@[expose] def Ma : VM := mkV (ex 1) (ex 2)
@[expose] def Mb : VM := mkV (ex 2) (ex 1)
@[expose] def Mc : VM := mkV (ex 1 + ex 2) (ex 1 + ex 2)

theorem qM_N1 : qM N1 = 1 := by decide
theorem qM_N2 : qM N2 = 1 := by decide
theorem qM_N4 : qM N4 = 1 := by decide
theorem qM_N5 : qM N5 = 1 := by decide
theorem qM_N6 : qM N6 = 1 := by decide

theorem inr_N1 : N1 (Sum.inr 0) = 0 := by decide
theorem inr_N2 : N2 (Sum.inr 0) = 0 := by decide
theorem inr_N4 : N4 (Sum.inr 0) = 0 := by decide
theorem inr_N5 : N5 (Sum.inr 0) = 0 := by decide
theorem inr_N6 : N6 (Sum.inr 0) = 0 := by decide

theorem trv1_mem : trv N1 ∈ Hm := trv_mem_Hm qM_N1 inr_N1
theorem trv2_mem : trv N2 ∈ Hm := trv_mem_Hm qM_N2 inr_N2
theorem trv4_mem : trv N4 ∈ Hm := trv_mem_Hm qM_N4 inr_N4
theorem trv5_mem : trv N5 ∈ Hm := trv_mem_Hm qM_N5 inr_N5
theorem trv6_mem : trv N6 ∈ Hm := trv_mem_Hm qM_N6 inr_N6

@[expose] def E1X : TX := ⟨E1, by decide⟩

@[expose] def tx9 : List VM := [E1, E2, Ev12, F1, F2, F12, Ma, Mb, Mc]

theorem TX_list : ∀ d : VM, inU d → qM d = 0 → d = 0 ∨ d ∈ tx9 := by
  decide +kernel

theorem TX_list' (d : VM) (hi : inU d) (hq : qM d = 0) (h0 : d ≠ 0) :
    d = E1 ∨ d = E2 ∨ d = Ev12 ∨ d = F1 ∨ d = F2 ∨ d = F12 ∨ d = Ma ∨ d = Mb ∨ d = Mc := by
  rcases TX_list d hi hq with h | h
  · exact absurd h h0
  · simpa [tx9] using h

theorem E1_orbit_VM : ∀ d : VM, inU d → qM d = 0 → d ≠ 0 → ∃ g : Hm, projU (g.1 E1) = d := by
  intro d hi hq h0
  rcases TX_list' d hi hq h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨⟨trv N6 * trv N1 * trv N2,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ trv6_mem trv1_mem) trv2_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N5 * trv N1, Subgroup.mul_mem _ trv5_mem trv1_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N1, trv1_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N4 * trv N1 * trv N5 * trv N1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ trv4_mem trv1_mem) trv5_mem) trv1_mem⟩,
      by decide +kernel⟩
  · exact ⟨⟨trv N2, trv2_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N1 * trv N2, Subgroup.mul_mem _ trv1_mem trv2_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N1 * trv N5 * trv N1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ trv1_mem trv5_mem) trv1_mem⟩, by decide +kernel⟩
  · exact ⟨⟨trv N2 * trv N6 * trv N1 * trv N2,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ trv2_mem trv6_mem) trv1_mem)
        trv2_mem⟩, by decide +kernel⟩

theorem Hm_trans_TX (c d : TX) : ∃ g : Hm, g • c = d := by
  have orb : ∀ x : TX, ∃ g : Hm, g • E1X = x := by
    intro x
    obtain ⟨g, hg⟩ := E1_orbit_VM x.1 x.2.1 x.2.2.1 x.2.2.2
    exact ⟨g, Subtype.ext (by rw [TX_smul_val]; exact hg)⟩
  obtain ⟨gc, hgc⟩ := orb c
  obtain ⟨gd, hgd⟩ := orb d
  refine ⟨gd * gc⁻¹, ?_⟩
  rw [mul_smul, ← hgc, inv_smul_smul, hgd]

end CFSG.Quasithin.H13.C1294.Model

end
