module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515bCfg

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fcomm_eq {z z' : G} (hz : z * z = 1) (hz' : z' * z' = 1) :
    fcomm z z' = z * (z' * z * z'⁻¹) := by
  have h1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h2 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'
  simp only [fcomm, h1, h2]
  group

theorem lab_one_cinv (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) :
    lab T z 1 ∈ Cinv G (T.line.vert (a + 3)) := by
  have h := lab_eq_Lb C 1
  rw [show a + 1 + 2 * 1 = a + 3 by ring] at h
  rw [h]
  refine Lb_cinv C.cinv ⟨T.τ, ?_⟩
  have := T.trans (a + 1)
  rwa [show a + 1 + 2 = a + 3 by ring] at this

theorem main_zero (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r)
    {z' : G} (hz'2 : z' * z' = 1) (h2 : z' • T.line.vert (a + 2) = T.line.vert (a + 2))
    (h3 : z' • T.line.vert (a + 3) = T.line.vert (a + 3))
    (h1 : z' • T.line.vert (a + 1) ≠ T.line.vert (a + 1)) : fcomm z z' = lab T z 1 := by
  set α := T.line.vert (a + 1) with hα
  set β := T.line.vert (a + 2) with hβ
  set δ := T.line.vert (a + 3) with hδ
  have hvβ := val_a2 F C
  have hβα : Γ.Adj β α := (adj_a12 T a).symm
  have hβδ : Γ.Adj β δ := adj_a23 T a
  have hαδ : α ≠ δ := by
    have := T.line.nb (a + 1)
    rwa [show a + 1 + 2 = a + 3 by ring] at this
  have hβα' : Γ.Adj β (z' • α) := by
    have := (F.adj_smul z' β α).2 hβα
    rwa [h2] at this
  have hαα' : α ≠ z' • α := fun h => h1 h.symm
  have hδα' : δ ≠ z' • α := fun h => hαδ (MulAction.injective z'
    (show z' • α = z' • δ by rw [h3]; exact h.symm))
  obtain ⟨hp, hc12, -, -⟩ := three_labels F C.cinv C.val hvβ C.f2 hβα hβδ hβα' hαδ hαα' hδα'
  rw [Lb_self C.cinv] at hp hc12
  have hw1 : Lb z α δ = lab T z 1 := by
    have h := lab_eq_Lb C 1
    rwa [show a + 1 + 2 * 1 = a + 3 by ring, eq_comm] at h
  have hz2 : z * z = 1 := C.cinv.2.1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hw1inv : (lab T z 1)⁻¹ = lab T z 1 := by
    have := (lab_one_cinv F C).2.1
    exact inv_eq_of_mul_eq_one_right this
  have hzz : Lb z α (z' • α) = z' * z * z'⁻¹ := by
    have h := Lb_conj C.cinv ⟨1, one_smul G α⟩ z'
    rw [Lb_self C.cinv] at h
    exact h.symm
  rw [hw1] at hp hc12
  have hzz' : Lb z α (z' • α) = lab T z 1 * z := by
    rw [eq_inv_of_mul_eq_one_right hp, mul_inv_rev, hw1inv, hzinv]
  rw [fcomm_eq hz2 hz'2, ← hzz, hzz', ← mul_assoc, hc12, mul_assoc, hz2, mul_one]

end P515

end CFSG.Quasithin.Fan86
