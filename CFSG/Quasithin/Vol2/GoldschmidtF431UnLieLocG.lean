module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem miyamotoXGL_zero_eq_one : miyamotoXGL h 0 0 0 0 = 1 :=
  Units.ext (by simp [coe_miyamotoXGL, miyamotoX_zero])

theorem ZX_le_Vx : ZX h ≤ Vx h := by
  intro x hx
  obtain ⟨d, hd, hxd⟩ := (mem_Z h).1 (Subgroup.mem_subgroupOf.1 hx)
  refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩ <;> rw [hxd]
  · exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩
  · exact (miyamotoXGL_mem_Cu h).2 ⟨map_zero _, map_zero _, map_zero _, hd⟩

@[expose] def zEl {d : K} (hd : h.bar d = d) : Xg h :=
  ⟨miyamotoXGL h 0 0 0 d,
    miyamotoUnipotent_le_SU h true false ((miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩)⟩

theorem zEl_mem {d : K} (hd : h.bar d = d) : zEl h hd ∈ ZX h :=
  Subgroup.mem_subgroupOf.2 ((mem_Z h).2 ⟨d, hd, rfl⟩)

theorem ZX_two (hf : 2 ≤ f) : ∃ a ∈ ZX h, ∃ b ∈ ZX h, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨t, htF, ht⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht1 : (t : K) ≠ 1 := fun e => ht (by rw [e, one_pow])
  have h1 : h.bar (1 : K) = 1 := map_one _
  refine ⟨zEl h h1, zEl_mem h h1, zEl h htF, zEl_mem h htF, ?_, ?_, ?_⟩
  · intro e
    have := congrArg (fun y : Xg h => ((y : GL (Fin 4) K))) e
    simp only [zEl, OneMemClass.coe_one] at this
    rw [← miyamotoXGL_zero_eq_one h, miyamotoXGL_inj] at this
    exact one_ne_zero this.2.2.2
  · intro e
    have := congrArg (fun y : Xg h => ((y : GL (Fin 4) K))) e
    simp only [zEl, OneMemClass.coe_one] at this
    rw [← miyamotoXGL_zero_eq_one h, miyamotoXGL_inj] at this
    exact t.ne_zero this.2.2.2
  · intro e
    have := congrArg (fun y : Xg h => ((y : GL (Fin 4) K))) e
    simp only [zEl] at this
    rw [miyamotoXGL_inj] at this
    exact ht1 this.2.2.2.symm

theorem ZX_cls {r : Xg h} (hr : r ∈ ZX h) (hr1 : r ≠ 1) :
    ∃ x ∈ Cx h, r = x * z1X h * x⁻¹ := by
  obtain ⟨d, hd, hrd⟩ := (mem_Z h).1 (Subgroup.mem_subgroupOf.1 hr)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hr1 (Subtype.ext (by rw [hrd, miyamotoXGL_zero_eq_one]; rfl))
  obtain ⟨p, hp, hpp⟩ := exists_sqrt_fixed h hd
  have hp0 : p ≠ 0 := fun e => hd0 (by rw [← hpp, e, mul_zero])
  obtain ⟨s, hs, hsz⟩ := exists_conj_z1 h hp (map_zero _) (Or.inl hp0)
  refine ⟨s, hs, Subtype.ext ?_⟩
  show (r : GL (Fin 4) K) = (s : GL (Fin 4) K) * ((z1X h : Xg h) : GL (Fin 4) K) *
    (s : GL (Fin 4) K)⁻¹
  rw [hsz, hrd, hpp]
  simp

theorem ZX_inf_Ux {r : Xg h} (hr : r ∈ ZX h) (hU : r ∈ Ux h) : r = 1 := by
  obtain ⟨d, hd, hrd⟩ := (mem_Z h).1 (Subgroup.mem_subgroupOf.1 hr)
  obtain ⟨c, hc, hrc⟩ := Subgroup.mem_subgroupOf.1 hU
  rw [hrd, miyamotoXGL_inj] at hrc
  have hd0 : d = 0 := hrc.2.2.2
  exact Subtype.ext (by rw [hrd, hd0, miyamotoXGL_zero_eq_one]; rfl)

theorem Psy_cent_z1 {y : Xg h} (hy : y ∈ Psy h) : y * z1X h = z1X h * y := by
  obtain ⟨a, b, c, d, hb, -, hya⟩ := (mem_P h).1 (Subgroup.mem_subgroupOf.1 hy)
  apply Subtype.ext
  show (y : GL (Fin 4) K) * ((z1X h : Xg h) : GL (Fin 4) K) =
    ((z1X h : Xg h) : GL (Fin 4) K) * (y : GL (Fin 4) K)
  rw [coe_z1X, hya, miyamotoXGL_mul h hb, miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  exact ⟨by simp, by simp, by simp, by simp [add_comm]⟩

end CFSG.Quasithin.H13.F431.Un.LL
