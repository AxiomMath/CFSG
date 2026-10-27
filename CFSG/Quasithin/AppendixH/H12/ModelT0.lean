module

public import CFSG.Quasithin.AppendixH.H12.ModelOrbit
public import CFSG.Certificates.Kernel.J4.ModelsSound

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsIsoPoint)

theorem isSylowIn_T0 : IsSylowIn 2 T0 G0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowIn_of_card_eq T0_le_G ?_
  rw [card_T0, show Nat.card G0 = 1330560 from card_G]
  have hf : (1330560 : ℕ).factorization 2 = 7 := by decide +kernel
  rw [hf]
  norm_num

theorem gmv_T0_five {t : Γ12} (ht : t ∈ T0) : gmv t 5 = 5 := by
  have h : t ∈ vecStab 5 := by
    rw [vecStab_five]
    exact T0_le_S0 ht
  exact ((mem_vecStab_iff (by norm_num) t).mp h).2

theorem T0_le_vecStab_five : T0 ≤ vecStab 5 := by
  rw [vecStab_five]
  exact T0_le_S0

theorem T0_stable_ptSub_five :
    ∀ t ∈ T0, ∀ x ∈ ptSub 5, glHom t x ∈ ptSub 5 := by
  intro t ht x hx
  have hsmul : smulSub t (ptSub 5) = ptSub 5 := by
    rw [smulSub_ptSub (T0_le_G ht) (by norm_num), gmv_T0_five ht]
  rw [← hsmul]
  exact Subgroup.mem_map_of_mem (glHom t).toMonoidHom hx

set_option maxRecDepth 200000 in
theorem tG_stable_forces :
    ∀ c < 4096, 0 < c → quadN 12 Qcols c = false →
      (∀ g ∈ tG, mvN g c = 0 ∨ mvN g c ∈ lineOf c) → c ∈ lineOf 5 := by
  intro c hc hc0 hq hstab
  have hcheck : (List.range 4096).all (fun d => d == 0 || quadN 12 Qcols d ||
      !(tG.all fun g => mvN g d == 0 || (lineOf d).contains (mvN g d)) ||
      (lineOf 5).contains d) = true := by decide +kernel
  have hall : (tG.all fun g => mvN g c == 0 || (lineOf c).contains (mvN g c)) = true := by
    rw [List.all_eq_true]
    intro g hg
    rcases hstab g hg with h | h
    · rw [h]; simp
    · have hcont : (lineOf c).contains (mvN g c) = true := List.contains_iff_mem.mpr h
      rw [hcont]; simp
  have hcne : (c == 0) = false := by
    cases h : c == 0 with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp h) (ne_of_gt hc0)
  have hc' := (List.all_eq_true.mp hcheck) c (List.mem_range.mpr hc)
  rw [hcne, hq, hall] at hc'
  simp only [Bool.not_true, Bool.false_or, Bool.or_false] at hc'
  exact List.contains_iff_mem.mp hc'

theorem unique_T0_stable_isoPoint {P : Subgroup Vec12}
    (hP : IsIsoPoint ι0 f0 P) (hstab : ∀ t ∈ T0, ∀ x ∈ P, glHom t x ∈ P) : P = ptSub 5 := by
  obtain ⟨c, hc0, hc, hq, hPc⟩ := (isIsoPoint_iff P).mp hP
  rw [hPc] at hstab ⊢
  have hvalid : ∀ g ∈ tG, ValidN 12 g := tG_validN
  have hstab' : ∀ g ∈ tG, mvN g c = 0 ∨ mvN g c ∈ lineOf c := by
    intro g hg
    obtain ⟨u, hu_val⟩ := tG_unit g hg
    have huT0 : u ∈ T0 := mem_genSubN_of_mem hvalid hg hu_val
    have hdc : dc c ∈ ptSub c :=
      (mem_ptSub_iff hc (dc c)).mpr (Or.inr (by rw [cd_dc hc]; simp [lineOf]))
    have hmem := hstab u huT0 (dc c) hdc
    rw [glHom_dc] at hmem
    rw [hu_val] at hmem
    rw [colsN_decN (hvalid g hg)] at hmem
    have hmem' := (mem_ptSub_iff hc (dc (mvN g c))).mp hmem
    have hlt : mvN g c < 4096 := by simpa using mvN_lt (hvalid g hg).2 c
    rwa [cd_dc hlt] at hmem'
  have hline : c ∈ lineOf 5 := tG_stable_forces c hc hc0 hq hstab'
  exact (ptSub_eq_of_mem (c := 5) (d := c) (by norm_num) (by norm_num) hline).symm

theorem clause5_core :
    IsIsoPoint ι0 f0 (ptSub 5) ∧ (∀ t ∈ T0, ∀ x ∈ ptSub 5, glHom t x ∈ ptSub 5) ∧
      ∀ P : Subgroup Vec12, IsIsoPoint ι0 f0 P → (∀ t ∈ T0, ∀ x ∈ P, glHom t x ∈ P) →
        P = ptSub 5 := by
  exact ⟨isIsoPoint_five, T0_stable_ptSub_five,
    fun P hP hstab => unique_T0_stable_isoPoint hP hstab⟩

set_option maxRecDepth 200000 in
theorem fixV_T0_le :
    CFSG.Quasithin.fixV (T0.map glHom) ≤ ptSub 5 := by
  intro v hv
  rw [CFSG.Quasithin.mem_fixV] at hv
  have hc : cd v < 4096 := cd_lt v
  have hvalid : ∀ g ∈ tG, ValidN 12 g := tG_validN
  have hgen : ∀ g ∈ tG, mvN g (cd v) = cd v := by
    intro g hg
    obtain ⟨u, hu_val⟩ := tG_unit g hg
    have huT0 : u ∈ T0 := mem_genSubN_of_mem hvalid hg hu_val
    have hfix := hv (glHom u) (show glHom u ∈ T0.map glHom from ⟨u, huT0, rfl⟩)
    rw [← dc_cd v] at hfix
    have hgl : glHom u (dc (cd v)) =
        dc (mvN (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) (cd v)) :=
      glHom_dc u (cd v)
    have hgmv : dc (mvN (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) (cd v)) = dc (cd v) := by
      rw [← hgl]
      exact hfix
    have hmv : mvN (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) (cd v) = cd v :=
      dc_inj (by simpa using mvN_lt (validN_colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))).2 (cd v))
        (by simpa using hc) hgmv
    rw [hu_val] at hmv
    rwa [colsN_decN (hvalid g hg)] at hmv
  have hall : (tG.all fun g => mvN g (cd v) == cd v) = true := by
    rw [List.all_eq_true]
    intro g hg
    exact beq_iff_eq.mpr (hgen g hg)
  have hcheck : (List.range 4096).all (fun d => d == 0 ||
      !(tG.all fun g => mvN g d == d) || (lineOf 5).contains d) = true := by decide +kernel
  have hc' := (List.all_eq_true.mp hcheck) (cd v) (List.mem_range.mpr hc)
  rw [hall] at hc'
  simp only [Bool.not_true, Bool.false_or, Bool.or_false, Bool.or_eq_true] at hc'
  rw [← dc_cd v]
  rcases hc' with h0 | hline
  · rw [beq_iff_eq.mp h0, dc_zero]
    exact Subgroup.one_mem _
  · have hlin : cd v ∈ lineOf 5 := List.contains_iff_mem.mp hline
    rw [ptSub_eq_of_mem (c := 5) (d := cd v) (by norm_num) (by norm_num) hlin]
    exact (mem_ptSub_iff hc (dc (cd v))).mpr (Or.inr (by rw [cd_dc hc]; simp [lineOf]))

end CFSG.Quasithin.AppendixH.H12.Model
