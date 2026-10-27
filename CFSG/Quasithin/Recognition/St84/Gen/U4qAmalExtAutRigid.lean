module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointModel
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLine
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtAutCocycle
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointAux

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem xc_yc_conj_mul_levHom_mul_u4 {r d w : hypSU h 2 0} (hr : r ∈ radQ h)
    (hd : d ∈ u4PtTorus h) (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) {x y c : K}
    (hw : ((w : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    xc (r * levHom h A * d * w * (r * levHom h A * d)⁻¹) =
        slMat h A 0 0 * (u4PtKappaVal h d * x) + slMat h A 0 1 * (u4PtKappaVal h d * y) ∧
      yc (r * levHom h A * d * w * (r * levHom h A * d)⁻¹) =
        slMat h A 1 0 * (u4PtKappaVal h d * x) + slMat h A 1 1 * (u4PtKappaVal h d * y) := by
  have := h.charP
  have key : ∀ a b : K, a + b + a = b := fun a b => by
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  have e : r * levHom h A * d * w * (r * levHom h A * d)⁻¹ =
      r * (levHom h A * (d * w * d⁻¹) * (levHom h A)⁻¹) * r⁻¹ := by group
  obtain ⟨a, b, c', hc', hrm⟩ := hr
  have hm := coe_mul_of (coe_mul_of hrm
    (coe_conj_levHom h (coe_conj_sMat_of_mem_u4PtTorus h hd hw) A)) (coe_inv_of_sMat hc' hrm)
  rw [e, xc_of hm, yc_of hm]
  exact ⟨key _ _, key _ _⟩

theorem parP_inf_centralizer_radQ_le_zRad_u4 :
    parP h ⊓ Subgroup.centralizer (radQ h : Set (hypSU h 2 0)) ≤ zRad h := by
  have := h.charP
  rintro g ⟨hgP, hgC⟩
  have hgc : ∀ w ∈ radQ h, g * w * g⁻¹ = w := fun w hw => by
    rw [(Subgroup.mem_centralizer_iff.mp hgC w hw).symm, mul_inv_cancel_right]
  obtain ⟨r, hr, A, d, hd, rfl⟩ := exists_eq_mul_levHom_mul_of_mem_parP h hgP
  have hX := xc_yc_conj_mul_levHom_mul_u4 h hr hd A (coe_sxElt (h := h) 1)
  have hY := xc_yc_conj_mul_levHom_mul_u4 h hr hd A (coe_syElt (h := h) 1)
  rw [hgc _ (sxElt_mem 1), xc_of (coe_sxElt 1), yc_of (coe_sxElt 1)] at hX
  rw [hgc _ (syElt_mem 1), xc_of (coe_syElt 1), yc_of (coe_syElt 1)] at hY
  simp only [mul_one, mul_zero, add_zero, zero_add] at hX hY
  obtain ⟨h00, h10⟩ := hX
  obtain ⟨h01, h11⟩ := hY
  have hκ0 : u4PtKappaVal h d ≠ 0 := u4PtKappaVal_ne_zero h hd
  have hA10 : slMat h A 1 0 = 0 := (mul_eq_zero.mp h10.symm).resolve_right hκ0
  have hA01 : slMat h A 0 1 = 0 := (mul_eq_zero.mp h01.symm).resolve_right hκ0
  have hdet := det_slMat h A
  rw [Matrix.det_fin_two, hA10, hA01, mul_zero, sub_zero] at hdet
  have hκ1 : u4PtKappaVal h d = 1 := by
    have e1 : u4PtKappaVal h d * u4PtKappaVal h d = 1 :=
      calc u4PtKappaVal h d * u4PtKappaVal h d
          = (slMat h A 0 0 * slMat h A 1 1) * (u4PtKappaVal h d * u4PtKappaVal h d) := by
            rw [hdet, one_mul]
        _ = (slMat h A 0 0 * u4PtKappaVal h d) * (slMat h A 1 1 * u4PtKappaVal h d) := by ring
        _ = 1 := by rw [← h00, ← h11, one_mul]
    exact CharTwo.sq_inj.mp (by rw [one_pow, sq]; exact e1)
  have h00' : slMat h A 0 0 = 1 := by
    rw [hκ1, mul_one] at h00
    exact h00.symm
  have h11' : slMat h A 1 1 = 1 := by
    rw [hκ1, mul_one] at h11
    exact h11.symm
  have hA : A = 1 := by
    have e1 : slMat h A = slMat h 1 := by
      rw [slMat_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00', h11', hA01, hA10]
    exact Subtype.ext (Matrix.map_injective h.fixedField.subtype_injective e1)
  have hd1 : d = 1 := by
    have e1 : u4PtKappa h ⟨d, hd⟩ = 1 := Units.ext (by rw [coe_u4PtKappa]; exact hκ1)
    exact congrArg Subtype.val ((u4PtKappa_injective h) (e1.trans (map_one _).symm))
  subst hA hd1
  rw [map_one, mul_one, mul_one] at hgc ⊢
  refine (mem_zRad_iff_comm h).mpr ⟨hr, fun x hx => ?_⟩
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [hgc x hx]

private theorem exists_fixed_ne_u4ExtAut (hm : 2 ≤ m) :
    ∃ l : K, h.bar l = l ∧ l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have := h.finite
  have hsurj : Function.Surjective
      (fun b : Bool => (if b then 1 else 0 : h.fixedField)) := by
    rintro ⟨l, hl⟩
    by_cases h0 : l = 0
    · exact ⟨false, Subtype.ext (by simp [h0])⟩
    · exact ⟨true, Subtype.ext (by simp [hcon l ((h.mem_fixedField).mp hl) h0])⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, h.card_fixedField] at hle
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

include h in
private theorem ne_inv_u4ExtAut {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) : l ≠ l⁻¹ := by
  have := h.charP
  intro e
  apply hl1
  have e2 : l ^ 2 = 1 ^ 2 := by
    rw [sq, one_pow]
    nth_rewrite 2 [e]
    exact mul_inv_cancel₀ hl0
  exact CharTwo.sq_inj.mp e2

private theorem eq_one_of_mem_zRad_comm_u4ExtAut (hm : 2 ≤ m) {v : hypSU h 2 0}
    (hv : v ∈ zRad h) (hc : ∀ b ∈ parP h ⊓ parP2 h, b * v = v * b) : v = 1 := by
  have hmem : v ∈ radQ h ⊓ Subgroup.centralizer (u4PtTorus h : Set (hypSU h 2 0)) :=
    ⟨zRad_le_radQ h hv, Subgroup.mem_centralizer_iff.mpr fun d hd =>
      hc d (u4PtTorus_le_inf h hd)⟩
  rw [radQ_inf_centralizer_u4PtTorus h hm] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem eq_one_of_mem_radQ2_comm_u4ExtAut (hm : 2 ≤ m) {v : hypSU h 2 0}
    (hv : v ∈ radQ2 h) (hc : ∀ b ∈ parP h ⊓ parP2 h, b * v = v * b) : v = 1 := by
  obtain ⟨l, hl, hl0, hl1⟩ := exists_fixed_ne_u4ExtAut h hm
  have hll : l ≠ l⁻¹ := ne_inv_u4ExtAut h hl0 hl1
  obtain ⟨d₁, hd₁, q₁, hq₁, e11, -, e13, e14⟩ :=
    exists_mem_hypTorus_u4 h hl0 one_ne_zero (by rw [mul_one]; exact hl)
  obtain ⟨d₂, hd₂, q₂, hq₂, -, e22, e23, e24⟩ :=
    exists_mem_hypTorus_u4 h one_ne_zero hl0 (by rw [one_mul]; exact hl)
  have H₁ := (comm_diag_iff_u4 h hq₁).mp (hc d₁ (hypTorus_le_inf_u4 h hd₁))
  have H₂ := (comm_diag_iff_u4 h hq₂).mp (hc d₂ (hypTorus_le_inf_u4 h hd₂))
  rw [hl] at e13 e24
  rw [map_one, inv_one] at e14 e23
  have v11 : ((v : GL Ix K) : Matrix Ix Ix K) ie1 if1 = 0 := by
    have e := H₁ ie1 if1
    rw [e11, e13] at e
    have e' : (l - l⁻¹) * ((v : GL Ix K) : Matrix Ix Ix K) ie1 if1 = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hll)
  have v12 : ((v : GL Ix K) : Matrix Ix Ix K) ie1 if2 = 0 := by
    have e := H₁ ie1 if2
    rw [e11, e14] at e
    have e' : (l - 1) * ((v : GL Ix K) : Matrix Ix Ix K) ie1 if2 = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hl1)
  have v21 : ((v : GL Ix K) : Matrix Ix Ix K) ie2 if1 = 0 := by
    have e := H₂ ie2 if1
    rw [e22, e23] at e
    have e' : (l - 1) * ((v : GL Ix K) : Matrix Ix Ix K) ie2 if1 = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hl1)
  have v22 : ((v : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 := by
    have e := H₂ ie2 if2
    rw [e22, e24] at e
    have e' : (l - l⁻¹) * ((v : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hll)
  refine u4LineBlk_inj h hv (radQ2 h).one_mem ?_
  rw [u4LineBlk_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4LineBlk, v11, v12, v21, v22]

private theorem odd_relIndex_inf_u4ExtAut {X : Subgroup (hypSU h 2 0)}
    (hUX : hypUnitriangular h 2 0 ≤ X) : Odd ((parP h ⊓ parP2 h).relIndex X) := by
  have h1 : ¬ 2 ∣ (hypUnitriangular h 2 0).index := by
    have := (isSylowTwoOf_hypUnitriangular h).2.2
    rwa [show ((hypUnitriangular h 2 0).subgroupOf ⊤).index = (hypUnitriangular h 2 0).index from
      Subgroup.relIndex_top_right _] at this
  have h2 : (parP h ⊓ parP2 h).relIndex X ∣ (hypUnitriangular h 2 0).index :=
    (Subgroup.relIndex_dvd_of_le_left X (hypUnitriangular_le_inf_u4 h)).trans
      (Subgroup.relIndex_dvd_index_of_le hUX)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h3 => h1 (h3.trans h2))

theorem eq_one_of_forall_fix_inf_parP_u4 (hm : 2 ≤ m) (α : MulAut ↥(parP h))
    (hα : ∀ x : ↥(parP h), (x : hypSU h 2 0) ∈ parP h ⊓ parP2 h → α x = x) : α = 1 :=
  eq_one_of_forall_fix_of_odd_relIndex inf_le_left
    (odd_relIndex_inf_u4ExtAut h ((hypUnitriangular_le_inf_u4 h).trans inf_le_left))
    (radQ_le_inf_u4 h)
    (fun p hp r hr => (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h hp) r).mp hr)
    (fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (zRad_le_centralizer h ha) b (zRad_le_radQ h hb)).symm)
    (fun v hv => by
      have := h.charP
      obtain ⟨c, -, hvc⟩ := hv
      apply hypSU_ext h
      rw [coe_mul_hypSU, hvc, sMat_mul]
      simp only [add_zero, map_zero, zero_mul, CharTwo.add_self_eq_zero]
      rw [sMat_zero_u4]
      rfl)
    (fun p hp v hv => conj_mem_zRad_of_mem_normalizer h p (parP_le_normalizer_radQ h hp) v hv)
    (parP_inf_centralizer_radQ_le_zRad_u4 h)
    (fun _ hv hc => eq_one_of_mem_zRad_comm_u4ExtAut h hm hv hc) α hα

theorem eq_one_of_forall_fix_inf_parP2_u4 (hm : 2 ≤ m) (α : MulAut ↥(parP2 h))
    (hα : ∀ x : ↥(parP2 h), (x : hypSU h 2 0) ∈ parP h ⊓ parP2 h → α x = x) : α = 1 :=
  eq_one_of_forall_fix_of_odd_relIndex inf_le_right
    (odd_relIndex_inf_u4ExtAut h ((hypUnitriangular_le_inf_u4 h).trans inf_le_right))
    (radQ2_le_inf_u4 h)
    (fun p hp r hr => (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h hp) r).mp hr)
    (fun a ha b hb => radQ2_comm h ha hb)
    (fun v hv => by
      have := h.charP
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hv
      apply hypSU_ext h
      rw [coe_mul_hypSU]
      ext i j
      rw [Matrix.mul_apply, sum_ix]
      rcases ix_cases i with rfl | rfl | rfl | rfl <;>
        rcases ix_cases j with rfl | rfl | rfl | rfl <;>
        simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, one_apply,
          CharTwo.add_self_eq_zero])
    (fun p hp v hv => (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h hp) v).mp hv)
    (parP2_inf_centralizer_radQ2_le h)
    (fun _ hv hc => eq_one_of_mem_radQ2_comm_u4ExtAut h hm hv hc) α hα

end CFSG.Quasithin.F112R.St84

end
