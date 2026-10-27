module

public import CFSG.Quasithin.Recognition.St84.G24ModelFrameFacts
public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Quasithin.KGC31 (eElt eElt_add eElt_zero)
open scoped commutatorElement


private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hle : a.val = 0 ∨ a.val = 1 := by omega
  rcases hle with h | h
  · exact Or.inl ((ZMod.val_eq_zero a).1 h)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num) a).1 h)

private theorem pow_val_eq_if (y : Y) (a : ZMod 2) :
    y ^ a.val = if a = 1 then y else 1 := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [show (0 : ZMod 2).val = 0 from (ZMod.val_eq_zero _).2 rfl]
    simp
  · rw [show (1 : ZMod 2).val = 1 from (ZMod.val_eq_one (by norm_num) _).2 rfl]
    simp

private def zWord {d : Nat} (off : Fin d → Fin 10) (c : Fin d → ZMod 2) :
    List (Fin 10 × Bool) :=
  (List.ofFn fun t => if c t = 1 then [(off t, false)] else []).flatten

private theorem signedProd_zWord {d : Nat} {z : Fin 10 → Y}
    (off : Fin d → Fin 10) (hz2 : ∀ t : Fin d, z (off t) * z (off t) = 1)
    (c : Fin d → ZMod 2) :
    CFSG.Certificates.signedProd z (zWord off c) = eElt (fun t => z (off t)) c := by
  have hletter : ∀ t : Fin d,
      CFSG.Certificates.signedProd z (if c t = 1 then [(off t, false)] else [])
        = z (off t) ^ (c t).val := by
    intro t
    rw [pow_val_eq_if]
    by_cases h : c t = 1
    · rw [if_pos h, if_pos h, CFSG.Certificates.signedProd]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
        mul_one]
      exact inv_eq_of_mul_eq_one_right (hz2 t)
    · rw [if_neg h, if_neg h, CFSG.Certificates.signedProd]
      simp
  unfold zWord
  rw [CFSG.Certificates.signedProd, List.map_flatten, List.prod_flatten, List.map_map,
    List.map_ofFn]
  rw [eElt, List.ofFn_eq_map, List.ofFn_eq_map]
  congr 1
  apply List.map_congr_left
  intro t _
  exact hletter t

private theorem eElt_mul_self {d : Nat} {z : Fin d → Y}
    (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s))
    (c : Fin d → ZMod 2) : eElt z c * eElt z c = 1 := by
  have h := eElt_add hz2 hzz c c
  have hcc : c + c = 0 := funext fun t => CharTwo.add_self_eq_zero (c t)
  rw [hcc, eElt_zero] at h
  exact h.symm

private theorem signedProd_pc1_coe (w : List (Fin 10 × Bool)) :
    ((CFSG.Certificates.signedProd pc1Q w : ↥Q1) : Y) =
      CFSG.Certificates.signedProd pc1Y w := by
  simpa [pc1Q] using CFSG.Certificates.map_signedProd (Subgroup.subtype Q1) pc1Q w

private theorem signedProd_pc2_coe (w : List (Fin 10 × Bool)) :
    ((CFSG.Certificates.signedProd pc2Q w : ↥Q2) : Y) =
      CFSG.Certificates.signedProd pc2Y w := by
  simpa [pc2Q] using CFSG.Certificates.map_signedProd (Subgroup.subtype Q2) pc2Q w

private theorem signedProd_pc1Y_of_mem (hM : Facts) {w : List (Fin 10 × Bool)}
    (hw : w ∈ CFSG.Quasithin.St84.G24Pc.relsQ1) :
    CFSG.Certificates.signedProd pc1Y w = 1 := by
  have h := congrArg (Subgroup.subtype Q1) (hM.rels_pc1Q w hw)
  change ((CFSG.Certificates.signedProd pc1Q w : ↥Q1) : Y) = ((1 : ↥Q1) : Y) at h
  rw [signedProd_pc1_coe] at h
  simpa using h

private theorem signedProd_pc2Y_of_mem (hM : Facts) {w : List (Fin 10 × Bool)}
    (hw : w ∈ CFSG.Quasithin.St84.G24Pc.relsQ2) :
    CFSG.Certificates.signedProd pc2Y w = 1 := by
  have h := congrArg (Subgroup.subtype Q2) (hM.rels_pc2Q w hw)
  change ((CFSG.Certificates.signedProd pc2Q w : ↥Q2) : Y) = ((1 : ↥Q2) : Y) at h
  rw [signedProd_pc2_coe] at h
  simpa using h

private theorem zb1_mem (hM : Facts) (t : Fin 2) : zb1 t ∈ Z1 := by
  fin_cases t <;> rw [hM.Z1_eq] <;> exact Subgroup.subset_closure (by simp [zb1])

private theorem zb2_mem (hM : Facts) (t : Fin 4) : zb2 t ∈ Z2 := by
  fin_cases t <;> rw [hM.Z2_eq] <;> exact Subgroup.subset_closure (by simp [zb2])

private theorem zb1_sq (hM : Facts) (t : Fin 2) : zb1 t * zb1 t = 1 := by
  simpa [pow_two] using hM.sq_Z1 (zb1 t) (zb1_mem hM t)

private theorem zb2_sq (hM : Facts) (t : Fin 4) : zb2 t * zb2 t = 1 := by
  simpa [pow_two] using hM.sq_Z2 (zb2 t) (zb2_mem hM t)

private theorem zb1_comm (hM : Facts) (t s : Fin 2) : Commute (zb1 t) (zb1 s) :=
  Subgroup.mem_centralizer_iff.mp (zb1_mem hM s).2 (zb1 t) (zb1_mem hM t).1

private theorem zb2_comm (hM : Facts) (t s : Fin 4) : Commute (zb2 t) (zb2 s) :=
  Subgroup.mem_centralizer_iff.mp (zb2_mem hM s).2 (zb2 t) (zb2_mem hM t).1

private def sqRel1 (i : Fin 8) : List (Fin 10 × Bool) :=
  [(Fin.castAdd 2 i, true), (Fin.castAdd 2 i, true)] ++
    zWord (Fin.natAdd 8) (CFSG.Quasithin.St84.G24MF.sqV1 i)

private def cmRel1 (i j : Fin 8) : List (Fin 10 × Bool) :=
  [(Fin.castAdd 2 j, true), (Fin.castAdd 2 i, true), (Fin.castAdd 2 j, false),
    (Fin.castAdd 2 i, false)] ++
    zWord (Fin.natAdd 8) (CFSG.Quasithin.St84.G24MF.cmV1 i j)

private def sqRel2 (i : Fin 6) : List (Fin 10 × Bool) :=
  [(Fin.castAdd 4 i, true), (Fin.castAdd 4 i, true)] ++
    zWord (Fin.natAdd 6) (CFSG.Quasithin.St84.G24MF.sqV2 i)

private def cmRel2 (i j : Fin 6) : List (Fin 10 × Bool) :=
  [(Fin.castAdd 4 j, true), (Fin.castAdd 4 i, true), (Fin.castAdd 4 j, false),
    (Fin.castAdd 4 i, false)] ++
    zWord (Fin.natAdd 6) (CFSG.Quasithin.St84.G24MF.cmV2 i j)

private theorem sqRel1_mem (i : Fin 8) :
    sqRel1 i ∈ CFSG.Quasithin.St84.G24Pc.relsQ1 := by
  fin_cases i <;> decide

private theorem cmRel1_mem {i j : Fin 8} (hij : i < j) :
    cmRel1 i j ∈ CFSG.Quasithin.St84.G24Pc.relsQ1 := by
  fin_cases i <;> fin_cases j <;> first | decide | exact absurd hij (by decide)

private theorem sqRel2_mem (i : Fin 6) :
    sqRel2 i ∈ CFSG.Quasithin.St84.G24Pc.relsQ2 := by
  fin_cases i <;> decide

private theorem cmRel2_mem {i j : Fin 6} (hij : i < j) :
    cmRel2 i j ∈ CFSG.Quasithin.St84.G24Pc.relsQ2 := by
  fin_cases i <;> fin_cases j <;> first | decide | exact absurd hij (by decide)

private theorem signedProd_sqRel1 (hM : Facts) (i : Fin 8) :
    CFSG.Certificates.signedProd pc1Y (sqRel1 i) =
      frame1 i * frame1 i * eElt zb1 (CFSG.Quasithin.St84.G24MF.sqV1 i) := by
  have hz := signedProd_zWord (z := pc1Y) (d := 2) (off := Fin.natAdd 8)
    (fun t => by simpa [zb1] using zb1_sq hM t)
    (CFSG.Quasithin.St84.G24MF.sqV1 i)
  unfold sqRel1
  rw [CFSG.Certificates.signedProd_append, hz]
  congr 1

private theorem signedProd_cmRel1 (hM : Facts) {i j : Fin 8} (hij : i < j) :
    CFSG.Certificates.signedProd pc1Y (cmRel1 i j) =
      frame1 j * frame1 i * (frame1 j)⁻¹ * (frame1 i)⁻¹ *
        eElt zb1 (CFSG.Quasithin.St84.G24MF.cmV1 i j) := by
  have hz := signedProd_zWord (z := pc1Y) (d := 2) (off := Fin.natAdd 8)
    (fun t => by simpa [zb1] using zb1_sq hM t)
    (CFSG.Quasithin.St84.G24MF.cmV1 i j)
  unfold cmRel1
  rw [CFSG.Certificates.signedProd_append, hz]
  congr 1

private theorem signedProd_sqRel2 (hM : Facts) (i : Fin 6) :
    CFSG.Certificates.signedProd pc2Y (sqRel2 i) =
      frame2 i * frame2 i * eElt zb2 (CFSG.Quasithin.St84.G24MF.sqV2 i) := by
  have hz := signedProd_zWord (z := pc2Y) (d := 4) (off := Fin.natAdd 6)
    (fun t => by simpa [zb2] using zb2_sq hM t)
    (CFSG.Quasithin.St84.G24MF.sqV2 i)
  unfold sqRel2
  rw [CFSG.Certificates.signedProd_append, hz]
  congr 1

private theorem signedProd_cmRel2 (hM : Facts) {i j : Fin 6} (hij : i < j) :
    CFSG.Certificates.signedProd pc2Y (cmRel2 i j) =
      frame2 j * frame2 i * (frame2 j)⁻¹ * (frame2 i)⁻¹ *
        eElt zb2 (CFSG.Quasithin.St84.G24MF.cmV2 i j) := by
  have hz := signedProd_zWord (z := pc2Y) (d := 4) (off := Fin.natAdd 6)
    (fun t => by simpa [zb2] using zb2_sq hM t)
    (CFSG.Quasithin.St84.G24MF.cmV2 i j)
  unfold cmRel2
  rw [CFSG.Certificates.signedProd_append, hz]
  congr 1

theorem sq_frame1 (hM : Facts) (i : Fin 8) :
    frame1 i ^ 2 = eElt zb1 (CFSG.Quasithin.St84.G24MF.sqV1 i) := by
  have h1 := signedProd_pc1Y_of_mem hM (sqRel1_mem i)
  have h2 := signedProd_sqRel1 hM i
  have hZ := eElt_mul_self (z := zb1) (fun t => zb1_sq hM t) (zb1_comm hM)
    (CFSG.Quasithin.St84.G24MF.sqV1 i)
  rw [h1] at h2
  rw [pow_two]
  calc frame1 i * frame1 i
      = (eElt zb1 (CFSG.Quasithin.St84.G24MF.sqV1 i))⁻¹ :=
        eq_inv_of_mul_eq_one_left h2.symm
    _ = eElt zb1 (CFSG.Quasithin.St84.G24MF.sqV1 i) := inv_eq_of_mul_eq_one_right hZ

theorem comm_frame1 (hM : Facts) {i j : Fin 8} (hij : i < j) :
    ⁅frame1 j, frame1 i⁆ = eElt zb1 (CFSG.Quasithin.St84.G24MF.cmV1 i j) := by
  have h1 := signedProd_pc1Y_of_mem hM (cmRel1_mem hij)
  have h2 := signedProd_cmRel1 hM hij
  have hZ := eElt_mul_self (z := zb1) (fun t => zb1_sq hM t) (zb1_comm hM)
    (CFSG.Quasithin.St84.G24MF.cmV1 i j)
  rw [h1] at h2
  have hcm : frame1 j * frame1 i * (frame1 j)⁻¹ * (frame1 i)⁻¹ = ⁅frame1 j, frame1 i⁆ := by
    rw [commutatorElement_def]
  rw [hcm] at h2
  calc ⁅frame1 j, frame1 i⁆ = (eElt zb1 (CFSG.Quasithin.St84.G24MF.cmV1 i j))⁻¹ :=
        eq_inv_of_mul_eq_one_left h2.symm
    _ = eElt zb1 (CFSG.Quasithin.St84.G24MF.cmV1 i j) := inv_eq_of_mul_eq_one_right hZ

theorem sq_frame2 (hM : Facts) (i : Fin 6) :
    frame2 i ^ 2 = eElt zb2 (CFSG.Quasithin.St84.G24MF.sqV2 i) := by
  have h1 := signedProd_pc2Y_of_mem hM (sqRel2_mem i)
  have h2 := signedProd_sqRel2 hM i
  have hZ := eElt_mul_self (z := zb2) (fun t => zb2_sq hM t) (zb2_comm hM)
    (CFSG.Quasithin.St84.G24MF.sqV2 i)
  rw [h1] at h2
  rw [pow_two]
  calc frame2 i * frame2 i
      = (eElt zb2 (CFSG.Quasithin.St84.G24MF.sqV2 i))⁻¹ :=
        eq_inv_of_mul_eq_one_left h2.symm
    _ = eElt zb2 (CFSG.Quasithin.St84.G24MF.sqV2 i) := inv_eq_of_mul_eq_one_right hZ

theorem comm_frame2 (hM : Facts) {i j : Fin 6} (hij : i < j) :
    ⁅frame2 j, frame2 i⁆ = eElt zb2 (CFSG.Quasithin.St84.G24MF.cmV2 i j) := by
  have h1 := signedProd_pc2Y_of_mem hM (cmRel2_mem hij)
  have h2 := signedProd_cmRel2 hM hij
  have hZ := eElt_mul_self (z := zb2) (fun t => zb2_sq hM t) (zb2_comm hM)
    (CFSG.Quasithin.St84.G24MF.cmV2 i j)
  rw [h1] at h2
  have hcm : frame2 j * frame2 i * (frame2 j)⁻¹ * (frame2 i)⁻¹ = ⁅frame2 j, frame2 i⁆ := by
    rw [commutatorElement_def]
  rw [hcm] at h2
  calc ⁅frame2 j, frame2 i⁆ = (eElt zb2 (CFSG.Quasithin.St84.G24MF.cmV2 i j))⁻¹ :=
        eq_inv_of_mul_eq_one_left h2.symm
    _ = eElt zb2 (CFSG.Quasithin.St84.G24MF.cmV2 i j) := inv_eq_of_mul_eq_one_right hZ

end CFSG.Quasithin.F112R.St84.G24M
