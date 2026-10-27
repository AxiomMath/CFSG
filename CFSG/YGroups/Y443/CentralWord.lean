module

public import CFSG.YGroups.KernelCriterion
public import CFSG.YGroups.Y433.Y322Embed

public section

namespace CFSG.YGroups.Y443

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def sub322Z (c : ℕ) : ℕ := [0, 9, 10, 11, 1, 2, 5, 6].getD c 0

@[expose] def sub322F (c : ℕ) : ℕ := [0, 1, 2, 3, 5, 6, 9, 10].getD c 0

theorem pairsPreserved_sub322Z : Relabel.PairsPreserved 3 2 2 4 4 3 sub322Z := by decide

theorem pairsPreserved_sub322F : Relabel.PairsPreserved 3 2 2 4 4 3 sub322F := by decide

@[expose] noncomputable def blk1 : YGroup 4 4 3 := yGen 4 4 3 0 * yGen 4 4 3 1 * yGen 4 4 3 2

@[expose] noncomputable def blk2 : YGroup 4 4 3 := yGen 4 4 3 0 * yGen 4 4 3 5 * yGen 4 4 3 6

@[expose] noncomputable def blk3 : YGroup 4 4 3 := yGen 4 4 3 0 * yGen 4 4 3 9 * yGen 4 4 3 10

theorem spider443 : (blk1 * blk2 * blk3) ^ 10 = 1 := by
  have h := evalWord_yGen_of_mem (p := 4) (q := 4) (r := 3)
    (w := (List.replicate 10 (spiderWord 4 4)).flatten) (by
      simp only [yRels, List.mem_append]
      refine Or.inr ?_
      simp only [Nat.reduceLeDiff, and_self, ↓reduceIte, List.reduceReplicate, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false])
  rw [Y443.evalWord_replicate_flatten] at h
  rw [← h, Relabel.evalWord_spiderWord]
  rfl

theorem spider_sub322F :
    evalWord (fun c => yGen 4 4 3 (sub322F c)) (spiderWord 3 2) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 4 3 (sub322F c)) (spiderWord 3 2) = blk1 * blk2 * blk3 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact spider443

theorem spider_sub322Z :
    evalWord (fun c => yGen 4 4 3 (sub322Z c)) (spiderWord 3 2) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 4 3 (sub322Z c)) (spiderWord 3 2) = blk3 * blk1 * blk2 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact Relabel.pow_eq_one_rotate (Relabel.pow_eq_one_rotate spider443)

@[expose] noncomputable def zY : YGroup 4 4 3 :=
  (yGen 4 4 3 0 * yGen 4 4 3 9 * yGen 4 4 3 10 * yGen 4 4 3 11 * yGen 4 4 3 1 * yGen 4 4 3 2 *
    yGen 4 4 3 5) ^ 9

@[expose] noncomputable def zY' : YGroup 4 4 3 :=
  (yGen 4 4 3 0 * yGen 4 4 3 9 * yGen 4 4 3 10 * yGen 4 4 3 11 * yGen 4 4 3 5 * yGen 4 4 3 6 *
    yGen 4 4 3 1) ^ 9

@[expose] noncomputable def fY : YGroup 4 4 3 :=
  (yGen 4 4 3 0 * yGen 4 4 3 1 * yGen 4 4 3 2 * yGen 4 4 3 3 * yGen 4 4 3 5 * yGen 4 4 3 6 *
    yGen 4 4 3 9) ^ 9

@[expose] noncomputable def fY' : YGroup 4 4 3 :=
  (yGen 4 4 3 0 * yGen 4 4 3 1 * yGen 4 4 3 2 * yGen 4 4 3 3 * yGen 4 4 3 9 * yGen 4 4 3 10 *
    yGen 4 4 3 5) ^ 9

theorem evalWord_F1_Z : evalWord (fun c => yGen 4 4 3 (sub322Z c)) y322WordF1 = zY := by
  rw [y322WordF1, Y443.evalWord_replicate_flatten, zY]
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]
  rfl

theorem evalWord_F2_Z : evalWord (fun c => yGen 4 4 3 (sub322Z c)) y322WordF2 = zY' := by
  rw [y322WordF2, Y443.evalWord_replicate_flatten, zY']
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]
  rfl

theorem evalWord_F1_F : evalWord (fun c => yGen 4 4 3 (sub322F c)) y322WordF1 = fY := by
  rw [y322WordF1, Y443.evalWord_replicate_flatten, fY]
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]
  rfl

theorem evalWord_F2_F : evalWord (fun c => yGen 4 4 3 (sub322F c)) y322WordF2 = fY' := by
  rw [y322WordF2, Y443.evalWord_replicate_flatten, fY']
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]
  rfl

theorem y322_transfer_Z :
    zY = zY' ∧ zY * zY = 1 ∧
      ∀ d, d < 8 → yGen 4 4 3 (sub322Z d) * zY = zY * yGen 4 4 3 (sub322Z d) := by
  have h := y322_transfer sub322Z pairsPreserved_sub322Z spider_sub322Z
  rw [evalWord_F1_Z, evalWord_F2_Z] at h
  exact h

theorem y322_transfer_F :
    fY = fY' ∧ fY * fY = 1 ∧
      ∀ d, d < 8 → yGen 4 4 3 (sub322F d) * fY = fY * yGen 4 4 3 (sub322F d) := by
  have h := y322_transfer sub322F pairsPreserved_sub322F spider_sub322F
  rw [evalWord_F1_F, evalWord_F2_F] at h
  exact h

theorem zY_eq_evalWord :
    zY = (evalWord (yGen 4 4 3) [0, 9, 10, 11, 1, 2, 5]) ^ 9 := by
  simp only [zY, evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem zY_eq_evalWord' :
    zY = (evalWord (yGen 4 4 3) [0, 9, 10, 11, 5, 6, 1]) ^ 9 := by
  rw [y322_transfer_Z.1]
  simp only [zY', evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem fY_eq_evalWord :
    fY = (evalWord (yGen 4 4 3) [0, 1, 2, 3, 5, 6, 9]) ^ 9 := by
  simp only [fY, evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem fY_eq_evalWord' :
    fY = (evalWord (yGen 4 4 3) [0, 1, 2, 3, 9, 10, 5]) ^ 9 := by
  rw [y322_transfer_F.1]
  simp only [fY', evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem zY_mul_self :
    zY * zY = 1 := y322_transfer_Z.2.1

theorem fY_mul_self :
    fY * fY = 1 := y322_transfer_F.2.1

theorem zY_comm
    {c : ℕ} (hc : c < 12) : yGen 4 4 3 c * zY = zY * yGen 4 4 3 c := by
  obtain ⟨-, -, hcomm⟩ := y322_transfer_Z
  interval_cases c
  · exact hcomm 0 (by norm_num)
  · exact hcomm 4 (by norm_num)
  · exact hcomm 5 (by norm_num)
  · rw [zY_eq_evalWord']
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · rw [zY_eq_evalWord']
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · exact hcomm 6 (by norm_num)
  · exact hcomm 7 (by norm_num)
  · rw [zY_eq_evalWord]
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · rw [zY_eq_evalWord]
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · exact hcomm 1 (by norm_num)
  · exact hcomm 2 (by norm_num)
  · exact hcomm 3 (by norm_num)

theorem fY_comm
    {c : ℕ} (hc : c < 12) (hc4 : c ≠ 4) :
    yGen 4 4 3 c * fY = fY * yGen 4 4 3 c := by
  obtain ⟨-, -, hcomm⟩ := y322_transfer_F
  interval_cases c
  · exact hcomm 0 (by norm_num)
  · exact hcomm 1 (by norm_num)
  · exact hcomm 2 (by norm_num)
  · exact hcomm 3 (by norm_num)
  · exact absurd rfl hc4
  · exact hcomm 4 (by norm_num)
  · exact hcomm 5 (by norm_num)
  · rw [fY_eq_evalWord']
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · rw [fY_eq_evalWord']
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq
  · exact hcomm 6 (by norm_num)
  · exact hcomm 7 (by norm_num)
  · rw [fY_eq_evalWord]
    exact ((Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) (by decide)
      (by decide)).pow_right 9).eq

theorem zY_central :
    zY ∈ Subgroup.center (YGroup 4 4 3) :=
  Relabel.mem_center_of_commute_yGen fun _ hc => zY_comm hc


theorem z2_mul_self' (a : Multiplicative (ZMod 2)) : a * a = 1 := by
  revert a
  decide

theorem mul_z_mul_z {G : Type*} [Group G] {z : G} (hz : ∀ g, g * z = z * g) (hzz : z * z = 1)
    (a b : G) : (a * z) * (b * z) = a * b := by
  calc a * z * (b * z) = a * (z * b) * z := by simp only [mul_assoc]
    _ = a * (b * z) * z := by rw [← hz b]
    _ = a * b * (z * z) := by simp only [mul_assoc]
    _ = a * b := by rw [hzz, mul_one]


@[expose] def IsTri {V : Type*} (Γ : SimpleGraph V) (u v w : V) : Prop :=
  Γ.Adj u v ∧ Γ.Adj v w ∧ Γ.Adj w u

section Triangle

variable {E : Type*} [Group E] {L : Subgroup E} {X Y : E}

theorem yTri_of_cube (hX : X * X = 1) (hY : Y ∈ L) (hXY : (X * Y) ^ 3 = 1) (hXL : X ∉ L)
    (g : E) :
    yTri L X Y (Quotient.mk'' g) (Quotient.mk'' (X * g)) (Quotient.mk'' (X * Y * g)) := by
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX
  refine ⟨g, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    rw [rc_mk_eq_mk_iff] at h
    apply hXL
    simpa using h
  · intro h
    rw [rc_mk_eq_mk_iff] at h
    apply hXL
    have e : X * Y * g * (X * g)⁻¹ = X * Y * X := by
      rw [mul_inv_rev, hXi]
      group
    rw [e] at h
    have h3 : X * Y * X * (Y * X * Y) = 1 := by
      have := hXY
      rw [pow_three] at this
      simpa only [mul_assoc] using this
    have e2 : X * Y * X = Y⁻¹ * X * Y⁻¹ := by
      have := eq_inv_of_mul_eq_one_left h3
      rw [this, mul_inv_rev, mul_inv_rev, hXi]
      group
    rw [e2] at h
    have : X = Y * (Y⁻¹ * X * Y⁻¹) * Y := by group
    rw [this]
    exact L.mul_mem (L.mul_mem hY h) hY
  · intro h
    rw [rc_mk_eq_mk_iff] at h
    apply hXL
    have e : X * Y * g * g⁻¹ = X * Y := by group
    rw [e] at h
    have := L.mul_mem h (L.inv_mem hY)
    simpa using this

theorem isTri_of_cube (hX : X * X = 1) (hY : Y ∈ L) (hXY : (X * Y) ^ 3 = 1) (hXL : X ∉ L)
    (g : E) :
    IsTri (rcGraph L X) (Quotient.mk'' g) (Quotient.mk'' (X * g)) (Quotient.mk'' (X * Y * g)) :=
  yTri_adj hX hY hXY (yTri_of_cube hX hY hXY hXL g)

end Triangle

end CFSG.YGroups.Y443
