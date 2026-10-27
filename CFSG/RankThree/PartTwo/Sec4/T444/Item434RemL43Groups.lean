module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Mat
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemL43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev PSL43 : Type := projectiveSL 4 (ZMod 3)

noncomputable abbrev piL : SL4 →* PSL43 := proj 4 (ZMod 3)

@[expose] def uSL (a b c d : ZMod 3) : SL4 := ⟨uMat a b c d, det_uMat a b c d⟩

@[expose] def vSL (a b c d : ZMod 3) : SL4 := ⟨vMat a b c d, det_vMat a b c d⟩

@[expose] def hOneSL (a : ZMod 3) : SL4 := ⟨hOne a, (hOne_facts a).1⟩

@[expose] def hThreeSL (a d : ZMod 3) (hd : d ≠ 0) : SL4 := ⟨hThree a d, (hThree_facts a d hd).1⟩

theorem val_hOneSL_inv (a : ZMod 3) : (((hOneSL a)⁻¹ : SL4) : Mat4) = hOneInv a := by
  have h1 : hOneSL a * ⟨hOneInv a, by
      have h := congrArg Matrix.det (hOne_facts a).2
      rwa [Matrix.det_mul, (hOne_facts a).1, one_mul, Matrix.det_one] at h⟩ = 1 :=
    Subtype.ext (hOne_facts a).2
  rw [inv_eq_of_mul_eq_one_right h1]

theorem val_hThreeSL_inv (a d : ZMod 3) (hd : d ≠ 0) :
    (((hThreeSL a d hd)⁻¹ : SL4) : Mat4) = hThreeInv a d := by
  have h1 : hThreeSL a d hd * ⟨hThreeInv a d, by
      have h := congrArg Matrix.det (hThree_facts a d hd).2
      rwa [Matrix.det_mul, (hThree_facts a d hd).1, one_mul, Matrix.det_one] at h⟩ = 1 :=
    Subtype.ext (hThree_facts a d hd).2
  rw [inv_eq_of_mul_eq_one_right h1]

theorem rMat_mul (a b c d a' b' c' d' : ZMod 3) :
    rMat a b c d * rMat a' b' c' d' = rMat (a + a') (b + b') (c + c') (d + d') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

@[expose] def rHom : Multiplicative (Fin 4 → ZMod 3) →* SL4 where
  toFun x := (⟨rMat (x.toAdd 0) (x.toAdd 1) (x.toAdd 2) (x.toAdd 3), det_rMat _ _ _ _⟩ : SL4)
  map_one' := Subtype.ext (by decide)
  map_mul' x y := Subtype.ext (by
    change rMat _ _ _ _ = rMat _ _ _ _ * rMat _ _ _ _
    simp only [toAdd_mul, Pi.add_apply, rMat_mul])

@[expose] def rGrp : Subgroup SL4 := rHom.range

theorem mem_rGrp_iff {x : SL4} : x ∈ rGrp ↔ IsR (x : Mat4) := by
  constructor
  · rintro ⟨y, rfl⟩
    show rMat _ _ _ _ = rMat (rMat _ _ _ _ 0 2) (rMat _ _ _ _ 0 3) (rMat _ _ _ _ 1 2)
      (rMat _ _ _ _ 1 3)
    simp [rMat]
  · intro h
    refine ⟨Multiplicative.ofAdd ![(x : Mat4) 0 2, (x : Mat4) 0 3, (x : Mat4) 1 2, (x : Mat4) 1 3],
      Subtype.ext ?_⟩
    change rMat _ _ _ _ = (x : Mat4)
    rw [h]
    simp [rMat]

theorem rHom_injective : Function.Injective rHom := by
  intro x y h
  have h' := congrArg (fun g : SL4 => (g : Mat4)) h
  simp only [rHom] at h'
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · exact congrFun (congrFun h' 0) 2
  · exact congrFun (congrFun h' 0) 3
  · exact congrFun (congrFun h' 1) 2
  · exact congrFun (congrFun h' 1) 3

theorem pow_three_mult {ι : Type*} (x : Multiplicative (ι → ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext k
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]

theorem isElemAbelian_range_mult {ι : Type*} {Y : Type*} [Group Y]
    (f : Multiplicative (ι → ZMod 3) →* Y) : CFSG.Assembly.IsElemAbelian 3 f.range := by
  rw [MonoidHom.range_eq_map]
  exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f ⊤
    ⟨inferInstance, fun x _ => pow_three_mult x⟩

theorem card_mult (k : ℕ) : Nat.card (Multiplicative (Fin k → ZMod 3)) = 3 ^ k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isElemAbelian_rGrp : CFSG.Assembly.IsElemAbelian 3 rGrp := isElemAbelian_range_mult rHom

theorem card_rGrp : Nat.card rGrp = 81 := by
  rw [rGrp, MonoidHom.range_eq_map, Subgroup.card_map_of_injective rHom_injective,
    Subgroup.card_top, card_mult]
  norm_num

theorem rGrp_comm {x y : SL4} (hx : x ∈ rGrp) (hy : y ∈ rGrp) : x * y = y * x :=
  congrArg Subtype.val (isElemAbelian_rGrp.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

@[expose] def phiHom : Multiplicative (Fin 3 → ZMod 3) →* SL4 where
  toFun t := (⟨phiMat (t.toAdd 0, t.toAdd 1, t.toAdd 2), by
    rw [phiMat]
    exact det_p0Mat _ _ _⟩ : SL4)
  map_one' := Subtype.ext (by decide)
  map_mul' s t := Subtype.ext (by
    change phiMat _ = phiMat _ * phiMat _
    rw [← phiMat_add]
    simp only [toAdd_mul, Pi.add_apply, Prod.mk_add_mk])

theorem val_phiHom (t : Multiplicative (Fin 3 → ZMod 3)) :
    ((phiHom t : SL4) : Mat4) = phiMat (t.toAdd 0, t.toAdd 1, t.toAdd 2) :=
  rfl

@[expose] def pZeroGrp : Subgroup SL4 := phiHom.range

theorem mem_pZeroGrp_iff {x : SL4} : x ∈ pZeroGrp ↔ IsP0 (x : Mat4) := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [val_phiHom]
    exact isP0_phiMat _
  · intro h
    obtain ⟨⟨i, j, k⟩, ht⟩ := exists_phiMat_of_isP0 h
    exact ⟨Multiplicative.ofAdd ![i, j, k], Subtype.ext ht⟩

theorem phiHom_injective : Function.Injective phiHom := by
  intro s t h
  have h' := phiMat_injective (congrArg Subtype.val h)
  simp only [Prod.mk.injEq] at h'
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · exact h'.1
  · exact h'.2.1
  · exact h'.2.2

theorem isElemAbelian_pZeroGrp : CFSG.Assembly.IsElemAbelian 3 pZeroGrp :=
  isElemAbelian_range_mult phiHom

theorem card_pZeroGrp : Nat.card pZeroGrp = 27 := by
  rw [pZeroGrp, MonoidHom.range_eq_map, Subgroup.card_map_of_injective phiHom_injective,
    Subgroup.card_top, card_mult]
  norm_num

@[expose] def inclTwo : Multiplicative (Fin 2 → ZMod 3) →* Multiplicative (Fin 3 → ZMod 3) where
  toFun s := Multiplicative.ofAdd ![s.toAdd 0, s.toAdd 1, 0]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext k
    fin_cases k <;> rfl
  map_mul' s t := by
    apply Multiplicative.toAdd.injective
    funext k
    fin_cases k <;> simp

@[expose] def bZeroGrp : Subgroup SL4 := (phiHom.comp inclTwo).range

theorem bZeroGrp_le : bZeroGrp ≤ pZeroGrp := by
  rintro _ ⟨s, rfl⟩
  exact ⟨inclTwo s, rfl⟩

theorem phiHom_comp_inclTwo_injective : Function.Injective (phiHom.comp inclTwo) := by
  intro s t h
  have h' := phiHom_injective h
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · exact congrFun (congrArg Multiplicative.toAdd h') 0
  · exact congrFun (congrArg Multiplicative.toAdd h') 1

theorem isElemAbelian_bZeroGrp : CFSG.Assembly.IsElemAbelian 3 bZeroGrp :=
  isElemAbelian_range_mult _

theorem card_bZeroGrp : Nat.card bZeroGrp = 9 := by
  rw [bZeroGrp, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective phiHom_comp_inclTwo_injective, Subgroup.card_top, card_mult]
  norm_num

theorem exists_of_mem_bZeroGrp {x : SL4} (hx : x ∈ bZeroGrp) :
    ∃ i j : ZMod 3, (x : Mat4) = phiMat (i, j, 0) := by
  obtain ⟨s, rfl⟩ := hx
  exact ⟨s.toAdd 0, s.toAdd 1, rfl⟩

theorem units_zmod_three (c : (ZMod 3)ˣ) : (c : ZMod 3) = 1 ∨ (c : ZMod 3) = -1 := by
  have hc : (c : ZMod 3) ≠ 0 := c.ne_zero
  generalize (c : ZMod 3) = x at hc ⊢
  revert x
  decide

theorem val_eq_one_or_neg_one_of_mem_scalars {x : SL4} (hx : x ∈ scalars 4 (ZMod 3)) :
    (x : Mat4) = 1 ∨ (x : Mat4) = -1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hx
  rcases units_zmod_three c with h | h
  · left
    rw [hc, h, map_one]
  · right
    rw [hc, h]
    ext a b
    by_cases hab : a = b
    · simp [hab]
    · have e1 : (scalar (Fin 4) (-1 : ZMod 3)) a b = 0 := by
        rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab]
      have e2 : (-1 : Mat4) a b = 0 := by
        rw [Matrix.neg_apply, Matrix.one_apply_ne hab]
        decide
      rw [e1, e2]

theorem eq_one_of_mem_scalars_of_pow_three {c : SL4} (hc : c ∈ scalars 4 (ZMod 3))
    (h3 : c ^ 3 = 1) : c = 1 := by
  rcases val_eq_one_or_neg_one_of_mem_scalars hc with h | h
  · exact Subtype.ext h
  · exfalso
    have h' : (c : Mat4) ^ 3 = 1 := congrArg (fun x : SL4 => (x : Mat4)) h3
    rw [h] at h'
    have := congrFun (congrFun h' 0) 0
    revert this
    decide

theorem mul_comm_of_proj_mul_comm {g b : SL4} (hb : b ^ 3 = 1)
    (h : piL g * piL b = piL b * piL g) : g * b = b * g := by
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h
  set c := (g * b)⁻¹ * (b * g) with hc
  have hcZ : c ∈ Subgroup.center SL4 := scalars_le_center 4 (ZMod 3) h
  have hbg : b * g = g * b * c := by rw [hc]; group
  have hconj : g⁻¹ * b * g = b * c := by
    calc g⁻¹ * b * g = g⁻¹ * (b * g) := by group
      _ = g⁻¹ * (g * b * c) := by rw [hbg]
      _ = b * c := by group
  have hc3 : c ^ 3 = 1 := by
    have h1 : (g⁻¹ * b * g) ^ 3 = 1 := by
      have e := conj_pow (a := g⁻¹) (b := b) (i := 3)
      rw [inv_inv, hb] at e
      rw [e]
      group
    have hbc : Commute b c := Subgroup.mem_center_iff.mp hcZ b
    rw [hconj, hbc.mul_pow, hb, one_mul] at h1
    exact h1
  have hc1 := eq_one_of_mem_scalars_of_pow_three h hc3
  rw [hbg, hc1, mul_one]

theorem mem_scalars_of_val {x : SL4} (hx : (x : Mat4) = 1 ∨ (x : Mat4) = -1) :
    x ∈ scalars 4 (ZMod 3) := by
  rcases hx with h | h
  · exact ⟨1, one_pow 4, by rw [h, Units.val_one, map_one]⟩
  · exact ⟨-1, by decide, by rw [h, Units.val_neg, Units.val_one, map_neg, map_one]⟩

theorem val_pow_three_of_comm {g : SL4} {i j : ZMod 3} (hij : ¬ (i = 0 ∧ j = 0))
    (h : (g : Mat4) * phiMat (i, j, 0) = phiMat (i, j, 0) * (g : Mat4)) :
    ((g ^ 3 : SL4) : Mat4) = 1 ∨ ((g ^ 3 : SL4) : Mat4) = -1 := by
  obtain ⟨hb, hinv, hdet⟩ := hB_check i j hij
  set H := hB i j
  set H' := hBInv i j
  have hinv' : H' * H = 1 := mul_eq_one_comm.mp hinv
  set b := phiMat (i, j, 0)
  have hb' : H' * b = (1 + nZero) * H' := by
    calc H' * b = H' * b * (H * H') := by rw [hinv, Matrix.mul_one]
      _ = H' * (b * H) * H' := by simp only [Matrix.mul_assoc]
      _ = H' * (H * (1 + nZero)) * H' := by rw [hb]
      _ = (H' * H) * (1 + nZero) * H' := by simp only [Matrix.mul_assoc]
      _ = (1 + nZero) * H' := by rw [hinv', Matrix.one_mul]
  set g' := H' * (g : Mat4) * H with hg'
  have hcomm : g' * (1 + nZero) = (1 + nZero) * g' := by
    calc g' * (1 + nZero) = H' * (g : Mat4) * (H * (1 + nZero)) := by
          rw [hg', Matrix.mul_assoc]
      _ = H' * (g : Mat4) * (b * H) := by rw [hb]
      _ = H' * ((g : Mat4) * b) * H := by simp only [Matrix.mul_assoc]
      _ = H' * (b * (g : Mat4)) * H := by rw [h]
      _ = (H' * b) * (g : Mat4) * H := by simp only [Matrix.mul_assoc]
      _ = (1 + nZero) * H' * (g : Mat4) * H := by rw [hb']
      _ = (1 + nZero) * g' := by rw [hg']; simp only [Matrix.mul_assoc]
  have hdet' : g'.det = 1 := by
    rw [hg', Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul, hinv',
      Matrix.det_one]
  have hcube := cMat_cube _ _ _ _ _ _ (eq_cMat_of_comm hcomm ▸ hdet')
  rw [← eq_cMat_of_comm hcomm] at hcube
  have hg : (g : Mat4) = H * g' * H' := by
    rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.mul_assoc,
      hinv, Matrix.mul_one]
  have hpow : ((g ^ 3 : SL4) : Mat4) = H * g' ^ 3 * H' := by
    change (g : Mat4) ^ 3 = _
    rw [hg]
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H' H, hinv', Matrix.one_mul, ← Matrix.mul_assoc H' H, hinv',
      Matrix.one_mul]
  rcases hcube with h1 | h1
  · left
    rw [hpow, h1, Matrix.mul_one, hinv]
  · right
    rw [hpow, h1, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hinv]
    rfl

theorem pow_three_eq_one_of_mem_centralizer {x : PSL43} {b : SL4} (hb : b ∈ bZeroGrp)
    (hb1 : b ≠ 1) (hx : x * piL b = piL b * x) : x ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 3) x
  obtain ⟨i, j, hij⟩ := exists_of_mem_bZeroGrp hb
  have hb3 : b ^ 3 = 1 := isElemAbelian_bZeroGrp.2 b hb
  have hgb := mul_comm_of_proj_mul_comm hb3 hx
  have hne : ¬ (i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hb1
    apply Subtype.ext
    rw [hij]
    exact phiMat_zero
  have hval : (g : Mat4) * phiMat (i, j, 0) = phiMat (i, j, 0) * (g : Mat4) := by
    rw [← hij]
    exact congrArg (fun x : SL4 => (x : Mat4)) hgb
  have hZ : g ^ 3 ∈ scalars 4 (ZMod 3) := mem_scalars_of_val (val_pow_three_of_comm hne hval)
  rw [← map_pow, ← MonoidHom.mem_ker, ker_proj]
  exact hZ

end CFSG.RankThree.PartTwo.Sec4.Item434RemL43
