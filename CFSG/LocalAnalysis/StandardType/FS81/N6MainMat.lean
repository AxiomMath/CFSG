module

public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Mat
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Rep
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.HMCore

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def tz : Matrix (Fin 7) (Fin 7) (ZMod 3) := tau0Mat 6

theorem tz_eq_tau0Mat : tz = tau0Mat 6 := rfl

theorem axis_eq_zero_of_mixed {σ : Equiv.Perm (Fin 7)} {s : Fin 7 → ZMod 3} (hσ0 : σ 0 = 0)
    {u : Fin 7 → ZMod 3} (hu0 : u 0 ≠ 0) (hu : spMat σ s *ᵥ u = -u)
    (hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z = c • u) : ∀ j : Fin 7, j ≠ 0 → u j = 0 :=
  axis_apply_eq_zero_of_axis_zero_ne (n := 6) hσ0 hu0 hu hl

structure N6MatHyp (Xg : Subgroup (GL (Fin 7) (ZMod 3))) : Prop where
  norm : ∀ A ∈ Xg, (∀ i : Fin 7, i ≠ 0 → (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 = 0) →
    (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenN0 6
  sub : ∀ M ∈ evenN0 6, ∃ A ∈ Xg, (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) = M
  odd : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥
  moves : ∃ A ∈ Xg, ∃ i : Fin 7, i ≠ 0 ∧ (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 ≠ 0

theorem N6MatHyp.toEvenN0MatHyp {Xg : Subgroup (GL (Fin 7) (ZMod 3))} (h : N6MatHyp Xg) :
    EvenN0MatHyp 6 Xg :=
  ⟨h.norm, h.sub, h.odd, h.moves⟩

@[expose] def O6 (Xg : Subgroup (GL (Fin 7) (ZMod 3))) (v : Fin 7 → ZMod 3) : Prop :=
  ∃ A ∈ Xg, (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 = v

section Orbit

variable {Xg : Subgroup (GL (Fin 7) (ZMod 3))}

theorem o6_mulVec {v : Fin 7 → ZMod 3} (hv : O6 Xg v) {B : GL (Fin 7) (ZMod 3)} (hB : B ∈ Xg) :
    O6 Xg ((B : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ v) := by
  obtain ⟨A, hA, rfl⟩ := hv
  exact ⟨B * A, Xg.mul_mem hB hA, gl_mul_mulVec B A _⟩

theorem o6_mulVec_iff {v : Fin 7 → ZMod 3} {B : GL (Fin 7) (ZMod 3)} (hB : B ∈ Xg) :
    O6 Xg ((B : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ v) ↔ O6 Xg v := by
  refine ⟨fun hv => ?_, fun hv => o6_mulVec hv hB⟩
  have := o6_mulVec hv (Xg.inv_mem hB)
  rwa [gl_inv_mulVec_mulVec] at this

theorem o6_e0 : O6 Xg (Pi.single 0 1) :=
  ⟨1, Xg.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩

end Orbit

namespace N6MatHyp

variable {Xg : Subgroup (GL (Fin 7) (ZMod 3))}

theorem mem_H_of_mulVec_e0 (h : N6MatHyp Xg) {A : GL (Fin 7) (ZMod 3)} (hA : A ∈ Xg) {c : ZMod 3}
    (hc : (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 = c • Pi.single 0 1) :
    (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenN0 6 :=
  h.toEvenN0MatHyp.mem_H_of_mulVec_e0 hA hc

theorem exists_T (h : N6MatHyp Xg) : ∃ T ∈ Xg, (T : Matrix (Fin 7) (Fin 7) (ZMod 3)) = tz := by
  obtain ⟨T, hT, hTe⟩ := h.toEvenN0MatHyp.exists_T
  exact ⟨T, hT, hTe.trans tz_eq_tau0Mat.symm⟩

theorem conj_eq_of_mulVec_e0 (h : N6MatHyp Xg) {T : GL (Fin 7) (ZMod 3)}
    (hT : (T : Matrix (Fin 7) (Fin 7) (ZMod 3)) = tz) {A B : GL (Fin 7) (ZMod 3)} (hA : A ∈ Xg)
    (hB : B ∈ Xg) {c : ZMod 3}
    (hAB : (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 =
      c • ((B : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1)) :
    A * T * A⁻¹ = B * T * B⁻¹ :=
  h.toEvenN0MatHyp.conj_eq_of_mulVec_e0 (hT.trans tz_eq_tau0Mat) hA hB hAB

end N6MatHyp

theorem refl_sub {T : GL (Fin 7) (ZMod 3)} (hT : (T : Matrix (Fin 7) (Fin 7) (ZMod 3)) = tz)
    (A : GL (Fin 7) (ZMod 3)) (z : Fin 7 → ZMod 3) :
    ((A * T * A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z - z =
      ((((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) 0) •
        ((A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) :=
  conj_tau0_mulVec_sub (n := 6) (T := T) (hT.trans tz_eq_tau0Mat) A z

namespace N6MatHyp

variable {Xg : Subgroup (GL (Fin 7) (ZMod 3))}

theorem exists_U2 (h : N6MatHyp Xg) : ∃ v, O6 Xg v ∧ v 0 = 0 ∧ wt v = 2 :=
  h.toEvenN0MatHyp.exists_U2

theorem wt_two_of_O6 (h : N6MatHyp Xg) {v : Fin 7 → ZMod 3} (hv : O6 Xg v)
    (hv0 : v 0 = 0) : wt v = 2 :=
  h.toEvenN0MatHyp.wt_two_of_O6 hv hv0

end N6MatHyp

@[expose] def wtR (v : Fin 7 → ZMod 3) : ℕ := wt (fun i : Fin 6 => v i.succ)

@[expose] def rep6 (z : Bool) (k : ℕ) (ε : ZMod 3) : Fin 7 → ZMod 3 := fun i =>
  if i = 0 then (if z then 0 else 1) else
    if (i : ℕ) ≤ k then (if (i : ℕ) = 6 then ε else 1) else 0

theorem wtR_le (v : Fin 7 → ZMod 3) : wtR v ≤ 6 := by
  unfold wtR wt
  exact (Finset.card_le_univ _).trans (by simp)

theorem exists_evenN0_mulVec_eq_rep6 (v : Fin 7 → ZMod 3) :
    ∃ M ∈ evenN0 6, M *ᵥ v = rep6 (decide (v 0 = 0)) (wtR v) (∏ i : Fin 6, v i.succ) := by
  obtain ⟨M, hM, hMv⟩ := exists_evenN0_mulVec_eq_rep 6 v
  exact ⟨M, hM, hMv⟩

theorem N6MatHyp.o6_iff_rep6 {Xg : Subgroup (GL (Fin 7) (ZMod 3))} (h : N6MatHyp Xg)
    (v : Fin 7 → ZMod 3) :
    O6 Xg v ↔ O6 Xg (rep6 (decide (v 0 = 0)) (wtR v) (∏ i : Fin 6, v i.succ)) := by
  obtain ⟨M, hM, hMv⟩ := exists_evenN0_mulVec_eq_rep6 v
  obtain ⟨A, hA, hAM⟩ := h.sub M hM
  rw [← hMv, ← hAM, o6_mulVec_iff hA]

theorem sum_mul_single7 (a : Fin 7 → ZMod 3) (l : Fin 7) (c : ZMod 3) :
    ∑ j, a j * (Pi.single l c : Fin 7 → ZMod 3) j = a l * c := by
  rw [Finset.sum_eq_single l (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same]

theorem sum_mul_add7 (a x y : Fin 7 → ZMod 3) :
    ∑ j, a j * (x + y) j = ∑ j, a j * x j + ∑ j, a j * y j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, mul_add]

theorem add_self_eq_neg (v : Fin 7 → ZMod 3) : v + v = -v := by
  funext i
  simp only [Pi.add_apply, Pi.neg_apply]
  generalize v i = a
  revert a
  decide

theorem sign_mem_evenN0 {i j : Fin 7} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    spMat 1 (fun l => if l = i ∨ l = j then -1 else 1) ∈ evenN0 6 := by
  refine ⟨1, _, fun l => ?_, ⟨rfl, ?_⟩, rfl⟩
  · show (if l = i ∨ l = j then (-1 : ZMod 3) else 1) = 1 ∨ _ = -1
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    have hij' : i' ≠ j' := fun h => hij (by rw [h])
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i'), ← Finset.mul_prod_erase _ _
      (Finset.mem_erase.mpr ⟨Ne.symm hij', Finset.mem_univ j'⟩)]
    rw [Finset.prod_eq_one fun l hl => ?_]
    · simp only [true_or, or_true, if_true]
      decide
    · have hl1 := Finset.ne_of_mem_erase hl
      have hl2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [if_neg]
      rintro (h | h)
      · exact hl2 (Fin.succ_injective _ h)
      · exact hl1 (Fin.succ_injective _ h)

namespace N6MatHyp

variable {Xg : Subgroup (GL (Fin 7) (ZMod 3))}

theorem refl_coeff_inv (h : N6MatHyp Xg) {T : GL (Fin 7) (ZMod 3)}
    (hT : (T : Matrix (Fin 7) (Fin 7) (ZMod 3)) = tz)
    {A : GL (Fin 7) (ZMod 3)} (hA : A ∈ Xg)
    (hv0 : ((A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 1)
    {g : GL (Fin 7) (ZMod 3)} (hg : g ∈ Xg)
    (hgv : (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ ((A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
      Pi.single 0 1) = (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1)
    (z : Fin 7 → ZMod 3) :
    (((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
      ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z)) 0 =
      (((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) 0 := by
  have hu := h.conj_eq_of_mulVec_e0 hT (Xg.mul_mem hg hA) hA (c := 1)
    (by rw [gl_mul_mulVec, hgv, one_smul])
  have hcomm : (A * T * A⁻¹) * g = g * (A * T * A⁻¹) := by
    calc (A * T * A⁻¹) * g = (g * A) * T * (g * A)⁻¹ * g := by rw [hu]
      _ = g * (A * T * A⁻¹) := by group
  have hrg : ((A * T * A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
      ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) = (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
      (((A * T * A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) := by
    rw [← gl_mul_mulVec, ← gl_mul_mulVec, hcomm]
  have e1 := refl_sub hT A ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z)
  rw [hrg] at e1
  have e3 : (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
      (((A * T * A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) -
        (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z =
      ((((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) 0) •
        ((A : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    rw [← Matrix.mulVec_sub, refl_sub hT A z, Matrix.mulVec_smul, hgv]
  rw [e1] at e3
  have e4 := congrFun e3 0
  simp only [Pi.smul_apply, smul_eq_mul, hv0, mul_one] at e4
  exact e4

theorem refl_data (h : N6MatHyp Xg) {v : Fin 7 → ZMod 3} (hv : O6 Xg v) (hv0 : v 0 = 1) :
    ∃ r ∈ Xg, ∃ a : Fin 7 → ZMod 3,
      (∀ z, (r : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z = z + (∑ j, a j * z j) • v) ∧
      (∑ j, a j * v j = 1) ∧
      (∀ M ∈ evenN0 6, M *ᵥ v = v → ∀ z, ∑ j, a j * (M *ᵥ z) j = ∑ j, a j * z j) := by
  obtain ⟨T, hTX, hT⟩ := h.exists_T
  obtain ⟨A, hA, rfl⟩ := hv
  have hf : ∀ z, (((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z) 0 =
      ∑ j, ((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) 0 j * z j :=
    fun z => rfl
  refine ⟨A * T * A⁻¹, Xg.mul_mem (Xg.mul_mem hA hTX) (Xg.inv_mem hA),
    fun j => ((A⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) 0 j,
    fun z => ?_, ?_, fun M hM hMv z => ?_⟩
  · rw [← hf, ← refl_sub hT A z]
    abel
  · rw [← hf, gl_inv_mulVec_mulVec, Pi.single_eq_same]
  · obtain ⟨g, hg, hgM⟩ := h.sub M hM
    rw [← hf, ← hf, ← hgM]
    exact h.refl_coeff_inv hT hA hv0 hg (by rw [hgM, hMv]) z

theorem false_of_refl_fix (h : N6MatHyp Xg) {v : Fin 7 → ZMod 3} (hv0 : v 0 = 1)
    {j : Fin 7} (hj : j ≠ 0)
    (hvj : v j ≠ 0) {r : GL (Fin 7) (ZMod 3)} (hr : r ∈ Xg) {a : Fin 7 → ZMod 3}
    (hra : ∀ z, (r : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z = z + (∑ j, a j * z j) • v)
    (hav : ∑ j, a j * v j = 1) (ha0 : a 0 = 0) : False := by
  have he : (r : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 =
      (1 : ZMod 3) • Pi.single 0 1 := by
    rw [hra, sum_mul_single7, ha0, zero_mul, zero_smul, add_zero, one_smul]
  obtain ⟨σ, s, -, ⟨hσ0, -⟩, hrs⟩ := h.mem_H_of_mulVec_e0 hr he
  have hneg : spMat σ s *ᵥ v = -v := by rw [← hrs, hra, hav, one_smul, add_self_eq_neg]
  have hl : ∀ z, ∃ c : ZMod 3, spMat σ s *ᵥ z - z = c • v :=
    fun z => ⟨∑ j, a j * z j, by rw [← hrs, hra, add_sub_cancel_left]⟩
  exact hvj (axis_eq_zero_of_mixed hσ0 (by rw [hv0]; decide) hneg hl j hj)

theorem o6_iff_of_rep6_eq (h : N6MatHyp Xg) {w u : Fin 7 → ZMod 3}
    (he : rep6 (decide (w 0 = 0)) (wtR w) (∏ i : Fin 6, w i.succ) =
      rep6 (decide (u 0 = 0)) (wtR u) (∏ i : Fin 6, u i.succ)) : O6 Xg w ↔ O6 Xg u := by
  rw [h.o6_iff_rep6 w, h.o6_iff_rep6 u, he]

theorem coeff_rel {v a : Fin 7 → ZMod 3}
    (hinv : ∀ M ∈ evenN0 6, M *ᵥ v = v → ∀ z, ∑ j, a j * (M *ᵥ z) j = ∑ j, a j * z j)
    {M : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hM : M ∈ evenN0 6) (hMv : M *ᵥ v = v) {l m : Fin 7}
    {c : ZMod 3} (hMl : M *ᵥ Pi.single l 1 = Pi.single m c) : a m * c = a l := by
  have e := hinv M hM hMv (Pi.single l 1)
  rwa [hMl, sum_mul_single7, sum_mul_single7, mul_one] at e

theorem o6_rep2_of_rep1 (h : N6MatHyp Xg) (h1 : O6 Xg (rep6 false 1 1)) :
    O6 Xg (rep6 false 2 1) := by
  obtain ⟨r, hr, a, hra, hav, hinv⟩ := h.refl_data h1 (by decide)
  have ha2 : a 2 = 0 := by
    have e := coeff_rel hinv (sign_mem_evenN0 (i := 2) (j := 3) (by decide) (by decide)
      (by decide)) (by rw [spMat_mulVec]; decide) (l := 2) (m := 2) (c := -1)
      (by rw [spMat_mulVec_single]; decide)
    rw [mul_neg_one] at e
    exact zmod3_eq_zero_of_eq_neg e.symm
  rcases (show ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 by decide) (a 0) with h0 | h0 | h0
  · exact (h.false_of_refl_fix (by decide) (j := 1) (by decide) (by decide) hr hra hav h0).elim
  ·
    have hw : O6 Xg (Pi.single 0 1 + Pi.single 2 1) := (h.o6_iff_of_rep6_eq (by decide)).mpr h1
    have hrw := o6_mulVec hw hr
    rw [hra, sum_mul_add7, sum_mul_single7, sum_mul_single7, h0, ha2] at hrw
    exact (h.o6_iff_of_rep6_eq (by decide)).mp hrw
  ·
    have hrw := o6_mulVec (o6_e0 (Xg := Xg)) hr
    rw [hra, sum_mul_single7, h0] at hrw
    exact absurd (h.wt_two_of_O6 hrw (by decide)) (by decide)

theorem of_o6_rep2_coeff (h : N6MatHyp Xg) (h2 : O6 Xg (rep6 false 2 1)) :
    ∃ r ∈ Xg, ∃ a : Fin 7 → ZMod 3,
      (∀ z, (r : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ z =
        z + (∑ j, a j * z j) • rep6 false 2 1) ∧
      (∑ j, a j * (rep6 false 2 1) j = 1) ∧
      (∀ M ∈ evenN0 6, M *ᵥ rep6 false 2 1 = rep6 false 2 1 →
        ∀ z, ∑ j, a j * (M *ᵥ z) j = ∑ j, a j * z j) ∧
      a 2 = a 1 ∧ a 3 = 0 ∧ a 4 = 0 ∧ a 5 = 0 ∧ a 0 + a 1 + a 1 = 1 := by
  obtain ⟨r, hr, a, hra, hav, hinv⟩ := h.refl_data h2 (by decide)
  have ha12 : a 2 = a 1 := by
    have e := coeff_rel hinv (M := spMat (Equiv.swap 1 2) 1)
      ⟨Equiv.swap 1 2, 1, fun _ => Or.inl rfl, ⟨by decide, by decide⟩, rfl⟩
      (by rw [spMat_mulVec]; decide) (l := 1) (m := 2) (c := 1)
      (by rw [spMat_mulVec_single]; decide)
    rwa [mul_one] at e
  have hzero : ∀ {i j : Fin 7} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j),
      spMat 1 (fun l => if l = i ∨ l = j then -1 else 1) *ᵥ rep6 false 2 1 = rep6 false 2 1 →
      a i = 0 := by
    intro i j hi hj hij hMv
    have e := coeff_rel hinv (sign_mem_evenN0 hi hj hij) hMv (l := i) (m := i) (c := -1)
      (by rw [spMat_mulVec_single, Equiv.Perm.one_apply, if_pos (Or.inl rfl), mul_one])
    rw [mul_neg_one] at e
    exact zmod3_eq_zero_of_eq_neg e.symm
  have ha3 : a 3 = 0 := hzero (j := 4) (by decide) (by decide) (by decide)
    (by rw [spMat_mulVec]; decide)
  have ha4 : a 4 = 0 := hzero (j := 3) (by decide) (by decide) (by decide)
    (by rw [spMat_mulVec]; decide)
  have ha5 : a 5 = 0 := hzero (j := 6) (by decide) (by decide) (by decide)
    (by rw [spMat_mulVec]; decide)
  have hsum : a 0 + a 1 + a 1 = 1 := by
    rw [show (rep6 false 2 1 : Fin 7 → ZMod 3) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 by
      decide, sum_mul_add7, sum_mul_add7, sum_mul_single7, sum_mul_single7, sum_mul_single7,
      ha12] at hav
    simpa only [mul_one] using hav
  exact ⟨r, hr, a, hra, hav, hinv, ha12, ha3, ha4, ha5, hsum⟩

theorem of_o6_rep2 (h : N6MatHyp Xg) (h2 : O6 Xg (rep6 false 2 1)) :
    O6 Xg (rep6 false 1 1) ∧ O6 Xg (rep6 false 3 1) ∧ O6 Xg (rep6 false 4 1) ∧
      O6 Xg (rep6 false 5 1) := by
  obtain ⟨r, hr, a, hra, hav, -, ha12, ha3, ha4, ha5, hsum⟩ := h.of_o6_rep2_coeff h2
  rcases (show ∀ c d : ZMod 3, c + d + d = 1 → c = 0 ∨ (c = 2 ∧ d = 1) ∨ (c = 1 ∧ d = 0) by
    decide) (a 0) (a 1) hsum with h0 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact (h.false_of_refl_fix (by decide) (j := 1) (by decide) (by decide) hr hra hav h0).elim
  · have hw : O6 Xg (Pi.single 0 1 + Pi.single 3 1 + Pi.single 4 1) :=
      (h.o6_iff_of_rep6_eq (by decide)).mpr h2
    have hrw := o6_mulVec hw hr
    rw [hra, sum_mul_add7, sum_mul_add7, sum_mul_single7, sum_mul_single7, sum_mul_single7, h0,
      ha3, ha4] at hrw
    exact absurd (h.wt_two_of_O6 hrw (by decide)) (by decide)
  · have h1' : O6 Xg (rep6 false 1 1) := by
      have hw : O6 Xg (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 (-1)) :=
        (h.o6_iff_of_rep6_eq (by decide)).mpr h2
      have hrw := o6_mulVec hw hr
      rw [hra, sum_mul_add7, sum_mul_add7, sum_mul_single7, sum_mul_single7, sum_mul_single7,
        h0, h1, ha12, h1] at hrw
      exact (h.o6_iff_of_rep6_eq (by decide)).mp hrw
    have h3 : O6 Xg (rep6 false 3 1) := by
      have hw : O6 Xg (Pi.single 0 1 + Pi.single 1 1 + Pi.single 3 1) :=
        (h.o6_iff_of_rep6_eq (by decide)).mpr h2
      have hrw := o6_mulVec hw hr
      rw [hra, sum_mul_add7, sum_mul_add7, sum_mul_single7, sum_mul_single7, sum_mul_single7,
        h0, h1, ha3] at hrw
      exact (h.o6_iff_of_rep6_eq (by decide)).mp hrw
    have h4 : O6 Xg (rep6 false 4 1) := by
      have hw : O6 Xg (Pi.single 0 1 + Pi.single 3 1 + Pi.single 4 1) :=
        (h.o6_iff_of_rep6_eq (by decide)).mpr h2
      have hrw := o6_mulVec hw hr
      rw [hra, sum_mul_add7, sum_mul_add7, sum_mul_single7, sum_mul_single7, sum_mul_single7,
        h0, ha3, ha4] at hrw
      exact (h.o6_iff_of_rep6_eq (by decide)).mp hrw
    have h5 : O6 Xg (rep6 false 5 1) := by
      have hw : O6 Xg (Pi.single 0 1 + Pi.single 1 1 + Pi.single 3 1 + Pi.single 4 1 +
          Pi.single 5 1) := (h.o6_iff_of_rep6_eq (by decide)).mpr h4
      have hrw := o6_mulVec hw hr
      rw [hra, sum_mul_add7, sum_mul_add7, sum_mul_add7, sum_mul_add7, sum_mul_single7,
        sum_mul_single7, sum_mul_single7, sum_mul_single7, sum_mul_single7, h0, h1, ha3, ha4,
        ha5] at hrw
      exact (h.o6_iff_of_rep6_eq (by decide)).mp hrw
    exact ⟨h1', h3, h4, h5⟩

end N6MatHyp

theorem card_perm_fix_zero7 : Nat.card {σ : Equiv.Perm (Fin 7) // σ 0 = 0} = 720 := by
  have e1 : {σ : Equiv.Perm (Fin 7) // σ 0 = 0} ≃
      {f : Equiv.Perm (Fin 7) // ∀ a, ¬ (a ≠ 0) → f a = a} :=
    Equiv.subtypeEquivRight fun f => ⟨fun h a ha => by
      rw [not_not] at ha
      subst ha
      exact h, fun h => h 0 (by simp)⟩
  rw [Nat.card_congr (e1.trans (Equiv.Perm.subtypeEquivSubtypePerm
    (fun a : Fin 7 => a ≠ 0)).symm), Nat.card_perm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_subtype_eq]
  rfl

theorem card_signs7 :
    Nat.card {s : Fin 7 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ = 1} = 32 := by
  have e : {s : Fin 7 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ = 1} =
      {s : Fin 7 → ZMod 3 // (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ = 1} :=
    rfl
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem sign_eq_of_spMat_eq7 {σ τ : Equiv.Perm (Fin 7)} {s t : Fin 7 → ZMod 3} (hs : IsSign s)
    (h : spMat σ s = spMat τ t) : s = t := by
  have hστ := perm_eq_of_spMat_eq hs h
  subst hστ
  funext j
  have e := congrFun (congrFun h (σ j)) j
  rwa [spMat_apply, spMat_apply, if_pos rfl, if_pos rfl] at e

theorem ncard_of_card7 {p : (Fin 7 → ZMod 3) → Prop} [DecidablePred p] {n : ℕ}
    (h : (Finset.univ.filter p).card = n) : {v : Fin 7 → ZMod 3 | p v}.ncard = n := by
  rw [← h, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem ncard_setOf_or7 {p q : (Fin 7 → ZMod 3) → Prop} (hd : ∀ v, p v → ¬ q v) :
    {v | p v ∨ q v}.ncard = {v | p v}.ncard + {v | q v}.ncard := by
  have hdisj : Disjoint {v : Fin 7 → ZMod 3 | p v} {v | q v} :=
    Set.disjoint_left.mpr fun v hp hq => hd v hp hq
  rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  rfl

theorem ncard_setOf_and7 (p : (Fin 7 → ZMod 3) → Prop) (b : Prop) [Decidable b] :
    {v | p v ∧ b}.ncard = if b then {v | p v}.ncard else 0 := by
  by_cases hb : b
  · simp [hb]
  · simp [hb]

theorem card_B0 : (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 0).card = 2 := by
  decide +kernel

theorem card_U2 : (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 = 0 ∧ wtR v = 2).card = 60 := by
  decide +kernel

theorem card_M1 : (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 1).card = 24 := by
  decide +kernel

theorem card_M2 :
    (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 2).card = 120 := by
  decide +kernel

theorem card_M3 :
    (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 3).card = 320 := by
  decide +kernel

theorem card_M4 :
    (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 4).card = 480 := by
  decide +kernel

theorem card_M5 :
    (Finset.univ.filter fun v : Fin 7 → ZMod 3 => v 0 ≠ 0 ∧ wtR v = 5).card = 384 := by
  decide +kernel

theorem card_M6p : (Finset.univ.filter fun v : Fin 7 → ZMod 3 =>
    v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = 1).card = 64 := by
  decide +kernel

theorem card_M6m : (Finset.univ.filter fun v : Fin 7 → ZMod 3 =>
    v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = -1).card = 64 := by
  decide +kernel

theorem rep6_indep {z : Bool} {k : ℕ} (hk : k < 6) (ε ε' : ZMod 3) : rep6 z k ε = rep6 z k ε' := by
  funext i
  unfold rep6
  split_ifs with h1 h2 h3 h4 <;> first | rfl | omega

theorem wt_rep6_true (k : ℕ) (hk : k ≤ 6) {ε : ZMod 3} (hε : ε ≠ 0) : wt (rep6 true k ε) = k := by
  rcases (show ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 by decide) ε hε with rfl | rfl <;>
    interval_cases k <;> decide

theorem wt_eq_wtR (v : Fin 7 → ZMod 3) : wt v = (if v 0 ≠ 0 then 1 else 0) + wtR v := by
  unfold wt wtR
  rw [Fin.card_filter_univ_succ']
  rfl

theorem prod_ne_zero_of_wtR {v : Fin 7 → ZMod 3} (hv : wtR v = 6) : ∏ i : Fin 6, v i.succ ≠ 0 := by
  have hall := (wt_eq_iff_forall_ne_zero (fun i : Fin 6 => v i.succ)).mp hv
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hall i

namespace N6MatHyp

variable {Xg : Subgroup (GL (Fin 7) (ZMod 3))}

theorem card_stab (h : N6MatHyp Xg) :
    Nat.card ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 7 → ZMod 3)) = 23040 := by
  classical
  let Q := {σ : Equiv.Perm (Fin 7) // σ 0 = 0} ×
    {s : Fin 7 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ = 1}
  have hsm : ∀ (A : ↥Xg) (v : Fin 7 → ZMod 3), A • v =
      ((A : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ v :=
    fun A v => by rw [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]
  have hex : ∀ q : Q, ∃ A ∈ Xg,
      (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) = spMat q.1.1 q.2.1 :=
    fun q => h.sub _ ⟨q.1.1, q.2.1, q.2.2.1, ⟨q.1.2, q.2.2.2.2⟩, rfl⟩
  have hfix : ∀ q : Q, spMat q.1.1 q.2.1 *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, -, hs0, -⟩⟩; show spMat σ s *ᵥ Pi.single 0 1 = Pi.single 0 1
    rw [spMat_mulVec_single, hσ, hs0, mul_one]
  let Φ : Q → ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 7 → ZMod 3)) := fun q =>
    ⟨⟨(hex q).choose, (hex q).choose_spec.1⟩, by
      rw [MulAction.mem_stabilizer_iff, hsm]
      show ((hex q).choose : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ _ = _
      rw [(hex q).choose_spec.2]; exact hfix q⟩
  have hΦ : ∀ q, (((Φ q : ↥Xg) : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) =
      spMat q.1.1 q.2.1 := fun q => (hex q).choose_spec.2
  have hbij : Function.Bijective Φ := by
    constructor
    · intro q q' hq
      have e := congrArg (fun A : ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 7 → ZMod 3)) =>
        (((A : ↥Xg) : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3))) hq
      simp only [hΦ] at e
      obtain ⟨⟨σ, hσ⟩, ⟨s, hs, hs'⟩⟩ := q
      obtain ⟨⟨σ', hσ''⟩, ⟨s', hs'', hs'''⟩⟩ := q'
      have h1 := perm_eq_of_spMat_eq hs e
      have h2 := sign_eq_of_spMat_eq7 hs e
      subst h1; subst h2
      rfl
    · rintro ⟨⟨A, hA⟩, hAs⟩
      rw [MulAction.mem_stabilizer_iff, hsm] at hAs
      obtain ⟨σ, s, hs, ⟨hσ0, hp⟩, hAe⟩ := h.mem_H_of_mulVec_e0 hA (c := 1)
        (by rw [hAs, one_smul])
      have hs0 : s 0 = 1 := by
        have e := congrFun hAs 0
        rwa [hAe, spMat_mulVec_single, hσ0, Pi.single_eq_same, Pi.single_eq_same, mul_one] at e
      refine ⟨(⟨σ, hσ0⟩, ⟨s, hs, hs0, hp⟩), ?_⟩
      apply Subtype.ext; apply Subtype.ext; apply Units.ext
      rw [hΦ]
      exact hAe.symm
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod, card_perm_fix_zero7,
    card_signs7]

theorem card_eq_orbit (h : N6MatHyp Xg) :
    Nat.card Xg = {v : Fin 7 → ZMod 3 | O6 Xg v}.ncard * 23040 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 7 → ZMod 3))
  rw [MulAction.index_stabilizer, h.card_stab] at h1
  have h2 : MulAction.orbit ↥Xg (Pi.single 0 1 : Fin 7 → ZMod 3) = {v | O6 Xg v} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, O6, Subgroup.smul_def,
      Units.smul_def, Matrix.smul_eq_mulVec]
    constructor
    · rintro ⟨⟨A, hA⟩, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨⟨A, hA⟩, rfl⟩
  rw [h2] at h1
  rw [← h1, mul_comm]

theorem u2_sub (h : N6MatHyp Xg) {v : Fin 7 → ZMod 3} (hv0 : v 0 = 0)
    (hv : wt v = 2) : O6 Xg v := by
  obtain ⟨u, hu, hu0, hwu⟩ := h.exists_U2
  refine (h.o6_iff_of_rep6_eq ?_).mpr hu
  have hwr : ∀ w : Fin 7 → ZMod 3, w 0 = 0 → wt w = 2 → wtR w = 2 := fun w hw0 hw => by
    rw [wt_eq_wtR, if_neg (not_not.mpr hw0), zero_add] at hw
    exact hw
  rw [hwr v hv0 hv, hwr u hu0 hwu, decide_eq_true hv0, decide_eq_true hu0]
  exact rep6_indep (by norm_num) _ _

theorem o6_iff (h : N6MatHyp Xg) (v : Fin 7 → ZMod 3) : O6 Xg v ↔
    ((v 0 ≠ 0 ∧ wtR v = 0) ∨ (v 0 = 0 ∧ wtR v = 2) ∨
      ((v 0 ≠ 0 ∧ wtR v = 1) ∧ O6 Xg (rep6 false 1 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 2) ∧ O6 Xg (rep6 false 2 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 3) ∧ O6 Xg (rep6 false 3 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 4) ∧ O6 Xg (rep6 false 4 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 5) ∧ O6 Xg (rep6 false 5 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = 1) ∧ O6 Xg (rep6 false 6 1)) ∨
      ((v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = -1) ∧ O6 Xg (rep6 false 6 (-1)))) := by
  rw [h.o6_iff_rep6 v]
  have hk6 := wtR_le v
  by_cases hv0 : v 0 = 0
  · rw [decide_eq_true hv0]
    simp only [hv0, ne_eq, not_true_eq_false, false_and, false_or, true_and, or_false]
    constructor
    · intro ho
      by_cases hk : wtR v = 6
      · have := h.wt_two_of_O6 ho rfl
        rw [wt_rep6_true _ hk6 (prod_ne_zero_of_wtR hk)] at this
        omega
      · have hε : rep6 true (wtR v) (∏ i : Fin 6, v i.succ) = rep6 true (wtR v) 1 :=
          rep6_indep (by omega) _ _
        rw [hε] at ho
        have := h.wt_two_of_O6 ho rfl
        rwa [wt_rep6_true _ hk6 one_ne_zero] at this
    · intro hk
      refine h.u2_sub rfl ?_
      rw [hk, rep6_indep (k := 2) (by norm_num) _ 1]
      decide
  · rw [decide_eq_false hv0]
    simp only [hv0, ne_eq, not_false_eq_true, true_and, false_and, false_or]
    generalize hk : wtR v = k at hk6
    have hε : ∀ k' < 6, rep6 false k' (∏ i : Fin 6, v i.succ) = rep6 false k' 1 :=
      fun k' hk' => rep6_indep hk' _ _
    interval_cases k
    · simp only [true_or, iff_true]
      rw [show rep6 false 0 (∏ i : Fin 6, v i.succ) = Pi.single 0 1 by
        rw [hε 0 (by norm_num)]; decide]
      exact o6_e0
    · rw [hε 1 (by norm_num)]; simp
    · rw [hε 2 (by norm_num)]; simp
    · rw [hε 3 (by norm_num)]; simp
    · rw [hε 4 (by norm_num)]; simp
    · rw [hε 5 (by norm_num)]; simp
    · have hp := prod_ne_zero_of_wtR hk
      rcases eq_one_or_of_ne_zero hp with hp1 | hp1
      · rw [hp1]; simp [show (1 : ZMod 3) ≠ -1 by decide]
      · rw [hp1]; simp [show (-1 : ZMod 3) ≠ 1 by decide]

end N6MatHyp

theorem card_GL7 : ∏ i : Fin 7, (3 ^ 7 - 3 ^ (i : ℕ)) = 134068444202678083338240 := by
  decide +kernel

theorem lagrange_six (b1 b2 b3 b4 b5 bp bm : Prop) [Decidable b1] [Decidable b2] [Decidable b3]
    [Decidable b4] [Decidable b5] [Decidable bp] [Decidable bm] (h12 : b1 → b2)
    (h21 : b2 → b1 ∧ b3 ∧ b4 ∧ b5)
    (h : (2 + 60 + (if b1 then 24 else 0) + (if b2 then 120 else 0) + (if b3 then 320 else 0) +
      (if b4 then 480 else 0) + (if b5 then 384 else 0) + (if bp then 64 else 0) +
      (if bm then 64 else 0)) * 23040 ∣ 134068444202678083338240) :
    ¬ b1 ∧ ¬ b2 ∧ ¬ b3 ∧ ¬ b4 ∧ ¬ b5 ∧ (bp ↔ ¬ bm) := by
  by_cases hb2 : b2
  · exfalso
    obtain ⟨hb1, hb3, hb4, hb5⟩ := h21 hb2
    by_cases hp : bp <;> by_cases hm : bm <;>
      simp only [hb1, hb2, hb3, hb4, hb5, hp, hm, ite_true, ite_false] at h <;>
      exact absurd h (by decide)
  · have hb1 : ¬ b1 := fun h1 => hb2 (h12 h1)
    by_cases h3 : b3 <;> by_cases h4 : b4 <;> by_cases h5 : b5 <;> by_cases hp : bp <;>
      by_cases hm : bm <;> simp only [hb1, hb2, h3, h4, h5, hp, hm, ite_true, ite_false] at h <;>
      first
      | exact absurd h (by decide)
      | exact ⟨hb1, hb2, h3, h4, h5, by simp [hp, hm]⟩

@[expose] def orbPred (b1 b2 b3 b4 b5 bp bm : Prop) (v : Fin 7 → ZMod 3) : Prop :=
  (v 0 ≠ 0 ∧ wtR v = 0) ∨ (v 0 = 0 ∧ wtR v = 2) ∨
    ((v 0 ≠ 0 ∧ wtR v = 1) ∧ b1) ∨ ((v 0 ≠ 0 ∧ wtR v = 2) ∧ b2) ∨
    ((v 0 ≠ 0 ∧ wtR v = 3) ∧ b3) ∨ ((v 0 ≠ 0 ∧ wtR v = 4) ∧ b4) ∨
    ((v 0 ≠ 0 ∧ wtR v = 5) ∧ b5) ∨
    ((v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = 1) ∧ bp) ∨
    ((v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = -1) ∧ bm)

theorem ncard_orbPred (b1 b2 b3 b4 b5 bp bm : Prop) [Decidable b1] [Decidable b2] [Decidable b3]
    [Decidable b4] [Decidable b5] [Decidable bp] [Decidable bm] :
    {v | orbPred b1 b2 b3 b4 b5 bp bm v}.ncard = 2 + 60 + (if b1 then 24 else 0) +
      (if b2 then 120 else 0) + (if b3 then 320 else 0) + (if b4 then 480 else 0) +
      (if b5 then 384 else 0) + (if bp then 64 else 0) + (if bm then 64 else 0) := by
  unfold orbPred
  rw [ncard_setOf_or7 ?_, ncard_setOf_or7 ?_, ncard_setOf_or7 ?_, ncard_setOf_or7 ?_,
    ncard_setOf_or7 ?_, ncard_setOf_or7 ?_, ncard_setOf_or7 ?_, ncard_setOf_or7 ?_]
  · rw [ncard_setOf_and7, ncard_setOf_and7, ncard_setOf_and7, ncard_setOf_and7, ncard_setOf_and7,
      ncard_setOf_and7, ncard_setOf_and7, ncard_of_card7 card_B0, ncard_of_card7 card_U2,
      ncard_of_card7 card_M1, ncard_of_card7 card_M2, ncard_of_card7 card_M3,
      ncard_of_card7 card_M4, ncard_of_card7 card_M5, ncard_of_card7 card_M6p,
      ncard_of_card7 card_M6m]
    ring
  all_goals
    intro v hA hR
    simp_all [show (-1 : ZMod 3) ≠ 1 by decide]

theorem orbPred_iff {b1 b2 b3 b4 b5 bp bm : Prop} (h1 : ¬ b1) (h2 : ¬ b2) (h3 : ¬ b3)
    (h4 : ¬ b4) (h5 : ¬ b5) (hpm : bp ↔ ¬ bm) [Decidable bp] (v : Fin 7 → ZMod 3) :
    orbPred b1 b2 b3 b4 b5 bp bm v ↔ ((v 0 ≠ 0 ∧ wtR v = 0) ∨ (v 0 = 0 ∧ wtR v = 2) ∨
      (v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = if bp then 1 else -1)) := by
  unfold orbPred
  by_cases hp : bp
  · have hm : ¬ bm := hpm.mp hp
    simp only [h1, h2, h3, h4, h5, hp, hm, ite_true, and_false, and_true, or_false, false_or]
  · have hm : bm := by tauto
    simp only [h1, h2, h3, h4, h5, hp, hm, ite_false, and_false, and_true, false_or]

theorem orbit_shape_iff (v : Fin 7 → ZMod 3) (δ : ZMod 3) :
    ((v 0 ≠ 0 ∧ wtR v = 0) ∨ (v 0 = 0 ∧ wtR v = 2) ∨
      (v 0 ≠ 0 ∧ wtR v = 6 ∧ ∏ i : Fin 6, v i.succ = δ)) ↔
      ((wt v = 1 ∧ v 0 ≠ 0) ∨ (wt v = 2 ∧ v 0 = 0) ∨ (wt v = 7 ∧ ∏ i : Fin 6, v i.succ = δ)) := by
  have hle := wtR_le v
  rw [wt_eq_wtR]
  by_cases hv0 : v 0 = 0
  · have e : (if v 0 ≠ 0 then 1 else 0) = 0 := if_neg (not_not.mpr hv0)
    rw [e, zero_add]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩)
      · exact absurd hv0 h1
      · exact Or.inr (Or.inl ⟨h2, hv0⟩)
      · exact absurd hv0 h1
    · rintro (⟨-, h1⟩ | ⟨h2, -⟩ | ⟨h7, -⟩)
      · exact absurd hv0 h1
      · exact Or.inr (Or.inl ⟨hv0, h2⟩)
      · omega
  · have e : (if v 0 ≠ 0 then 1 else 0) = 1 := if_pos hv0
    rw [e]
    constructor
    · rintro (⟨-, h0⟩ | ⟨h1, -⟩ | ⟨-, h6, hp⟩)
      · exact Or.inl ⟨by omega, hv0⟩
      · exact absurd h1 hv0
      · exact Or.inr (Or.inr ⟨by omega, hp⟩)
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h7, hp⟩)
      · exact Or.inl ⟨hv0, by omega⟩
      · exact absurd h2 hv0
      · exact Or.inr (Or.inr ⟨hv0, by omega, hp⟩)

theorem orbit_evenN0_six (Xg : Subgroup (GL (Fin 7) (ZMod 3))) (h : N6MatHyp Xg) :
    Nat.card Xg = 2903040 ∧ ∃ δ : ZMod 3, (δ = 1 ∨ δ = -1) ∧ ∀ v : Fin 7 → ZMod 3,
      O6 Xg v ↔ ((wt v = 1 ∧ v 0 ≠ 0) ∨ (wt v = 2 ∧ v 0 = 0) ∨
        (wt v = 7 ∧ ∏ i : Fin 6, v i.succ = δ)) := by
  classical
  have hO : ∀ v, O6 Xg v ↔ orbPred (O6 Xg (rep6 false 1 1)) (O6 Xg (rep6 false 2 1))
      (O6 Xg (rep6 false 3 1)) (O6 Xg (rep6 false 4 1)) (O6 Xg (rep6 false 5 1))
      (O6 Xg (rep6 false 6 1)) (O6 Xg (rep6 false 6 (-1))) v := h.o6_iff
  have hX := h.card_eq_orbit
  rw [show {v : Fin 7 → ZMod 3 | O6 Xg v} = {v | orbPred (O6 Xg (rep6 false 1 1))
      (O6 Xg (rep6 false 2 1)) (O6 Xg (rep6 false 3 1)) (O6 Xg (rep6 false 4 1))
      (O6 Xg (rep6 false 5 1)) (O6 Xg (rep6 false 6 1)) (O6 Xg (rep6 false 6 (-1))) v} from
    Set.ext hO, ncard_orbPred] at hX
  have hdvd : Nat.card Xg ∣ 134068444202678083338240 := by
    have := Subgroup.card_subgroup_dvd_card Xg
    rwa [Matrix.card_GL_field, ZMod.card, card_GL7] at this
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hpm⟩ := lagrange_six _ _ _ _ _ _ _
    (fun h1 => h.o6_rep2_of_rep1 h1) (fun h2 => h.of_o6_rep2 h2) (hX ▸ hdvd)
  refine ⟨?_, if O6 Xg (rep6 false 6 1) then 1 else -1, ?_, fun v => ?_⟩
  · rw [hX]
    by_cases hp : O6 Xg (rep6 false 6 1)
    · simp [hb1, hb2, hb3, hb4, hb5, hp, hpm.mp hp]
    · simp [hb1, hb2, hb3, hb4, hb5, hp, show O6 Xg (rep6 false 6 (-1)) by tauto]
  · split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [hO v, orbPred_iff hb1 hb2 hb3 hb4 hb5 hpm v, orbit_shape_iff]

end CFSG.StandardType.FrameRoute.FS81

end
