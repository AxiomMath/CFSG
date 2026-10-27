module

public import CFSG.Quasithin.Vol2.Ch3Sec3HatCode
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.HatM

open CFSG.Quasithin.H13.HatC
open CFSG.Quasithin (fixV mem_fixV)

@[expose] def g1c : List ℕ := [4, 8, 16, 32, 21, 42]

@[expose] def g1i : List ℕ := [21, 42, 1, 2, 4, 8]

@[expose] def g2c : List ℕ := [16, 32, 4, 8, 57, 30]

@[expose] def g2i : List ℕ := [27, 45, 4, 8, 1, 2]

@[expose] def sgc : List ℕ := [1, 3, 4, 12, 16, 48]

@[expose] def omc : List ℕ := [2, 3, 8, 12, 32, 48]

@[expose] def omi : List ℕ := [3, 1, 12, 4, 48, 16]

@[expose] def S0l : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [1, 2, 21, 42, 16, 32], [1, 3, 4, 12, 16, 48], [1, 3, 21, 63, 16, 48],
    [4, 8, 1, 2, 21, 42], [4, 8, 16, 32, 21, 42], [4, 12, 1, 3, 21, 63], [4, 12, 16, 48, 21, 63],
    [16, 32, 4, 8, 1, 2], [16, 32, 21, 42, 1, 2], [16, 48, 4, 12, 1, 3], [16, 48, 21, 63, 1, 3],
    [21, 42, 1, 2, 4, 8], [21, 42, 16, 32, 4, 8], [21, 63, 1, 3, 4, 12], [21, 63, 16, 48, 4, 12]]

@[expose] def D0l : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [1, 2, 21, 42, 16, 32], [4, 8, 1, 2, 21, 42], [4, 8, 16, 32, 21, 42],
    [16, 32, 4, 8, 1, 2], [16, 32, 21, 42, 1, 2], [21, 42, 1, 2, 4, 8], [21, 42, 16, 32, 4, 8]]

@[expose] def Pw : List (List ℕ × List ℕ) := [
    ([1, 2, 4, 8, 16, 32], []), ([1, 2, 21, 42, 16, 32], [1, 2, 0, 1, 2, 0, 1]),
    ([1, 2, 39, 57, 16, 32], [0, 1, 2, 1, 1, 2, 1, 0, 0, 0]),
    ([1, 2, 54, 27, 16, 32], [0, 0, 0, 1, 2, 1, 1, 2, 1, 0]), ([1, 3, 4, 12, 16, 48], [2]),
    ([1, 3, 21, 63, 16, 48], [2, 1, 2, 0, 1, 2, 0, 1]),
    ([1, 3, 39, 30, 16, 48], [1, 1, 1, 1, 0, 1, 1, 2, 1, 0]),
    ([1, 3, 54, 45, 16, 48], [1, 1, 0, 1, 2, 1, 1, 0, 1]),
    ([4, 8, 1, 2, 21, 42], [0, 1, 2, 0, 1, 2, 0, 1]), ([4, 8, 16, 32, 21, 42], [0]),
    ([4, 8, 39, 57, 21, 42], [1, 2, 1, 1, 2, 1, 0]),
    ([4, 8, 54, 27, 21, 42], [1, 1, 2, 1, 2, 1, 1, 0]),
    ([4, 12, 1, 3, 21, 63], [2, 0, 1, 2, 0, 1, 2, 0, 1]), ([4, 12, 16, 48, 21, 63], [2, 0]),
    ([4, 12, 39, 30, 21, 63], [1, 2, 1, 1, 2, 1, 2, 0]),
    ([4, 12, 54, 45, 21, 63], [2, 1, 2, 1, 1, 2, 1, 0]),
    ([16, 32, 4, 8, 1, 2], [1, 2, 0, 1, 2, 0, 1, 0, 0]), ([16, 32, 21, 42, 1, 2], [0, 0]),
    ([16, 32, 39, 57, 1, 2], [0, 1, 1, 2, 1, 2, 1, 1, 0]),
    ([16, 32, 54, 27, 1, 2], [0, 1, 2, 1, 1, 2, 1, 0]),
    ([16, 48, 4, 12, 1, 3], [2, 1, 2, 0, 1, 2, 0, 1, 0, 0]), ([16, 48, 21, 63, 1, 3], [2, 0, 0]),
    ([16, 48, 39, 30, 1, 3], [2, 0, 1, 2, 1, 1, 2, 1, 0]),
    ([16, 48, 54, 45, 1, 3], [0, 1, 2, 1, 1, 2, 1, 2, 0]), ([21, 42, 1, 2, 4, 8], [0, 0, 0]),
    ([21, 42, 16, 32, 4, 8], [1, 2, 0, 1, 2, 0, 1, 0]),
    ([21, 42, 39, 57, 4, 8], [0, 0, 1, 2, 1, 1, 2, 1, 0]),
    ([21, 42, 54, 27, 4, 8], [1, 2, 1, 1, 2, 1, 0, 0, 0]), ([21, 63, 1, 3, 4, 12], [2, 0, 0, 0]),
    ([21, 63, 16, 48, 4, 12], [2, 1, 2, 0, 1, 2, 0, 1, 0]),
    ([21, 63, 39, 30, 4, 12], [2, 1, 2, 1, 1, 2, 1, 0, 0, 0]),
    ([21, 63, 54, 45, 4, 12], [1, 2, 1, 1, 0, 1, 1, 1, 1]),
    ([39, 30, 1, 3, 54, 45], [2, 0, 1, 2, 1, 1, 2, 1, 0, 0]),
    ([39, 30, 4, 12, 54, 45], [2, 1, 2, 1, 1, 2, 1]),
    ([39, 30, 16, 48, 54, 45], [0, 1, 2, 1, 1, 2, 1, 2]),
    ([39, 30, 21, 63, 54, 45], [1, 2, 1, 1, 2, 1, 2, 0, 0]),
    ([39, 57, 1, 2, 54, 27], [0, 0, 0, 1, 2, 1, 1, 2, 1]),
    ([39, 57, 4, 8, 54, 27], [1, 1, 2, 1, 2, 1, 1]),
    ([39, 57, 16, 32, 54, 27], [0, 1, 2, 1, 1, 2, 1]),
    ([39, 57, 21, 42, 54, 27], [1, 2, 1, 1, 2, 1, 0, 0]),
    ([54, 27, 1, 2, 39, 57], [0, 1, 2, 1, 1, 2, 1, 0, 0]),
    ([54, 27, 4, 8, 39, 57], [1, 2, 1, 1, 2, 1]),
    ([54, 27, 16, 32, 39, 57], [0, 1, 1, 2, 1, 2, 1, 1]),
    ([54, 27, 21, 42, 39, 57], [0, 0, 1, 2, 1, 1, 2, 1]),
    ([54, 45, 1, 3, 39, 30], [1, 1, 1, 1, 0, 1, 1, 2, 1]),
    ([54, 45, 4, 12, 39, 30], [1, 2, 1, 1, 2, 1, 2]),
    ([54, 45, 16, 48, 39, 30], [2, 0, 1, 2, 1, 1, 2, 1]),
    ([54, 45, 21, 63, 39, 30], [2, 1, 2, 1, 1, 2, 1, 0, 0])]

@[expose] def Rl : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [1, 2, 21, 42, 16, 32], [1, 3, 4, 12, 16, 48], [1, 3, 21, 63, 16, 48],
    [16, 32, 4, 8, 1, 2], [16, 32, 21, 42, 1, 2], [16, 48, 4, 12, 1, 3], [16, 48, 21, 63, 1, 3]]

@[expose] def RGl : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [1, 2, 21, 42, 16, 32], [16, 32, 4, 8, 1, 2], [16, 32, 21, 42, 1, 2]]

@[expose] def A0l : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [4, 8, 1, 2, 21, 42], [16, 32, 21, 42, 1, 2], [21, 42, 16, 32, 4, 8]]

@[expose] def sg1w : List ℕ := [0]

@[expose] def sg2w : List ℕ := [0, 1, 1, 1, 1, 0]

@[expose] def pa : List ℕ := [1, 2, 39, 57, 16, 32]

@[expose] def pb : List ℕ := [4, 8, 1, 2, 21, 42]

@[expose] def InvPair (m m' : List ℕ) : Prop :=
  (∀ c < 64, mact m (mact m' c) = c ∧ mact m' (mact m c) = c) ∧
    (∀ k < 6, m.getD k 0 < 64) ∧ (∀ k < 6, m'.getD k 0 < 64)

instance (m m' : List ℕ) : Decidable (InvPair m m') := by unfold InvPair; infer_instance

theorem pair_g1 : InvPair g1c g1i := by decide +kernel
theorem pair_g2 : InvPair g2c g2i := by decide +kernel
theorem pair_sg : InvPair sgc sgc := by decide +kernel
theorem pair_om : InvPair omc omi := by decide +kernel

@[expose] def hg1 : MulAut W6 := caut g1c g1i pair_g1.1 pair_g1.2.1 pair_g1.2.2
@[expose] def hg2 : MulAut W6 := caut g2c g2i pair_g2.1 pair_g2.2.1 pair_g2.2.2
@[expose] def hsg : MulAut W6 := caut sgc sgc pair_sg.1 pair_sg.2.1 pair_sg.2.2
@[expose] def hom : MulAut W6 := caut omc omi pair_om.1 pair_om.2.1 pair_om.2.2

theorem mcode_hg1 : mcode ⇑hg1 = g1c := mcode_caut _ _ _ _ _ rfl
theorem mcode_hg2 : mcode ⇑hg2 = g2c := mcode_caut _ _ _ _ _ rfl
theorem mcode_hsg : mcode ⇑hsg = sgc := mcode_caut _ _ _ _ _ rfl
theorem mcode_hom : mcode ⇑hom = omc := mcode_caut _ _ _ _ _ rfl

@[expose] def gen (i : ℕ) : MulAut W6 := if i = 0 then hg1 else if i = 1 then hg2 else hsg

@[expose] def genc (i : ℕ) : List ℕ := if i = 0 then g1c else if i = 1 then g2c else sgc

theorem mcode_gen (i : ℕ) : mcode ⇑(gen i) = genc i := by
  unfold gen genc
  split_ifs
  · exact mcode_hg1
  · exact mcode_hg2
  · exact mcode_hsg

@[expose] def welt : List ℕ → MulAut W6
  | [] => 1
  | i :: w => gen i * welt w

@[expose] def wval : List ℕ → List ℕ
  | [] => idc
  | i :: w => mmul (genc i) (wval w)

theorem mcode_welt (w : List ℕ) : mcode ⇑(welt w) = wval w := by
  induction w with
  | nil => exact mcode_one
  | cons i w ih => rw [welt, wval, mcode_mul, mcode_gen, ih]

@[expose] def Gam0 : Subgroup (MulAut W6) := Subgroup.closure {hg1, hg2}

@[expose] def Nor0 : Subgroup (MulAut W6) := Subgroup.closure {hg1, hg2, hsg}

theorem gen_mem_Nor0 (i : ℕ) : gen i ∈ Nor0 := by
  unfold gen
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem welt_mem_Nor0 (w : List ℕ) : welt w ∈ Nor0 := by
  induction w with
  | nil => exact Nor0.one_mem
  | cons i w ih => exact Nor0.mul_mem (gen_mem_Nor0 i) ih

theorem welt_mem_Gam0 (w : List ℕ) (h : ∀ i ∈ w, i < 2) : welt w ∈ Gam0 := by
  induction w with
  | nil => exact Gam0.one_mem
  | cons i w ih =>
    refine Gam0.mul_mem ?_ (ih fun j hj => h j (List.mem_cons_of_mem i hj))
    have hi := h i List.mem_cons_self
    unfold gen
    split_ifs with h0 h1
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · omega

theorem Gam0_le_Nor0 : Gam0 ≤ Nor0 :=
  Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx ⊢; tauto)

theorem comm_of_code {x y : MulAut W6}
    (h : mmul (mcode ⇑x) (mcode ⇑y) = mmul (mcode ⇑y) (mcode ⇑x)) :
    x * y = y * x :=
  mcode_injective (by rw [mcode_mul, mcode_mul, h])

theorem code_comm : mmul g1c omc = mmul omc g1c ∧ mmul g2c omc = mmul omc g2c ∧
    mmul sgc omc = mmul (mmul omc omc) sgc ∧ mmul omc omc ≠ omc ∧ mmul sgc sgc = idc := by
  decide +kernel

theorem comm_hom {x : MulAut W6} (hx : x ∈ Gam0) : x * hom = hom * x := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact comm_of_code (by rw [mcode_hg1, mcode_hom]; exact code_comm.1)
    · exact comm_of_code (by rw [mcode_hg2, mcode_hom]; exact code_comm.2.1)
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    calc a⁻¹ * hom = a⁻¹ * (hom * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * hom) * a⁻¹ := by rw [ha]
      _ = hom * a⁻¹ := by group

theorem hsg_hom : hsg * hom = hom * hom * hsg := by
  apply mcode_injective
  rw [mcode_mul, mcode_mul, mcode_mul, mcode_hsg, mcode_hom]
  exact code_comm.2.2.1

theorem hom_ne : hom * hom ≠ hom := fun h => by
  have := congrArg (fun g : MulAut W6 => mcode ⇑g) h
  simp only [mcode_mul, mcode_hom] at this
  exact code_comm.2.2.2.1 this

theorem hsg_not_mem_Gam0 : hsg ∉ Gam0 := fun h => by
  have h1 := comm_hom h
  rw [hsg_hom] at h1
  exact hom_ne (mul_right_cancel h1)

theorem hsg_sq : hsg * hsg = 1 := by
  apply mcode_injective
  rw [mcode_mul, mcode_hsg, mcode_one]
  exact code_comm.2.2.2.2

theorem code_sg : wval sg1w = mmul (mmul sgc g1c) sgc ∧ wval sg2w = mmul (mmul sgc g2c) sgc ∧
    (∀ i ∈ sg1w, i < 2) ∧ (∀ i ∈ sg2w, i < 2) := by
  decide +kernel

theorem hsg_conj_mem {x : MulAut W6} (hx : x ∈ Gam0) : hsg * x * hsg ∈ Gam0 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · have e : hsg * hg1 * hsg = welt sg1w := by
        apply mcode_injective
        rw [mcode_welt, mcode_mul, mcode_mul, mcode_hsg, mcode_hg1]
        exact code_sg.1.symm
      rw [e]
      exact welt_mem_Gam0 _ code_sg.2.2.1
    · have e : hsg * hg2 * hsg = welt sg2w := by
        apply mcode_injective
        rw [mcode_welt, mcode_mul, mcode_mul, mcode_hsg, mcode_hg2]
        exact code_sg.2.1.symm
      rw [e]
      exact welt_mem_Gam0 _ code_sg.2.2.2
  | one => rw [mul_one, hsg_sq]; exact Gam0.one_mem
  | mul a b _ _ ha hb =>
    have e : hsg * (a * b) * hsg = (hsg * a * hsg) * (hsg * b * hsg) := by
      calc hsg * (a * b) * hsg = hsg * a * (hsg * hsg) * b * hsg := by rw [hsg_sq]; group
        _ = _ := by group
    rw [e]
    exact Gam0.mul_mem ha hb
  | inv a _ ha =>
    have e : hsg * a⁻¹ * hsg = (hsg * a * hsg)⁻¹ := by
      have hsi : hsg⁻¹ = hsg := inv_eq_of_mul_eq_one_right hsg_sq
      rw [mul_inv_rev, mul_inv_rev, hsi, mul_assoc]
    rw [e]
    exact Gam0.inv_mem ha

theorem mem_Nor0_iff {x : MulAut W6} : x ∈ Nor0 ↔ x ∈ Gam0 ∨ hsg * x ∈ Gam0 := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inr (by rw [hsg_sq]; exact Gam0.one_mem)
    | one => exact Or.inl Gam0.one_mem
    | mul a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (Gam0.mul_mem ha hb)
      · refine Or.inr ?_
        have e : hsg * (a * b) = (hsg * a * hsg) * (hsg * b) := by
          calc hsg * (a * b) = hsg * a * (hsg * hsg) * b := by rw [hsg_sq, mul_one, mul_assoc]
            _ = _ := by group
        rw [e]
        exact Gam0.mul_mem (hsg_conj_mem ha) hb
      · refine Or.inr ?_
        rw [← mul_assoc]
        exact Gam0.mul_mem ha hb
      · refine Or.inl ?_
        have e : a * b = (hsg * (hsg * a) * hsg) * (hsg * b) := by
          calc a * b = (hsg * hsg) * a * (hsg * hsg) * b := by rw [hsg_sq]; group
            _ = _ := by group
        rw [e]
        exact Gam0.mul_mem (hsg_conj_mem ha) hb
    | inv a _ ha =>
      rcases ha with ha | ha
      · exact Or.inl (Gam0.inv_mem ha)
      · refine Or.inr ?_
        have e : hsg * a⁻¹ = hsg * (hsg * a)⁻¹ * hsg := by
          have hsi : hsg⁻¹ = hsg := inv_eq_of_mul_eq_one_right hsg_sq
          rw [mul_inv_rev, hsi]
          calc hsg * a⁻¹ = hsg * a⁻¹ * (hsg * hsg) := by rw [hsg_sq, mul_one]
            _ = _ := by group
        rw [e]
        exact hsg_conj_mem (Gam0.inv_mem ha)
  · rintro (h | h)
    · exact Gam0_le_Nor0 h
    · have e : x = hsg * (hsg * x) := by rw [← mul_assoc, hsg_sq, one_mul]
      rw [e]
      exact Nor0.mul_mem (gen_mem_Nor0 2) (Gam0_le_Nor0 h)

theorem mem_Gam0_iff {x : MulAut W6} (hx : x ∈ Nor0) : x ∈ Gam0 ↔ x * hom = hom * x := by
  refine ⟨comm_hom, fun hc => ?_⟩
  rcases mem_Nor0_iff.mp hx with h | h
  · exact h
  · exfalso
    have h1 := comm_hom h
    have e : hsg * x * hom = hom * hom * (hsg * x) := by
      calc hsg * x * hom = hsg * (x * hom) := mul_assoc _ _ _
        _ = hsg * (hom * x) := by rw [hc]
        _ = (hsg * hom) * x := (mul_assoc _ _ _).symm
        _ = (hom * hom * hsg) * x := by rw [hsg_hom]
        _ = hom * hom * (hsg * x) := mul_assoc _ _ _
    have h2 : hom * hom * (hsg * x) = hom * (hsg * x) := e.symm.trans h1
    exact hom_ne (mul_right_cancel h2)

@[expose] def codeSub (l : List (List ℕ)) (h1 : idc ∈ l) (hmul : ∀ a ∈ l, ∀ b ∈ l, mmul a b ∈ l) :
    Subgroup (MulAut W6) where
  carrier := {x | mcode ⇑x ∈ l}
  mul_mem' := fun {x y} hx hy => by
    show mcode ⇑(x * y) ∈ l
    rw [mcode_mul]
    exact hmul _ hx _ hy
  one_mem' := by
    show mcode ⇑(1 : MulAut W6) ∈ l
    rw [mcode_one]
    exact h1
  inv_mem' := fun {x} hx => by
    have hpow : ∀ k : ℕ, mcode ⇑(x ^ k) ∈ l := by
      intro k
      induction k with
      | zero => rw [pow_zero, mcode_one]; exact h1
      | succ k ih => rw [pow_succ, mcode_mul]; exact hmul _ ih _ hx
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel
        (orderOf_pos x), pow_orderOf_eq_one]
    show mcode ⇑x⁻¹ ∈ l
    rw [e]
    exact hpow _

theorem card_codeSub {l : List (List ℕ)} {h1} {hmul} (hnd : l.Nodup)
    (hw : ∀ c ∈ l, ∃ w : List ℕ, wval w = c) : Nat.card (codeSub l h1 hmul) = l.length := by
  classical
  have hbij : Function.Bijective (fun x : codeSub l h1 hmul =>
      (⟨mcode ⇑(x : MulAut W6), x.2⟩ : {c // c ∈ l})) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (mcode_injective (congrArg Subtype.val hxy))
    · rintro ⟨c, hc⟩
      obtain ⟨w, hw⟩ := hw c hc
      exact ⟨⟨welt w, show mcode ⇑(welt w) ∈ l by rw [mcode_welt, hw]; exact hc⟩,
        Subtype.ext (by simp [mcode_welt, hw])⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_congr (Equiv.subtypeEquivRight
    (fun c => (List.mem_toFinset (l := l) (a := c)).symm)), Nat.card_eq_fintype_card,
    Fintype.card_coe, List.toFinset_card_of_nodup hnd]

@[expose] def Pl : List (List ℕ) := Pw.map Prod.fst

theorem chk_S0 : idc ∈ S0l ∧ (∀ a ∈ S0l, ∀ b ∈ S0l, mmul a b ∈ S0l) ∧ S0l.Nodup ∧
    S0l.length = 16 := by decide +kernel

theorem chk_D0 : idc ∈ D0l ∧ (∀ a ∈ D0l, ∀ b ∈ D0l, mmul a b ∈ D0l) ∧ D0l.Nodup ∧
    D0l.length = 8 := by decide +kernel

theorem chk_P : idc ∈ Pl ∧ (∀ a ∈ Pl, ∀ b ∈ Pl, mmul a b ∈ Pl) ∧ Pl.Nodup ∧
    Pl.length = 48 := by decide +kernel

theorem chk_R : idc ∈ Rl ∧ (∀ a ∈ Rl, ∀ b ∈ Rl, mmul a b ∈ Rl) ∧ Rl.Nodup ∧
    Rl.length = 8 := by decide +kernel

theorem chk_A0 : idc ∈ A0l ∧ (∀ a ∈ A0l, ∀ b ∈ A0l, mmul a b ∈ A0l) ∧ A0l.Nodup ∧
    A0l.length = 4 := by decide +kernel

theorem chk_incl : (∀ c ∈ S0l, c ∈ Pl) ∧ (∀ c ∈ D0l, c ∈ S0l) ∧ (∀ c ∈ Rl, c ∈ S0l) ∧
    (∀ c ∈ A0l, c ∈ S0l) ∧ (∀ p ∈ Pw, wval p.2 = p.1) := by decide +kernel

theorem word_of_Pl {c : List ℕ} (hc : c ∈ Pl) : ∃ w, wval w = c := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact ⟨p.2, chk_incl.2.2.2.2 p hp⟩

@[expose] def S0 : Subgroup (MulAut W6) := codeSub S0l chk_S0.1 chk_S0.2.1
@[expose] def D0 : Subgroup (MulAut W6) := codeSub D0l chk_D0.1 chk_D0.2.1
@[expose] def P0 : Subgroup (MulAut W6) := codeSub Pl chk_P.1 chk_P.2.1
@[expose] def R0 : Subgroup (MulAut W6) := codeSub Rl chk_R.1 chk_R.2.1
@[expose] def A0 : Subgroup (MulAut W6) := codeSub A0l chk_A0.1 chk_A0.2.1

theorem card_S0 : Nat.card S0 = 16 := by
  rw [S0, card_codeSub chk_S0.2.2.1 fun c hc => word_of_Pl (chk_incl.1 c hc)]
  exact chk_S0.2.2.2

theorem card_P0 : Nat.card P0 = 48 := by
  rw [P0, card_codeSub chk_P.2.2.1 fun c hc => word_of_Pl hc]
  exact chk_P.2.2.2

theorem card_R0 : Nat.card R0 = 8 := by
  rw [R0, card_codeSub chk_R.2.2.1 fun c hc => word_of_Pl (chk_incl.1 c (chk_incl.2.2.1 c hc))]
  exact chk_R.2.2.2

theorem card_D0 : Nat.card D0 = 8 := by
  rw [D0, card_codeSub chk_D0.2.2.1 fun c hc => word_of_Pl (chk_incl.1 c (chk_incl.2.1 c hc))]
  exact chk_D0.2.2.2

theorem mem_Nor0_of_code {x : MulAut W6} (hx : mcode ⇑x ∈ Pl) : x ∈ Nor0 := by
  obtain ⟨w, hw⟩ := word_of_Pl hx
  have : x = welt w := mcode_injective (by rw [mcode_welt, hw])
  rw [this]
  exact welt_mem_Nor0 w

theorem P0_le_Nor0 : P0 ≤ Nor0 := fun _ hx => mem_Nor0_of_code hx
theorem S0_le_P0 : S0 ≤ P0 := fun _ hx => chk_incl.1 _ hx
theorem R0_le_S0 : R0 ≤ S0 := fun _ hx => chk_incl.2.2.1 _ hx

@[expose] def w0 : W6 := Multiplicative.ofAdd (dec 17)

@[expose] def orbw : List (ℕ × List ℕ) := [
    (5, [1, 0, 0, 0, 1]), (6, [1, 1]), (7, [0, 1, 1, 1, 0, 0, 1]), (9, [0, 0, 0, 1, 1, 1]),
    (10, [1, 1, 0, 1, 1, 0, 1]), (11, [0, 0, 0, 1, 0, 1]), (13, [0, 0, 1, 0, 0, 1]),
    (14, [0, 1]), (15, [1, 0, 1, 1, 1]), (17, []), (18, [1, 1, 0, 1]), (19, [0, 0, 1, 0, 1, 1]),
    (20, [0, 1, 0, 0, 0, 1]), (22, [0, 1, 0, 0, 1]), (23, [0, 0, 1, 1, 1]), (24, [0, 1, 1]),
    (25, [1, 1, 1, 0, 1]), (26, [0, 1, 0, 1]), (28, [1, 0, 0, 1, 0, 0, 1]),
    (29, [0, 1, 1, 0, 1]), (31, [0, 0, 0, 1]), (33, [0, 0, 1, 1, 0, 1]), (34, [1, 1, 0, 0, 1]),
    (35, [0, 1, 1, 0, 1, 1]), (36, [1, 1, 1]), (37, [1, 0, 1, 1, 0, 1]),
    (38, [1, 0, 0, 0, 1, 1]), (40, [0, 1, 1, 0, 1, 1, 0, 1]), (41, [1]), (43, [0, 0, 0, 1, 1]),
    (44, [1, 0, 1]), (46, [0, 0, 0, 1, 1, 0, 1]), (47, [1, 0, 0, 1]), (49, [1, 0, 1, 1]),
    (50, [0, 1, 0, 0, 0, 1, 1]), (51, [1, 0, 0, 1, 1]), (52, [0, 0, 0, 1, 0, 0, 1]),
    (53, [0, 0, 1, 1]), (55, [1, 1, 0, 1, 1]), (56, [0, 0, 1]), (58, [0, 1, 1, 1]),
    (59, [0, 1, 0, 1, 1]), (60, [0, 1, 0, 1, 1, 1]), (61, [0, 0, 1, 0, 1]),
    (62, [1, 1, 1, 0, 0, 1])]

theorem orb_checks : (∀ p ∈ orbw, mact (wval p.2) 17 = p.1 ∧ ∀ i ∈ p.2, i < 2) ∧
    (∀ p ∈ orbw, mact g1c p.1 ∈ orbw.map Prod.fst ∧ mact g2c p.1 ∈ orbw.map Prod.fst ∧
      mact sgc p.1 ∈ orbw.map Prod.fst) ∧ (orbw.map Prod.fst).Nodup ∧ orbw.length = 45 ∧
    (∀ p ∈ orbw, p.1 < 64) ∧
    (∀ c < 64, (∀ m ∈ D0l, mact m c = c) → c = 0 ∨ c = 17 ∨ c = 34 ∨ c = 51) ∧
    mact omc 17 = 34 ∧ mact omc 34 = 51 ∧ (∀ m ∈ Pl, mact m 17 = 17) := by
  decide +kernel

theorem not_mem_of_mem {x : MulAut W6} (hx : x ∈ Gam0) : x * hsg ∉ Gam0 := fun h => by
  apply hsg_not_mem_Gam0
  have e : hsg = x⁻¹ * (x * hsg) := by group
  rw [e]
  exact Gam0.mul_mem (Gam0.inv_mem hx) h

theorem relIndex_Gam0 : Gam0.relIndex Nor0 = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨hsg, gen_mem_Nor0 2⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : MulAut W6) ∈ Gam0
  · exact Or.inr ⟨hb, not_mem_of_mem hb⟩
  · refine Or.inl ⟨?_, hb⟩
    have h1 := (mem_Nor0_iff.mp b.2).resolve_left hb
    have e : (b : MulAut W6) * hsg = hsg * (hsg * b) * hsg := by
      rw [← mul_assoc, hsg_sq, one_mul]
    rw [e]
    exact hsg_conj_mem h1

theorem card_Nor0 : Nat.card Nor0 = 2 * Nat.card Gam0 := by
  have h := Subgroup.relIndex_mul_card Gam0 Nor0
  rw [inf_of_le_left Gam0_le_Nor0, relIndex_Gam0] at h
  exact h.symm

theorem eq_or_eq_of_le {Q : Subgroup (MulAut W6)} (h1 : Gam0 ≤ Q) (h2 : Q ≤ Nor0) :
    Q = Gam0 ∨ Q = Nor0 := by
  have h := Subgroup.relIndex_mul_relIndex Gam0 Q Nor0 h1 h2
  rw [relIndex_Gam0] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h) with h3 | h3
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h3) h1)
  · rw [h3] at h
    have h4 : Q.relIndex Nor0 = 1 := by omega
    exact Or.inr (le_antisymm h2 (Subgroup.relIndex_eq_one.mp h4))

theorem enc_w0_apply (x : MulAut W6) : enc (Multiplicative.toAdd (x w0)) = mact (mcode ⇑x) 17 :=
  enc_apply x 17 (by norm_num)

theorem apply_w0_eq_iff (x : MulAut W6) : x w0 = w0 ↔ mact (mcode ⇑x) 17 = 17 := by
  constructor
  · intro h
    rw [← enc_w0_apply, h, w0, toAdd_ofAdd, enc_dec 17 (by norm_num)]
  · intro h
    apply Multiplicative.toAdd.injective
    rw [← dec_enc (Multiplicative.toAdd (x w0)), enc_w0_apply, h]
    rfl

@[expose] def stab0 : Subgroup (MulAut W6) := MulAction.stabilizer (MulAut W6) w0

theorem P0_le_stab0 : P0 ≤ stab0 := fun x hx =>
  (apply_w0_eq_iff x).mpr (orb_checks.2.2.2.2.2.2.2.2 _ hx)

theorem le_card_orbit {H : Subgroup (MulAut W6)} (h1 : Gam0 ≤ H) :
    45 ≤ Nat.card (MulAction.orbit H w0) := by
  classical
  have hmem : ∀ p ∈ orbw, welt p.2 ∈ H := fun p hp => h1 (welt_mem_Gam0 _ (orb_checks.1 p hp).2)
  let f : {p // p ∈ orbw} → MulAction.orbit H w0 := fun p =>
    ⟨welt p.1.2 w0, ⟨⟨welt p.1.2, hmem p.1 p.2⟩, rfl⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    have h2 : welt p.2 w0 = welt q.2 w0 := congrArg Subtype.val hpq
    have h3 := congrArg (fun v => enc (Multiplicative.toAdd v)) h2
    simp only [enc_w0_apply, mcode_welt, (orb_checks.1 p hp).1, (orb_checks.1 q hq).1] at h3
    have hnd := orb_checks.2.2.1
    have h4 : p = q := by
      have hinj := List.inj_on_of_nodup_map hnd
      exact hinj hp hq h3
    exact Subtype.ext h4
  have h5 := Nat.card_le_card_of_injective f hf
  have h6 : Nat.card {p // p ∈ orbw} = 45 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p => (List.mem_toFinset (l := orbw)
      (a := p)).symm)), Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup (List.Nodup.of_map _ orb_checks.2.2.1), orb_checks.2.2.2.1]
  rwa [h6] at h5

@[expose] def PGl : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32], [1, 2, 21, 42, 16, 32], [1, 2, 39, 57, 16, 32], [1, 2, 54, 27, 16, 32],
    [4, 8, 1, 2, 21, 42], [4, 8, 16, 32, 21, 42], [4, 8, 39, 57, 21, 42], [4, 8, 54, 27, 21, 42],
    [16, 32, 4, 8, 1, 2], [16, 32, 21, 42, 1, 2], [16, 32, 39, 57, 1, 2], [16, 32, 54, 27, 1, 2],
    [21, 42, 1, 2, 4, 8], [21, 42, 16, 32, 4, 8], [21, 42, 39, 57, 4, 8], [21, 42, 54, 27, 4, 8],
    [39, 57, 1, 2, 54, 27], [39, 57, 4, 8, 54, 27], [39, 57, 16, 32, 54, 27],
    [39, 57, 21, 42, 54, 27], [54, 27, 1, 2, 39, 57], [54, 27, 4, 8, 39, 57],
    [54, 27, 16, 32, 39, 57], [54, 27, 21, 42, 39, 57]]

theorem chk_PG : idc ∈ PGl ∧ (∀ a ∈ PGl, ∀ b ∈ PGl, mmul a b ∈ PGl) ∧ PGl.Nodup ∧
    PGl.length = 24 ∧ (∀ c ∈ PGl, c ∈ Pl) := by
  decide +kernel

theorem chk_RG : idc ∈ RGl ∧ (∀ a ∈ RGl, ∀ b ∈ RGl, mmul a b ∈ RGl) ∧ RGl.Nodup ∧
    RGl.length = 4 ∧ (∀ c ∈ RGl, c ∈ Rl) := by
  decide +kernel

theorem chk_comm : (∀ c ∈ Pl, (mmul c omc = mmul omc c ↔ c ∈ PGl)) ∧
    (∀ c ∈ Rl, (mmul c omc = mmul omc c ↔ c ∈ RGl)) ∧
    (∀ c ∈ S0l, (mmul c omc = mmul omc c ↔ c ∈ D0l)) := by
  decide +kernel

theorem inf_stab0_eq (hG : Nat.card Gam0 = 1080) : Nor0 ⊓ stab0 = P0 := by
  refine (Subgroup.eq_of_le_of_card_ge (le_inf P0_le_Nor0 P0_le_stab0) ?_).symm
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer Nor0 w0)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_Nor0, hG] at h1
  have h2 := le_card_orbit (H := Nor0) Gam0_le_Nor0
  have h3 : Nat.card (MulAction.stabilizer Nor0 w0) ≤ 48 := by
    by_contra h4
    push Not at h4
    have := Nat.mul_le_mul h4 h2
    omega
  have h4 : Nat.card ↥(Nor0 ⊓ stab0) = Nat.card (MulAction.stabilizer Nor0 w0) := by
    refine Nat.card_congr ⟨fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩, fun x => ⟨x.1, x.1.2, x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [h4, card_P0]
  exact h3

theorem mem_Gam0_iff_code {x : MulAut W6} (hx : x ∈ Nor0) :
    x ∈ Gam0 ↔ mmul (mcode ⇑x) omc = mmul omc (mcode ⇑x) := by
  rw [mem_Gam0_iff hx]
  constructor
  · intro h
    have := congrArg (fun g : MulAut W6 => mcode ⇑g) h
    simpa only [mcode_mul, mcode_hom] using this
  · intro h
    apply mcode_injective
    rw [mcode_mul, mcode_mul, mcode_hom]
    exact h

@[expose] def PG0 : Subgroup (MulAut W6) := codeSub PGl chk_PG.1 chk_PG.2.1

@[expose] def RG0 : Subgroup (MulAut W6) := codeSub RGl chk_RG.1 chk_RG.2.1

theorem inf_P0_eq : Gam0 ⊓ P0 = PG0 := by
  ext x
  constructor
  · rintro ⟨hG, hP⟩
    exact (chk_comm.1 _ hP).mp ((mem_Gam0_iff_code (P0_le_Nor0 hP)).mp hG)
  · intro hx
    have hP : mcode ⇑x ∈ Pl := chk_PG.2.2.2.2 _ hx
    exact ⟨(mem_Gam0_iff_code (P0_le_Nor0 hP)).mpr ((chk_comm.1 _ hP).mpr hx), hP⟩

theorem inf_R0_eq : Gam0 ⊓ R0 = RG0 := by
  ext x
  constructor
  · rintro ⟨hG, hR⟩
    have hP : mcode ⇑x ∈ Pl := chk_incl.1 _ (chk_incl.2.2.1 _ hR)
    exact (chk_comm.2.1 _ hR).mp ((mem_Gam0_iff_code (P0_le_Nor0 hP)).mp hG)
  · intro hx
    have hR : mcode ⇑x ∈ Rl := chk_RG.2.2.2.2 _ hx
    have hP : mcode ⇑x ∈ Pl := chk_incl.1 _ (chk_incl.2.2.1 _ hR)
    exact ⟨(mem_Gam0_iff_code (P0_le_Nor0 hP)).mpr ((chk_comm.2.1 _ hR).mpr hx), hR⟩

theorem inf_S0_eq : Gam0 ⊓ S0 = D0 := by
  ext x
  constructor
  · rintro ⟨hG, hS⟩
    have hP : mcode ⇑x ∈ Pl := chk_incl.1 _ hS
    exact (chk_comm.2.2 _ hS).mp ((mem_Gam0_iff_code (P0_le_Nor0 hP)).mp hG)
  · intro hx
    have hS : mcode ⇑x ∈ S0l := chk_incl.2.1 _ hx
    have hP : mcode ⇑x ∈ Pl := chk_incl.1 _ hS
    exact ⟨(mem_Gam0_iff_code (P0_le_Nor0 hP)).mpr ((chk_comm.2.2 _ hS).mpr hx), hS⟩

theorem card_PG0 : Nat.card PG0 = 24 := by
  rw [PG0, card_codeSub chk_PG.2.2.1 fun c hc => word_of_Pl (chk_PG.2.2.2.2 c hc)]
  exact chk_PG.2.2.2.1

theorem card_RG0 : Nat.card RG0 = 4 := by
  rw [RG0, card_codeSub chk_RG.2.2.1 fun c hc =>
    word_of_Pl (chk_incl.1 c (chk_incl.2.2.1 c (chk_RG.2.2.2.2 c hc)))]
  exact chk_RG.2.2.2.1

theorem card_inf_P0 {Q : Subgroup (MulAut W6)}
    (hQ : Q = Gam0 ∨ Q = Nor0) : Nat.card ↥(Q ⊓ P0) = 6 * Nat.card ↥(Q ⊓ R0) := by
  rcases hQ with rfl | rfl
  · rw [inf_P0_eq, inf_R0_eq, card_PG0, card_RG0]
  · rw [inf_of_le_right P0_le_Nor0, inf_of_le_right (R0_le_S0.trans (S0_le_P0.trans P0_le_Nor0)),
      card_P0, card_R0]

theorem S0_le_Nor0 : S0 ≤ Nor0 := S0_le_P0.trans P0_le_Nor0

theorem isSylow_S0 (hG : Nat.card Gam0 = 1080) :
    IsPGroup 2 ↥(S0.subgroupOf Nor0) ∧ ¬ 2 ∣ (S0.subgroupOf Nor0).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(S0.subgroupOf Nor0) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Nor0).toEquiv, card_S0]
  refine ⟨IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num), ?_⟩
  have h1 := (S0.subgroupOf Nor0).card_mul_index
  rw [hcard, card_Nor0, hG] at h1
  omega

@[expose] def fixc (M : List (List ℕ)) : ℕ :=
  ((List.range 64).filter fun c => M.all fun m => mact m c == c).length

theorem card_subtype_mem {α : Type} [DecidableEq α] (l : List α) (h : l.Nodup) :
    Nat.card {c // c ∈ l} = l.length := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun c => (List.mem_toFinset (l := l)
    (a := c)).symm)), Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

theorem card_fixV_le {B : Subgroup (MulAut W6)} {M : List (List ℕ)}
    (hM : ∀ m ∈ M, ∃ x ∈ B, mcode ⇑x = m) : Nat.card (fixV B) ≤ fixc M := by
  classical
  let f : fixV B → {c // c ∈ (List.range 64).filter fun c =>
      M.all fun m => mact m c == c} := fun v => ⟨enc (Multiplicative.toAdd (v : W6)), by
    rw [List.mem_filter, List.mem_range, List.all_eq_true]
    refine ⟨enc_lt _, fun m hm => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hM m hm
    have h1 : x (v : W6) = v := (mem_fixV.mp v.2) x hx
    rw [beq_iff_eq, ← enc_apply x _ (enc_lt _), dec_enc]
    exact congrArg (fun y : W6 => enc (Multiplicative.toAdd y)) h1⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h1 : enc (Multiplicative.toAdd (v : W6)) = enc (Multiplicative.toAdd (w : W6)) :=
      congrArg Subtype.val hvw
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [← dec_enc (Multiplicative.toAdd (v : W6)), h1, dec_enc]
  have h2 := Nat.card_le_card_of_injective f hf
  rwa [card_subtype_mem _ (List.nodup_range.filter _)] at h2

theorem fix_D0 (v : W6) (hv : ∀ x ∈ D0, x v = v) :
    v = 1 ∨ v = w0 ∨ v = hom w0 ∨ v = hom (hom w0) := by
  set c := enc (Multiplicative.toAdd v) with hc
  have hc64 : c < 64 := enc_lt _
  have hfix : ∀ m ∈ D0l, mact m c = c := by
    intro m hm
    obtain ⟨w, hw⟩ := word_of_Pl (chk_incl.1 m (chk_incl.2.1 m hm))
    have hx : welt w ∈ D0 := show mcode ⇑(welt w) ∈ D0l by rw [mcode_welt, hw]; exact hm
    have h1 := hv _ hx
    rw [← hw, ← mcode_welt, hc, ← enc_apply _ _ (enc_lt _), dec_enc]
    show enc (Multiplicative.toAdd (welt w v)) = _
    rw [h1]
  have hv' : v = Multiplicative.ofAdd (dec c) := by rw [hc, dec_enc]; rfl
  have hw1 : hom w0 = Multiplicative.ofAdd (dec 34) := by
    apply Multiplicative.toAdd.injective
    rw [← dec_enc (Multiplicative.toAdd (hom w0)), enc_w0_apply, mcode_hom,
      orb_checks.2.2.2.2.2.2.1]
    rfl
  have hw2 : hom (hom w0) = Multiplicative.ofAdd (dec 51) := by
    rw [hw1]
    apply Multiplicative.toAdd.injective
    rw [← dec_enc (Multiplicative.toAdd (hom (Multiplicative.ofAdd (dec 34)))),
      enc_apply _ _ (by norm_num), mcode_hom, orb_checks.2.2.2.2.2.2.2.1]
    rfl
  rcases orb_checks.2.2.2.2.2.1 c hc64 hfix with h | h | h | h
  · left
    rw [hv', h, dec_zero]
    rfl
  · right; left
    rw [hv', h]
    rfl
  · right; right; left
    rw [hv', h, hw1]
  · right; right; right
    rw [hv', h, hw2]

theorem fix_w0_of_fix {x : MulAut W6} (hx : x ∈ Gam0) {k : ℕ}
    (hk : x ((hom ^ k) w0) = (hom ^ k) w0) :
    x w0 = w0 := by
  have hc : ∀ k : ℕ, x * hom ^ k = hom ^ k * x := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, comm_hom hx, ← mul_assoc]
  have h1 : (hom ^ k) (x w0) = (hom ^ k) w0 := by
    rw [← MulAut.mul_apply, ← hc k, MulAut.mul_apply, hk]
  exact (hom ^ k).injective h1

theorem chk_off1 : ∀ a ∈ S0l, a ≠ idc → mmul a a = idc → fixc [a] ≤ 16 := by
  decide +kernel

theorem chk_off2 : ∀ a ∈ S0l, ∀ b ∈ S0l, a ≠ idc → b ≠ idc → a ≠ b → mmul a a = idc →
    mmul b b = idc → mmul a b = mmul b a →
      fixc [a, b] ≤ 16 ∧ (16 ≤ fixc [a, b] → a ∈ A0l ∧ b ∈ A0l) := by
  decide +kernel

theorem chk_offA : (∀ a ∈ A0l, ∀ b ∈ A0l, a ≠ idc → b ≠ idc → a ≠ b →
      ∀ c ∈ A0l, c = idc ∨ c = a ∨ c = b ∨ c = mmul a b) ∧
    (∀ a ∈ A0l, a ≠ idc → fixc [a] = 16) ∧ (∃ a ∈ A0l, a ∉ Rl) ∧
    (∃ a ∈ S0l, ∃ b ∈ S0l, mmul a b ≠ mmul b a) := by
  decide +kernel

theorem chk_off3 : ∀ a ∈ S0l, ∀ b ∈ S0l, ∀ c ∈ S0l, a ≠ idc → b ≠ idc → a ≠ b →
    c ≠ idc → c ≠ a → c ≠ b → c ≠ mmul a b → mmul a a = idc → mmul b b = idc → mmul c c = idc →
    mmul a b = mmul b a → mmul a c = mmul c a → mmul b c = mmul c b → fixc [a, b, c] ≤ 4 := by
  decide +kernel

theorem code_ne_idc {x : MulAut W6} (hx : x ≠ 1) : mcode ⇑x ≠ idc := fun h =>
  hx (mcode_injective (by rw [h, mcode_one]))

theorem code_sq {x : MulAut W6} (hx : x ^ 2 = 1) : mmul (mcode ⇑x) (mcode ⇑x) = idc := by
  rw [← mcode_mul, ← pow_two, hx, mcode_one]

theorem code_commute {x y : MulAut W6} (h : x * y = y * x) :
    mmul (mcode ⇑x) (mcode ⇑y) = mmul (mcode ⇑y) (mcode ⇑x) := by
  rw [← mcode_mul, ← mcode_mul, h]

theorem offender_S0 {B : Subgroup (MulAut W6)} (hBS : B ≤ S0) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card B * Nat.card (fixV B) ≤ 64 ∧ (64 ≤ Nat.card B * Nat.card (fixV B) → B = A0) := by
  classical
  have hS : ∀ x ∈ B, mcode ⇑x ∈ S0l := fun x hx => hBS hx
  have hfix : ∀ M : List (List ℕ), (∀ m ∈ M, ∃ x ∈ B, mcode ⇑x = m) →
      Nat.card (fixV B) ≤ fixc M := fun M hM => card_fixV_le hM
  have hdvd : Nat.card B ∣ 16 := by
    rw [← card_S0]
    exact Subgroup.card_dvd_of_le hBS
  have hne16 : Nat.card B ≠ 16 := by
    intro h16
    have hBeq : B = S0 := Subgroup.eq_of_le_of_card_ge hBS (by rw [h16, card_S0])
    obtain ⟨a, ha, b, hb, hab⟩ := chk_offA.2.2.2
    obtain ⟨wa, hwa⟩ := word_of_Pl (chk_incl.1 a ha)
    obtain ⟨wb, hwb⟩ := word_of_Pl (chk_incl.1 b hb)
    have hxa : welt wa ∈ B := by
      rw [hBeq]
      show mcode ⇑(welt wa) ∈ S0l
      rw [mcode_welt, hwa]
      exact ha
    have hxb : welt wb ∈ B := by
      rw [hBeq]
      show mcode ⇑(welt wb) ∈ S0l
      rw [mcode_welt, hwb]
      exact hb
    have := code_commute (hBc _ hxa _ hxb)
    rw [mcode_welt, mcode_welt, hwa, hwb] at this
    exact hab this
  have hne1 : Nat.card B ≠ 1 := fun h1 => hB1 (Subgroup.eq_bot_of_card_eq B h1)
  have hex : ∀ (s : Finset (MulAut W6)), s.card < Nat.card B → ∃ x ∈ B, x ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have : Nat.card B ≤ s.card := by
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_le_card_of_injective (fun x : B => (⟨x, hcon x x.2⟩ : s)) ?_
      intro x y h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this
    omega
  have hcases : Nat.card B = 2 ∨ Nat.card B = 4 ∨ Nat.card B = 8 := by
    have : Nat.card B ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h16] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  obtain ⟨a, haB, ha1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  rw [Finset.mem_singleton] at ha1
  rcases hcases with h2 | h4 | h8
  · have hle := hfix [mcode ⇑a] (by
      simp only [List.mem_singleton]
      rintro m rfl
      exact ⟨a, haB, rfl⟩)
    have h1 := chk_off1 _ (hS a haB) (code_ne_idc ha1) (code_sq (hB2 a haB))
    rw [h2]
    constructor
    · omega
    · intro h; omega
  · obtain ⟨b, hbB, hb⟩ := hex {1, a} (by
      have := Finset.card_le_two (a := (1 : MulAut W6)) (b := a); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    have hab : mcode ⇑a ≠ mcode ⇑b := fun h => hb.2 (mcode_injective h).symm
    have hle := hfix [mcode ⇑a, mcode ⇑b] (by
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨a, haB, rfl⟩
      · exact ⟨b, hbB, rfl⟩)
    obtain ⟨h1, h2⟩ := chk_off2 _ (hS a haB) _ (hS b hbB) (code_ne_idc ha1) (code_ne_idc hb.1)
      hab (code_sq (hB2 a haB)) (code_sq (hB2 b hbB)) (code_commute (hBc _ haB _ hbB))
    rw [h4]
    refine ⟨by omega, fun h64 => ?_⟩
    obtain ⟨haA, hbA⟩ := h2 (by omega)
    have hAB : A0 ≤ B := by
      intro x hx
      rcases chk_offA.1 _ haA _ hbA (code_ne_idc ha1) (code_ne_idc hb.1) hab _ hx with
        h | h | h | h
      · have : x = 1 := mcode_injective (by rw [h, mcode_one])
        rw [this]
        exact B.one_mem
      · rw [mcode_injective h]
        exact haB
      · rw [mcode_injective h]
        exact hbB
      · rw [mcode_injective (h.trans (mcode_mul a b).symm)]
        exact B.mul_mem haB hbB
    have hcA : Nat.card A0 = 4 := by
      rw [A0, card_codeSub chk_A0.2.2.1 fun c hc =>
        word_of_Pl (chk_incl.1 c (chk_incl.2.2.2.1 c hc))]
      exact chk_A0.2.2.2
    exact (Subgroup.eq_of_le_of_card_ge hAB (by rw [h4, hcA])).symm
  · obtain ⟨b, hbB, hb⟩ := hex {1, a} (by
      have := Finset.card_le_two (a := (1 : MulAut W6)) (b := a); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    obtain ⟨c, hcB, hc⟩ := hex {1, a, b, a * b} (by
      have := Finset.card_le_four (a := (1 : MulAut W6)) (b := a) (c := b) (d := a * b); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    have hle := hfix [mcode ⇑a, mcode ⇑b, mcode ⇑c] (by
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨a, haB, rfl⟩
      · exact ⟨b, hbB, rfl⟩
      · exact ⟨c, hcB, rfl⟩)
    have h1 := chk_off3 _ (hS a haB) _ (hS b hbB) _ (hS c hcB) (code_ne_idc ha1)
      (code_ne_idc hb.1) (fun h => hb.2 (mcode_injective h).symm) (code_ne_idc hc.1)
      (fun h => hc.2.1 (mcode_injective h)) (fun h => hc.2.2.1 (mcode_injective h))
      (fun h => hc.2.2.2 (mcode_injective (h.trans (mcode_mul a b).symm)))
      (code_sq (hB2 a haB)) (code_sq (hB2 b hbB)) (code_sq (hB2 c hcB))
      (code_commute (hBc _ haB _ hbB)) (code_commute (hBc _ haB _ hcB))
      (code_commute (hBc _ hbB _ hcB))
    rw [h8]
    constructor
    · omega
    · intro h; omega

theorem offender_R0 {B : Subgroup (MulAut W6)} (hBR : B ≤ R0) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card B * Nat.card (fixV B) < 64 := by
  obtain ⟨h1, h2⟩ := offender_S0 (hBR.trans R0_le_S0) hB1 hBc hB2
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exfalso
    have hBA := h2 h.ge
    obtain ⟨a, haA, haR⟩ := chk_offA.2.2.1
    obtain ⟨w, hw⟩ := word_of_Pl (chk_incl.1 a (chk_incl.2.2.2.1 a haA))
    have hx : welt w ∈ A0 := show mcode ⇑(welt w) ∈ A0l by rw [mcode_welt, hw]; exact haA
    rw [← hBA] at hx
    have := hBR hx
    exact haR (by rw [← hw, ← mcode_welt]; exact this)

theorem chk_norm : (∀ a ∈ Pl, ∀ b ∈ Rl, ∀ a' ∈ Pl, mmul a' a = idc → mmul (mmul a b) a' ∈ Rl) ∧
    pa ∈ PGl ∧ pb ∈ PGl ∧ (∀ q ∈ Pl, mmul q (mmul pb pa) = idc → mmul q (mmul pa pb) ∉ Rl) := by
  decide +kernel

theorem R0_le_P0 : R0 ≤ P0 := R0_le_S0.trans S0_le_P0

theorem P0_le_normalizer : P0 ≤ Subgroup.normalizer (R0 : Set (MulAut W6)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ P0, ∀ y ∈ R0, x * y * x⁻¹ ∈ R0 := by
    intro x hx y hy
    have hxi : x⁻¹ ∈ P0 := P0.inv_mem hx
    show mcode ⇑(x * y * x⁻¹) ∈ Rl
    rw [mcode_mul, mcode_mul]
    refine chk_norm.1 _ hx _ hy _ hxi ?_
    rw [← mcode_mul, inv_mul_cancel, mcode_one]
  intro y
  refine ⟨key x hx y, fun h => ?_⟩
  have := key x⁻¹ (P0.inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem isPGroup_R0 : IsPGroup 2 ↥R0 := IsPGroup.of_card (n := 3) (by rw [card_R0]; norm_num)

theorem exists_pair : ∃ x ∈ Gam0, ∃ y ∈ Gam0, x ∈ P0 ∧ y ∈ P0 ∧ (y * x)⁻¹ * (x * y) ∉ R0 := by
  obtain ⟨-, ha, hb, hq⟩ := chk_norm
  have hwa := word_of_Pl (chk_PG.2.2.2.2 _ ha)
  obtain ⟨wa, hwa⟩ := hwa
  obtain ⟨wb, hwb⟩ := word_of_Pl (chk_PG.2.2.2.2 _ hb)
  have hxP : welt wa ∈ P0 := show mcode ⇑(welt wa) ∈ Pl by
    rw [mcode_welt, hwa]; exact chk_PG.2.2.2.2 _ ha
  have hyP : welt wb ∈ P0 := show mcode ⇑(welt wb) ∈ Pl by
    rw [mcode_welt, hwb]; exact chk_PG.2.2.2.2 _ hb
  have hxG : welt wa ∈ Gam0 := (inf_P0_eq ▸ (show welt wa ∈ PG0 by
    show mcode ⇑(welt wa) ∈ PGl
    rw [mcode_welt, hwa]; exact ha) : welt wa ∈ Gam0 ⊓ P0).1
  have hyG : welt wb ∈ Gam0 := (inf_P0_eq ▸ (show welt wb ∈ PG0 by
    show mcode ⇑(welt wb) ∈ PGl
    rw [mcode_welt, hwb]; exact hb) : welt wb ∈ Gam0 ⊓ P0).1
  refine ⟨welt wa, hxG, welt wb, hyG, hxP, hyP, fun h => ?_⟩
  have hi : (welt wb * welt wa)⁻¹ ∈ P0 := P0.inv_mem (P0.mul_mem hyP hxP)
  have h1 := hq _ hi (by
    rw [← hwa, ← hwb, ← mcode_welt, ← mcode_welt, ← mcode_mul, ← mcode_mul, inv_mul_cancel,
      mcode_one])
  apply h1
  have h2 : mcode ⇑((welt wb * welt wa)⁻¹ * (welt wa * welt wb)) ∈ Rl := h
  rwa [mcode_mul, mcode_mul, mcode_welt, mcode_welt, hwa, hwb] at h2

@[expose] def HatA6Embed : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 6 →
    ∀ K : Subgroup (MulAut V), CFSG.Quasithin.IsHat ↥K ↥(alternatingGroup (Fin 6)) →
      ∃ e : V ≃* W6, K.map (CFSG.Quasithin.H.congrHom e) = Gam0

@[expose] def HatA6Normalizer : Prop :=
  Subgroup.normalizer (Gam0 : Set (MulAut W6)) = Nor0

end CFSG.Quasithin.H13.HatM
