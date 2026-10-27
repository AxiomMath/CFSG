module

public import CFSG.Monster.B.Rep4371.XLabels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B

theorem uvec_labelIdx (l : ShortLabel) :
    uvec (labelIdx l) = labelVec l ∨ uvec (labelIdx l) = -labelVec l := by
  have hcl : classOf (labelVec l) = classOf (uvec (labelIdx l)) :=
    (phi0_labelElt l).symm.trans (classOf_uvec (labelIdx l)).symm
  exact (classOf_eq_iff (labelVec_mem l) (uvec_mem _)).1 hcl

theorem eight_alphaS_labelIdx (l l' : ShortLabel) :
    8 * alphaS (labelIdx l) (labelIdx l') = ∑ i, labelVec l i * labelVec l' i ∨
      8 * alphaS (labelIdx l) (labelIdx l') = -∑ i, labelVec l i * labelVec l' i := by
  rw [eight_mul_alphaS]
  rcases uvec_labelIdx l with h | h <;> rcases uvec_labelIdx l' with h' | h' <;> rw [h, h'] <;>
    simp [Finset.sum_neg_distrib]

@[expose] def rStarLab : ShortLabel := .inl ⟨(0, 1), by decide⟩

theorem shortCls_rStar : shortCls Short.isShortCoord_rStar = labelIdx rStarLab := Subtype.ext rfl

theorem sum_vMinus01 (v : Fin 24 → ℤ) : ∑ i, vMinus 0 1 i * v i = 4 * v 0 - 4 * v 1 := by
  simp [vMinus, eℤ, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]

theorem partnerCls_labelIdx_iff (l : ShortLabel) :
    PartnerCls Short.isShortCoord_rStar (labelIdx l) ↔ labelIdx l ≠ labelIdx rStarLab ∧
      (labelVec l 0 - labelVec l 1 = 4 ∨ labelVec l 0 - labelVec l 1 = -4) := by
  have h := eight_alphaS_labelIdx rStarLab l
  have hv : labelVec rStarLab = vMinus 0 1 := rfl
  rw [hv, sum_vMinus01] at h
  unfold PartnerCls
  rw [shortCls_rStar]
  refine and_congr Iff.rfl ⟨fun h2 => ?_, fun h2 => ?_⟩ <;> omega

theorem toC_surj (c : C) : ∃ a < 4096, toC a = c := by
  have hinj : Function.Injective (fun a : Fin 4096 => toC a) := fun a b h =>
    Fin.ext (toC_inj a.2 b.2 h)
  obtain ⟨a, ha⟩ := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hinj, by rw [Fintype.card_fin, card_C]⟩).2 c
  exact ⟨a, a.2, ha⟩

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem testBit_zero_of_mod_two {n : ℕ} (h : n.testBit 0 = false) : n % 2 = 0 := by
  rw [Nat.testBit_zero] at h
  simp only [decide_eq_false_iff_not] at h
  omega

theorem mod_four_of_testBit {n : ℕ} (h0 : n.testBit 0 = true) (h1 : n.testBit 1 = true) :
    n % 4 = 3 := by
  rw [Nat.testBit_zero] at h0
  rw [Nat.testBit_succ, Nat.testBit_zero] at h1
  simp only [decide_eq_true_eq] at h0 h1
  omega

theorem getElem!_eq_toList {A : Array ℕ} {t : ℕ} (ht : t < A.toList.length) :
    A[t]! = A.toList[t] := by
  rw [getElem!_pos A t (by simpa using ht), Array.getElem_toList]

theorem exists_oddC (c : C₀) (h : ((c : C) : Fin 24 → ZMod 2) 0 = ((c : C) : Fin 24 → ZMod 2) 1) :
    ∃ t < 1024, oddC t = c := by
  obtain ⟨a, ha, hac⟩ := toC_surj (c : C)
  have hmem : a ∈ Model.oddCodes.toList := by
    rw [mem_oddCodes_iff]
    refine ⟨ha, ?_, ?_⟩
    · have h0 : μ₀ (toC a) = 0 := by rw [hac]; exact μ₀_coe c
      rw [μ₀_toC, boolZ_eq_zero_iff, Model.mu0N] at h0
      exact testBit_zero_of_mod_two h0
    · have h' := h
      rw [← hac, coe_toC_apply, coe_toC_apply] at h'
      exact boolZ_injective h'
  obtain ⟨t, ht, hta⟩ := List.mem_iff_getElem.1 hmem
  have ht' : t < Model.oddCodes.size := by simpa using ht
  have hsz := oddCodes_size
  refine ⟨t, by omega, Subtype.ext ?_⟩
  rw [coe_oddC, (getElem!_eq_toList ht).trans hta, hac]

theorem exists_octadW (hoct : Model.octDataOK = true) (d : OctadWord)
    (h0 : ((d : C) : Fin 24 → ZMod 2) 0 ≠ 0) (h1 : ((d : C) : Fin 24 → ZMod 2) 1 ≠ 0) :
    ∃ b, ∃ hb : b < 77, octadW hoct hb = d := by
  obtain ⟨a, ha, hac⟩ := toC_surj (d : C)
  have hw : Model.popcN 24 (Model.wordN a) = 8 := by
    have := d.2
    rw [← hac, coe_toC, hammingNorm_bvec, ← popcN_eq_popc] at this
    exact this
  have hb0 : (Model.wordN a).testBit 0 = true := by
    rw [← hac, coe_toC_apply] at h0
    cases hx : (Model.wordN a).testBit ((0 : Fin 24) : ℕ) <;> simp_all [boolZ]
  have hb1 : (Model.wordN a).testBit 1 = true := by
    rw [← hac, coe_toC_apply] at h1
    cases hx : (Model.wordN a).testBit ((1 : Fin 24) : ℕ) <;> simp_all [boolZ]
  have hmem : a ∈ Model.octCoeffs.toList :=
    (mem_octCoeffs_iff a).2 ⟨ha, hw, mod_four_of_testBit hb0 hb1⟩
  obtain ⟨b, hb, hba⟩ := List.mem_iff_getElem.1 hmem
  have hb' : b < Model.octCoeffs.size := by simpa using hb
  have hsz := octCoeffs_size hoct
  have hb77 : b < 77 := by omega
  refine ⟨b, hb77, Subtype.ext ?_⟩
  show toC Model.octCoeffs[b]! = (d : C)
  rw [(getElem!_eq_toList hb).trans hba, hac]

theorem spreadN_one (d : ℕ) : Model.spreadN d 1 = 1 := by
  simp only [Model.spreadN, Model.combN, show (1 : ℕ).testBit 1 = false from rfl,
    show (1 : ℕ).testBit 2 = false from rfl, show (1 : ℕ).testBit 3 = false from rfl,
    show (1 : ℕ).testBit 4 = false from rfl, show (1 : ℕ).testBit 5 = false from rfl,
    show (1 : ℕ).testBit 6 = false from rfl, show (1 : ℕ).testBit 7 = false from rfl,
    show (1 : ℕ).testBit 0 = true from rfl, Model.localOrder]
  simp

theorem spreadN_two (d : ℕ) : Model.spreadN d 2 = 2 := by
  simp only [Model.spreadN, Model.combN, show (2 : ℕ).testBit 0 = false from rfl,
    show (2 : ℕ).testBit 2 = false from rfl, show (2 : ℕ).testBit 3 = false from rfl,
    show (2 : ℕ).testBit 4 = false from rfl, show (2 : ℕ).testBit 5 = false from rfl,
    show (2 : ℕ).testBit 6 = false from rfl, show (2 : ℕ).testBit 7 = false from rfl,
    show (2 : ℕ).testBit 1 = true from rfl, Model.localOrder]
  simp

theorem spreadN_zero (d : ℕ) : Model.spreadN d 0 = 0 := by
  simp [Model.spreadN, Model.combN]

theorem octSet_one (b : ℕ) : octSet b 1 = {0} := by
  ext i
  simp only [octSet, Finset.mem_filter, Finset.mem_univ, true_and, spreadN_one,
    Finset.mem_singleton]
  rw [Nat.testBit_one_eq_true_iff_self_eq_zero, Fin.ext_iff, Fin.val_zero]

theorem octSet_two (b : ℕ) : octSet b 2 = {1} := by
  ext i
  simp only [octSet, Finset.mem_filter, Finset.mem_univ, true_and, spreadN_two,
    Finset.mem_singleton]
  rw [show (2 : ℕ) = 2 ^ 1 from rfl, Nat.testBit_two_pow, Fin.ext_iff, Fin.val_one,
    decide_eq_true_iff]
  constructor <;> intro h <;> omega

theorem octSet_zero (b : ℕ) : octSet b 0 = ∅ := by
  ext i
  simp [octSet, spreadN_zero]

theorem mem_octSet_bit (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) {m : ℕ}
    (hm : m < 256) (t : Fin 2) :
    (⟨t, by omega⟩ : Fin 24) ∈ octSet b m ↔ m.testBit t = true := by
  have hand := octSet_and hoct hb hm (by fin_cases t <;> decide : 2 ^ (t : ℕ) < 256)
  have hset : octSet b (2 ^ (t : ℕ)) = {⟨t, by omega⟩} := by
    fin_cases t
    · exact octSet_one b
    · exact octSet_two b
  rw [hset] at hand
  constructor
  · intro h
    by_contra hc
    have h0 : m &&& 2 ^ (t : ℕ) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : (t : ℕ) = j
      · subst hj; simp_all
      · simp [hj]
    rw [h0, octSet_zero] at hand
    have : (⟨t, by omega⟩ : Fin 24) ∈ octSet b m ∩ {⟨t, by omega⟩} :=
      Finset.mem_inter.2 ⟨h, Finset.mem_singleton_self _⟩
    rw [← hand] at this
    exact absurd this (Finset.notMem_empty _)
  · intro h
    have h0 : m &&& 2 ^ (t : ℕ) = 2 ^ (t : ℕ) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hj : (t : ℕ) = j
      · subst hj; simp_all
      · simp [hj]
    rw [h0, hset] at hand
    have : (⟨t, by omega⟩ : Fin 24) ∈ octSet b m ∩ {⟨t, by omega⟩} := by
      rw [← hand]; exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.1 this).1

theorem localPairs_cover : ∀ m < 256, Model.popcN 8 m % 2 = 0 → m.testBit 0 ≠ m.testBit 1 →
    ∃ i < 16, ∃ e : Bool,
      m = (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) ∨
      m = (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) ^^^ 255 := by
  decide +kernel

theorem xLab_minus' (hoct : Model.octDataOK = true) {j : Fin 24} (hj : 2 ≤ (j : ℕ)) (e : Bool) :
    xLab hoct (23 + 2 * ((j : ℕ) - 2)) e = .inl (pairLab e j) := by
  rw [xLab_minus hoct (by omega) (by omega)]
  congr 2
  omega

theorem xLab_plus' (hoct : Model.octDataOK = true) {j : Fin 24} (hj : 2 ≤ (j : ℕ)) (e : Bool) :
    xLab hoct (24 + 2 * ((j : ℕ) - 2)) e = .inr (.inl (pairLab e j)) := by
  rw [xLab_plus hoct (by omega) (by omega)]
  congr 3
  omega

theorem xLab_odd' (hoct : Model.octDataOK = true) {t : ℕ} (ht : t < 1024) (e : Bool) :
    xLab hoct (67 + t) e = .inr (.inr (.inl (oddC t, if e then 1 else 0))) := by
  rw [xLab_odd hoct (by omega) (by omega), Nat.add_sub_cancel_left]

theorem octLab_congr (hoct : Model.octDataOK = true) {b b' : ℕ} (h : b = b') (hb : b < 77)
    (hb' : b' < 77) (m : ℕ) :
    (⟨octadW hoct hb, Octad.cls _ (octSet b m)⟩ : OctIdx) =
      ⟨octadW hoct hb', Octad.cls _ (octSet b' m)⟩ := by
  subst h
  rfl

theorem xLab_oct' (hoct : Model.octDataOK = true) {b i : ℕ} (hb : b < 77) (hi : i < 16)
    (e : Bool) :
    xLab hoct (1091 + 16 * b + i) e = .inr (.inr (.inr ⟨octadW hoct hb, Octad.cls _ (octSet b
      (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1))⟩)) := by
  have hX : (1091 + 16 * b + i - 1091) / 16 = b := by omega
  have hY : (1091 + 16 * b + i - 1091) % 16 = i := by omega
  rw [xLab, ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega), hY]
  exact congrArg (fun o => (Sum.inr (Sum.inr (Sum.inr o)) : ShortLabel))
    (octLab_congr hoct hX _ hb _)

theorem pairLab_eq {e : Bool} {i j : Fin 24} (hj : 2 ≤ (j : ℕ)) (hi : i = if e then 1 else 0)
    (hij : i < j) : pairLab e j = ⟨(i, j), hij⟩ := by
  subst hi
  apply Subtype.ext
  rw [pairLab_val ⟨hj, by omega⟩]
  exact Prod.ext rfl (Fin.ext (val_fin24 j.2))

theorem fin_two_le {j : Fin 24} (h0 : j ≠ 0) (h1 : j ≠ 1) : 2 ≤ (j : ℕ) := by
  have h0' : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : (j : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
  omega

theorem partner_minus (hoct : Model.octDataOK = true) (p : LtPair)
    (hp : PartnerCls Short.isShortCoord_rStar (labelIdx (.inl p))) :
    ∃ k, 23 ≤ k ∧ k ≤ 2322 ∧ ∃ e, (.inl p : ShortLabel) = xLab hoct k e := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hv := ((partnerCls_labelIdx_iff _).1 hp).2
  have hlv : ∀ k : Fin 24, labelVec (.inl ⟨(i, j), hij⟩) k =
      4 * (if k = i then 1 else 0) - 4 * (if k = j then 1 else 0) := fun k => by
    simp [labelVec, vMinus, eℤ, Pi.single_apply]
  rw [hlv, hlv] at hv
  have hij' : (i : ℕ) < j := hij
  have hj0 : j ≠ 0 := fun h => by rw [h] at hij'; simp at hij'
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj1 : j = 1
    · subst hj1
      simp at hv
    · have hj2 := fin_two_le hj0 hj1
      exact ⟨23 + 2 * ((j : ℕ) - 2), by omega, by omega, false,
        by rw [xLab_minus' hoct hj2, pairLab_eq (e := false) hj2 rfl hij]; rfl⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have hj1 : j ≠ 1 := fun h => by rw [h] at hij'; simp at hij'
      have hj2 := fin_two_le hj0 hj1
      exact ⟨23 + 2 * ((j : ℕ) - 2), by omega, by omega, true,
        by rw [xLab_minus' hoct hj2, pairLab_eq (e := true) hj2 rfl hij]; rfl⟩
    · exfalso
      have hj1 : j ≠ 1 := fun h => by
        rw [h] at hij'
        have := fin_two_le hi0 hi1
        simp at hij'
        omega
      rw [ite_eq_right (Ne.symm hi0), ite_eq_right (Ne.symm hj0), ite_eq_right (Ne.symm hi1),
        ite_eq_right (Ne.symm hj1)] at hv
      omega

theorem partner_plus (hoct : Model.octDataOK = true) (p : LtPair)
    (hp : PartnerCls Short.isShortCoord_rStar (labelIdx (.inr (.inl p)))) :
    ∃ k, 23 ≤ k ∧ k ≤ 2322 ∧ ∃ e, (.inr (.inl p) : ShortLabel) = xLab hoct k e := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hv := ((partnerCls_labelIdx_iff _).1 hp).2
  have hlv : ∀ k : Fin 24, labelVec (.inr (.inl ⟨(i, j), hij⟩)) k =
      4 * (if k = i then 1 else 0) + 4 * (if k = j then 1 else 0) := fun k => by
    simp [labelVec, vPlus, eℤ, Pi.single_apply]
  rw [hlv, hlv] at hv
  have hij' : (i : ℕ) < j := hij
  have hj0 : j ≠ 0 := fun h => by rw [h] at hij'; simp at hij'
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj1 : j = 1
    · subst hj1
      simp at hv
    · have hj2 := fin_two_le hj0 hj1
      exact ⟨24 + 2 * ((j : ℕ) - 2), by omega, by omega, false,
        by rw [xLab_plus' hoct hj2, pairLab_eq (e := false) hj2 rfl hij]; rfl⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have hj1 : j ≠ 1 := fun h => by rw [h] at hij'; simp at hij'
      have hj2 := fin_two_le hj0 hj1
      exact ⟨24 + 2 * ((j : ℕ) - 2), by omega, by omega, true,
        by rw [xLab_plus' hoct hj2, pairLab_eq (e := true) hj2 rfl hij]; rfl⟩
    · exfalso
      have hj1 : j ≠ 1 := fun h => by
        rw [h] at hij'
        have := fin_two_le hi0 hi1
        simp at hij'
        omega
      rw [ite_eq_right (Ne.symm hi0), ite_eq_right (Ne.symm hj0), ite_eq_right (Ne.symm hi1),
        ite_eq_right (Ne.symm hj1)] at hv
      omega

theorem odd_partner_aux (x y : ZMod 2) (p q : Prop) [Decidable p] [Decidable q]
    (hpq : ¬ (p ∧ q))
    (h : (-1 : ℤ) ^ x.val * (1 - 4 * if p then 1 else 0) -
        (-1) ^ y.val * (1 - 4 * if q then 1 else 0) = 4 ∨
      (-1 : ℤ) ^ x.val * (1 - 4 * if p then 1 else 0) -
        (-1) ^ y.val * (1 - 4 * if q then 1 else 0) = -4) :
    (p ∨ q) ∧ x = y := by
  by_cases hp : p <;> by_cases hq : q
  · exact absurd ⟨hp, hq⟩ hpq
  · simp only [hp, hq, ↓reduceIte, true_or, true_and] at h ⊢
    revert h
    revert x y
    decide
  · simp only [hp, hq, ↓reduceIte, or_true, true_and] at h ⊢
    revert h
    revert x y
    decide
  · simp only [hp, hq, ↓reduceIte] at h
    exfalso
    revert h
    revert x y
    decide

theorem partner_odd (hoct : Model.octDataOK = true) (c : C₀) (i : Fin 24)
    (hp : PartnerCls Short.isShortCoord_rStar (labelIdx (.inr (.inr (.inl (c, i)))))) :
    ∃ k, 23 ≤ k ∧ k ≤ 2322 ∧ ∃ e, (.inr (.inr (.inl (c, i))) : ShortLabel) = xLab hoct k e := by
  have hv := ((partnerCls_labelIdx_iff _).1 hp).2
  have hlv : ∀ k : Fin 24, labelVec (.inr (.inr (.inl (c, i)))) k =
      (-1) ^ (((c : C) : Fin 24 → ZMod 2) k).val * (1 - 4 * if k = i then 1 else 0) :=
    fun k => rfl
  rw [hlv, hlv] at hv
  obtain ⟨hi, hc⟩ := odd_partner_aux _ _ _ _
    (fun h => absurd (h.1.trans h.2.symm) (by decide)) hv
  obtain ⟨t, ht, rfl⟩ := exists_oddC c hc
  rcases hi with hi | hi
  · subst hi
    exact ⟨67 + t, by omega, by omega, false, by rw [xLab_odd' hoct ht]; rfl⟩
  · subst hi
    exact ⟨67 + t, by omega, by omega, true, by rw [xLab_odd' hoct ht]; rfl⟩

theorem oct_partner_aux (x y : ZMod 2) (p q : Prop) [Decidable p] [Decidable q]
    (hpx : p → x ≠ 0) (hqy : q → y ≠ 0)
    (h : (2 * (x.val : ℤ) - 4 * if p then 1 else 0) - (2 * (y.val : ℤ) - 4 * if q then 1 else 0) =
        4 ∨
      (2 * (x.val : ℤ) - 4 * if p then 1 else 0) - (2 * (y.val : ℤ) - 4 * if q then 1 else 0) =
        -4) :
    x ≠ 0 ∧ y ≠ 0 ∧ (p ↔ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q
  · exfalso
    have hx := hpx hp
    have hy := hqy hq
    simp only [hp, hq, ↓reduceIte] at h
    clear hpx hqy
    revert h hx hy
    revert x y
    decide
  · have hx := hpx hp
    simp only [hp, hq, ↓reduceIte, not_false_eq_true] at h ⊢
    clear hpx hqy
    revert h hx
    revert x y
    decide
  · have hy := hqy hq
    simp only [hp, hq, ↓reduceIte, not_true_eq_false] at h ⊢
    clear hpx hqy
    revert h hy
    revert x y
    decide
  · exfalso
    simp only [hp, hq, ↓reduceIte] at h
    clear hpx hqy
    revert h
    revert x y
    decide

theorem partner_oct (hoct : Model.octDataOK = true) (o : OctIdx)
    (hp : PartnerCls Short.isShortCoord_rStar (labelIdx (.inr (.inr (.inr o))))) :
    ∃ k, 23 ≤ k ∧ k ≤ 2322 ∧ ∃ e, (.inr (.inr (.inr o)) : ShortLabel) = xLab hoct k e := by
  obtain ⟨d, v⟩ := o
  have hv := ((partnerCls_labelIdx_iff _).1 hp).2
  obtain ⟨hsub, heven, hcls⟩ := octRep_spec d v
  have hlv : ∀ k : Fin 24, labelVec (.inr (.inr (.inr ⟨d, v⟩))) k =
      2 * ((((d : C) : Fin 24 → ZMod 2) k).val : ℤ) - 4 * if k ∈ octRep d v then 1 else 0 := by
    intro k
    simp only [labelVec, vOct, liftℤ, bitLift, Octad.ind, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    split_ifs
    · simp
      decide
    · simp
  rw [hlv, hlv] at hv
  have hmem : ∀ k, k ∈ octRep d v → ((d : C) : Fin 24 → ZMod 2) k ≠ 0 := fun k hk =>
    mem_supp_iff.1 (hsub hk)
  obtain ⟨hd0, hd1, hone⟩ := oct_partner_aux _ _ _ _ (hmem 0) (hmem 1) hv
  obtain ⟨b, hb, rfl⟩ := exists_octadW hoct d hd0 hd1
  obtain ⟨m, hm, hmδ⟩ := exists_octSet_eq hoct hb hsub
  have hme : Model.popcN 8 m % 2 = 0 := by
    have := card_octSet' hoct hb hm
    rw [hmδ] at this
    rw [← this]
    exact Nat.even_iff.1 heven
  have h0 : (0 : Fin 24) ∈ octSet b m ↔ m.testBit 0 = true := mem_octSet_bit hoct hb hm 0
  have h1 : (1 : Fin 24) ∈ octSet b m ↔ m.testBit 1 = true := mem_octSet_bit hoct hb hm 1
  rw [hmδ] at h0 h1
  have hbits : m.testBit 0 ≠ m.testBit 1 := by
    intro h
    cases h2 : m.testBit 0 <;> simp_all
  obtain ⟨i, hi, e, hme'⟩ := localPairs_cover m hm hme hbits
  obtain ⟨hx, hxe⟩ := localPair_even hi e
  have hv' : v = Octad.cls _ (octSet b
      (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1)) := by
    rw [← hcls, ← hmδ]
    exact (cls_octSet_eq_iff hoct hb hm hme hx hxe).2 hme'
  subst hv'
  exact ⟨1091 + 16 * b + i, by omega, by omega, e, by rw [xLab_oct' hoct hb hi]⟩

theorem partnerCls_eq_xLab (hoct : Model.octDataOK = true) {d : ShortIdx}
    (hd : PartnerCls Short.isShortCoord_rStar d) :
    ∃ k, 23 ≤ k ∧ k ≤ 2322 ∧ ∃ e, d = labelIdx (xLab hoct k e) := by
  obtain ⟨l, rfl⟩ := labelIdx_surjective d
  rcases l with p | p | ⟨c, i⟩ | o
  · obtain ⟨k, h1, h2, e, he⟩ := partner_minus hoct p hd
    exact ⟨k, h1, h2, e, congrArg labelIdx he⟩
  · obtain ⟨k, h1, h2, e, he⟩ := partner_plus hoct p hd
    exact ⟨k, h1, h2, e, congrArg labelIdx he⟩
  · obtain ⟨k, h1, h2, e, he⟩ := partner_odd hoct c i hd
    exact ⟨k, h1, h2, e, congrArg labelIdx he⟩
  · obtain ⟨k, h1, h2, e, he⟩ := partner_oct hoct o hd
    exact ⟨k, h1, h2, e, congrArg labelIdx he⟩

@[expose] noncomputable def xRep (hoct : Model.octDataOK = true) (t : Fin 2300) : Q :=
  labelElt (xLab hoct (23 + t) false)

theorem add_self_coord (x : C × Cocode) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem isPartner_xRep (hoct : Model.octDataOK = true) (t : Fin 2300) :
    IsPartner Short.isShortCoord_rStar (xRep hoct t) := by
  have hs := isShortCoord_labelElt (xLab hoct (23 + t) false)
  have hmul := rStar_mul_xLab hoct (k := 23 + t) (by omega) (by omega)
  have hsum : IsShortCoord ((shortCls Short.isShortCoord_rStar).1 +
      (⟨coordOf (xRep hoct t), hs⟩ : ShortIdx).1) := by
    show IsShortCoord (coordOf Short.rStar + coordOf (labelElt (xLab hoct (23 + t) false)))
    rw [← coordOf_mul, hmul]
    exact isShortCoord_labelElt _
  have hne : shortCls Short.isShortCoord_rStar ≠ ⟨coordOf (xRep hoct t), hs⟩ := by
    intro h
    have h' : coordOf Short.rStar = coordOf (xRep hoct t) := congrArg Subtype.val h
    apply not_isShortCoord_zero
    have h0 : (shortCls Short.isShortCoord_rStar).1 +
        (⟨coordOf (xRep hoct t), hs⟩ : ShortIdx).1 = 0 := by
      show coordOf Short.rStar + coordOf (xRep hoct t) = 0
      rw [h', add_self_coord]
    rw [← h0]
    exact hsum
  exact ⟨hs, fun h => hne (Subtype.ext h.symm), (isShortCoord_add_iff hne).1 hsum⟩

theorem coordOf_labelElt (l : ShortLabel) : coordOf (labelElt l) = (labelIdx l).1 := rfl

theorem huniq_xRep (hoct : Model.octDataOK = true) (d : ShortIdx)
    (hd : PartnerCls Short.isShortCoord_rStar d) :
    ∃! t : Fin 2300, coordOf (xRep hoct t) = d.1 ∨ coordOf (Short.rStar * xRep hoct t) = d.1 := by
  obtain ⟨k, h1, h2, e, rfl⟩ := partnerCls_eq_xLab hoct hd
  have hk : 23 + (k - 23) = k := by omega
  refine ⟨⟨k - 23, by omega⟩, ?_, ?_⟩
  · show coordOf (labelElt (xLab hoct (23 + (k - 23)) false)) = _ ∨
      coordOf (Short.rStar * labelElt (xLab hoct (23 + (k - 23)) false)) = _
    rw [hk]
    cases e
    · exact Or.inl rfl
    · exact Or.inr (by rw [rStar_mul_xLab hoct h1 h2]; rfl)
  · intro t ht
    have key : ∃ e', labelIdx (xLab hoct (23 + t) e') = labelIdx (xLab hoct k e) := by
      rcases ht with h | h
      · exact ⟨false, Subtype.ext h⟩
      · refine ⟨true, Subtype.ext ?_⟩
        rw [← h, xRep, rStar_mul_xLab hoct (by omega) (by omega)]
        rfl
    obtain ⟨e', he'⟩ := key
    have := (xLab_injective hoct (by omega) (by omega) h1 h2 (labelIdx_injective he')).1
    exact Fin.ext (by simp only; omega)

theorem xdiffVec_xRep (hoct : Model.octDataOK = true) (t : Fin 2300) :
    xdiffVec Short.rStar (xRep hoct t) = Rraw (23 + t) := by
  rw [xdiffVec, xRep, rStar_mul_xLab hoct (by omega) (by omega),
    Rraw_xLab hoct (by omega) (by omega)]

theorem xdiff_Rraw (hoct : Model.octDataOK = true) :
    LinearIndependent ℚ (fun t : Fin 2300 => Rraw (23 + t)) ∧
      Submodule.span ℚ (Set.range fun t : Fin 2300 => Rraw (23 + t)) =
        Xdiff Short.isShortCoord_rStar ∧
      Pairwise fun t t' : Fin 2300 => bform (Rraw (23 + t)) (Rraw (23 + t')) = 0 := by
  have h := xdiff_representatives Short.isShortCoord_rStar (xRep hoct) (isPartner_xRep hoct)
    (huniq_xRep hoct)
  simp only [xdiffVec_xRep] at h
  exact h

end CFSG.Monster.B.Rep4371
