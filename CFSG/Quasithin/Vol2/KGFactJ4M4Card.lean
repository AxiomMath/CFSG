module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4KW3
public import Certificates.Certificate7256

public section

namespace CFSG.Quasithin.J4M4Card

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4 CFSG.Quasithin.KGC31.J4M4
open CFSG.Monster.B.Co2.Native (eqA)
open CFSG.Certificates.Native (rawChainOK rawOrbitSizes)
open scoped Matrix

theorem chk_parts : (chkT () = true) ∧ (chkMasks () = true) ∧
    (chkWit () = true) ∧ (chkDistinct () = true) ∧ (chkPsi () = true) ∧ (chkKE () = true) :=
  Certificates.certificate7256

theorem kwSig_lt : ∀ l < 4, ∀ k < 31, (kwSig.getD l []).getD k 0 < 31 := by decide

theorem kwSig_inv : ∀ s < 2, ∀ k < 31,
    (kwSig.getD s []).getD ((kwSig.getD (s + 2) []).getD k 0) 0 = k := by decide

theorem idxAct_lt {l : ℤ} {k : ℕ} (hk : k < 31) : idxAct l k < 31 := by
  unfold idxAct
  split_ifs with h
  · by_cases hl : l.toNat - 1 < 4
    · exact kwSig_lt _ hl k hk
    · have : kwSig.getD (l.toNat - 1) [] = [] := by
        rw [List.getD_eq_default]
        simp only [kwSig, List.length_cons, List.length_nil]
        omega
      rw [this]
      simp
  · by_cases hl : (-l).toNat + 1 < 4
    · exact kwSig_lt _ hl k hk
    · have : kwSig.getD ((-l).toNat + 1) [] = [] := by
        rw [List.getD_eq_default]
        simp only [kwSig, List.length_cons, List.length_nil]
        omega
      rw [this]
      simp

theorem wordAct_lt (w : List ℤ) {k : ℕ} (hk : k < 31) : wordAct w k < 31 := by
  induction w with
  | nil => exact hk
  | cons l w ih => exact idxAct_lt ih

@[expose] def GoodWord (w : List ℤ) : Prop := ∀ l ∈ w, l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2

theorem GoodWord.ne_zero {w : List ℤ} (h : GoodWord w) : ∀ l ∈ w, l ≠ 0 := fun l hl => by
  rcases h l hl with rfl | rfl | rfl | rfl <;> norm_num

theorem tWords_good : ∀ x < 31, GoodWord (tWords.getD x []) := by
  unfold GoodWord; decide +kernel

theorem keWords_good : ∀ j < 10, GoodWord (keWords.getD j []) := by
  unfold GoodWord; decide +kernel

theorem schWord_good {i : ℕ} (hi : i < 62) : GoodWord (schWord i) := by
  have ht := tWords_good
  intro l hl
  simp only [schWord, List.mem_append, List.mem_singleton] at hl
  rcases hl with (hl | hl) | hl
  · obtain ⟨l', hl', rfl⟩ : ∃ l' ∈ tWords.getD ((kwSig.getD (i % 2) []).getD (i / 2) 0) [],
        l = -l' := by
      simp only [invW, List.mem_map, List.mem_reverse] at hl
      obtain ⟨l', hl', rfl⟩ := hl
      exact ⟨l', hl', rfl⟩
    have := ht _ (kwSig_lt (i % 2) (by omega) (i / 2) (by omega)) l' hl'
    rcases this with rfl | rfl | rfl | rfl <;> simp
  · have : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases this with h | h <;> simp [hl, h]
  · exact ht _ (by omega) l hl


theorem inv_smul_kwRow_of {x : G₀} {P : Array V2}
    (hx : ((x : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = rowsMatrix P)
    (k : ℕ) : x⁻¹ • kwRow k = toRow (frApply (frTable P) (kwVecs.getD k V2.zero)).toVec := by
  apply ofRow_inj.mp
  rw [inv_smul_row, hx]
  show (kwVecs.getD k V2.zero).toVec ᵥ* rowsMatrix P = _
  rw [frApply_toVec_eq_vecMul]
  rfl

theorem letter_smul_kwRow {l : ℤ}
    (hl : l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2) {k : ℕ} (hk : k < 31) :
    wordProd m4gen [l] • kwRow k = kwRow (idxAct l k) := by
  have hM := j4Facts.mat
  have hc := chkKW_true
  obtain ⟨-, h2⟩ := chkKW_parts hc
  rcases hl with rfl | rfl | rfl | rfl
  · simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ite_eq_left (by norm_num)]
    exact m4gen_smul_kwRow hc hM (by norm_num) hk
  · simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ite_eq_left (by norm_num)]
    exact m4gen_smul_kwRow hc hM (by norm_num) hk
  · simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ite_eq_right (by norm_num)]
    show (m4gen 0)⁻¹ • kwRow k = _
    rw [inv_smul_kwRow_of (m4Mats_spec hM 0).symm, kwRow, idxAct, ite_eq_right (by norm_num)]
    have e := h2 2 (by norm_num) k hk
    rw [show (letRows ())[2]?.getD idRows = (m4Mats ())[0]?.getD idRows by
      simp only [letRows, List.getElem?_toArray, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some]] at e
    rw [e]
    rfl
  · simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ite_eq_right (by norm_num)]
    show (m4gen 1)⁻¹ • kwRow k = _
    rw [inv_smul_kwRow_of (m4Mats_spec hM 1).symm, kwRow, idxAct, ite_eq_right (by norm_num)]
    have e := h2 3 (by norm_num) k hk
    rw [show (letRows ())[3]?.getD idRows = (m4Mats ())[1]?.getD idRows by
      simp only [letRows, List.getElem?_toArray, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some]] at e
    rw [e]
    rfl

theorem wordProd_smul_kwRow
    {w : List ℤ} (hw : GoodWord w) {k : ℕ} (hk : k < 31) :
    wordProd m4gen w • kwRow k = kwRow (wordAct w k) := by
  induction w with
  | nil => simp [wordProd, wordAct]
  | cons l w ih =>
    have hw' : GoodWord w := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have h1 : wordProd m4gen (l :: w) = wordProd m4gen [l] * wordProd m4gen w := by
      simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [h1, mul_smul, ih hw', letter_smul_kwRow (hw l (List.mem_cons_self ..)) (wordAct_lt w hk)]
    rfl

theorem chkT_parts :
    (∀ x < 31, wordAct (tWords.getD x []) 0 = x) ∧ ∀ i < 62, wordAct (schWord i) 0 = 0 := by
  have h := chk_parts.1
  simp only [chkT, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem kwRow_inj {k k' : ℕ} (hk : k < 31) (hk' : k' < 31)
    (h : kwRow k = kwRow k') : k = k' := by
  by_contra hne
  have hd := chk_parts.2.2.2.1
  simp only [chkDistinct, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd k hk k' hk' with h1 | h1
  · exact hne h1
  · exact differs_toVec h1 (congrArg ofRow h)

@[expose] noncomputable def tJ (x : ℕ) : G₀ := wordProd m4gen (tWords.getD x [])

@[expose] noncomputable def yJ (i : ℕ) : G₀ := wordProd m4gen (schWord i)

theorem tJ_mem (x : ℕ) : tJ x ∈ CFSG.Quasithin.KGJ4.M4 := wordProd_mem _ m4gen_mem _

theorem yJ_mem (i : ℕ) : yJ i ∈ CFSG.Quasithin.KGJ4.M4 := wordProd_mem _ m4gen_mem _

theorem tJ_zero : tJ 0 = 1 := by
  rw [tJ, show tWords.getD 0 [] = [] by decide]
  rfl

theorem wordProd_append' (w w' : List ℤ) :
    wordProd m4gen (w ++ w') = wordProd m4gen w * wordProd m4gen w' := by
  unfold wordProd
  rw [List.map_append, List.prod_append]

theorem wordProd_m4gen_single (s : ℕ) : wordProd m4gen [((s : ℕ) : ℤ) + 1] = m4gen s := by
  simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [ite_eq_left (by omega)]
  congr 1

theorem yJ_eq {i : ℕ} (hi : i < 62) :
    yJ i = (tJ ((kwSig.getD (i % 2) []).getD (i / 2) 0))⁻¹ * m4gen (i % 2) * tJ (i / 2) := by
  unfold yJ schWord tJ
  rw [wordProd_append', wordProd_append',
    CFSG.Quasithin.KGC31.J4M4.wordProd_invW _
      (tWords_good _ (kwSig_lt (i % 2) (by omega) (i / 2) (by omega))).ne_zero,
    wordProd_m4gen_single]

theorem tJ_smul
    {x : ℕ} (hx : x < 31) :
    tJ x • kwRow 0 = kwRow x := by
  rw [tJ, wordProd_smul_kwRow (tWords_good x hx) (by norm_num), chkT_parts.1 x hx]

theorem yJ_smul
    {i : ℕ} (hi : i < 62) :
    yJ i • kwRow 0 = kwRow 0 := by
  rw [yJ, wordProd_smul_kwRow (schWord_good hi) (by norm_num), chkT_parts.2 i hi]

theorem w1_eq_word : CFSG.Quasithin.KGJ4.w1 = wordProd m4gen [1] := by
  simp [wordProd, m4gen]

theorem w2_eq_word : CFSG.Quasithin.KGJ4.w2 = wordProd m4gen [2] := by
  simp [wordProd, m4gen]

theorem inv_wordProd_single (l : ℤ) (hl : l ≠ 0) :
    (wordProd m4gen [l])⁻¹ = wordProd m4gen [-l] := by
  have := CFSG.Quasithin.KGC31.J4M4.wordProd_invW m4gen (w := [l]) (fun l' hl' => by
    rw [List.mem_singleton] at hl'
    rw [hl']
    exact hl)
  rw [← this]
  rfl

theorem M4_smul_kwRow {m : G₀}
    (hm : m ∈ CFSG.Quasithin.KGJ4.M4) :
    ∀ k < 31, ∃ k' < 31, m • kwRow k = kwRow k' := by
  induction hm using Subgroup.closure_induction'' with
  | mem x hx =>
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, idxAct_lt hk, by rw [w1_eq_word, letter_smul_kwRow (by norm_num) hk]⟩
    · exact ⟨_, idxAct_lt hk, by rw [w2_eq_word, letter_smul_kwRow (by norm_num) hk]⟩
  | inv_mem x hx =>
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, idxAct_lt hk, by
        rw [w1_eq_word, inv_wordProd_single _ (by norm_num), letter_smul_kwRow (by norm_num) hk]⟩
    · exact ⟨_, idxAct_lt hk, by
        rw [w2_eq_word, inv_wordProd_single _ (by norm_num), letter_smul_kwRow (by norm_num) hk]⟩
  | one => exact fun k hk => ⟨k, hk, one_smul _ _⟩
  | mul x y _ _ hx hy =>
    intro k hk
    obtain ⟨k₁, hk₁, h₁⟩ := hy k hk
    obtain ⟨k₂, hk₂, h₂⟩ := hx k₁ hk₁
    exact ⟨k₂, hk₂, by rw [mul_smul, h₁, h₂]⟩

theorem orbit_kwRow :
    MulAction.orbit ↥CFSG.Quasithin.KGJ4.M4 (kwRow 0) =
      Set.range fun k : Fin 31 => kwRow (k : ℕ) := by
  ext v
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    obtain ⟨k', hk', h⟩ := M4_smul_kwRow hm 0 (by norm_num)
    exact ⟨⟨k', hk'⟩, h.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨tJ k, tJ_mem k⟩, tJ_smul k.2⟩

theorem card_orbit_kwRow :
    Nat.card (MulAction.orbit ↥CFSG.Quasithin.KGJ4.M4 (kwRow 0)) = 31 := by
  rw [orbit_kwRow, Nat.card_range_of_injective, Nat.card_fin]
  intro k k' h
  exact Fin.ext (kwRow_inj k.2 k'.2 h)

@[expose] noncomputable def Ycl : Subgroup G₀ := Subgroup.closure {g | ∃ i < 62, g = yJ i}

theorem schreier_claim
    {m : G₀}
    (hm : m ∈ CFSG.Quasithin.KGJ4.M4) :
    ∃ k < 31, m • kwRow 0 = kwRow k ∧ (tJ k)⁻¹ * m ∈ Ycl := by
  induction hm using Subgroup.closure_induction_left with
  | one =>
    exact ⟨0, by norm_num, one_smul _ _, by rw [tJ_zero, inv_one, mul_one]; exact Ycl.one_mem⟩
  | mul_left x hx y _ ih =>
    obtain ⟨k, hk, hyk, hY⟩ := ih
    have hs : ∃ s < 2, x = m4gen s := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    obtain ⟨s, hs2, rfl⟩ := hs
    have hlet : m4gen s • kwRow k = kwRow ((kwSig.getD s []).getD k 0) := by
      have := letter_smul_kwRow (l := (s : ℤ) + 1) (by omega) hk
      rw [wordProd_m4gen_single] at this
      rw [this]
      congr 1
      unfold idxAct
      rw [ite_eq_left (by omega)]
      congr 2
    refine ⟨(kwSig.getD s []).getD k 0, kwSig_lt s (by omega) k hk, by rw [mul_smul, hyk, hlet],
      ?_⟩
    have hy := yJ_eq (i := 2 * k + s) (by omega)
    rw [show (2 * k + s) % 2 = s by omega, show (2 * k + s) / 2 = k by omega] at hy
    have e : (tJ ((kwSig.getD s []).getD k 0))⁻¹ * (m4gen s * y) =
        yJ (2 * k + s) * ((tJ k)⁻¹ * y) := by rw [hy]; group
    rw [e]
    exact Ycl.mul_mem (Subgroup.subset_closure ⟨2 * k + s, by omega, rfl⟩) hY
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, hk, hyk, hY⟩ := ih
    have hs : ∃ s < 2, x = m4gen s := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    obtain ⟨s, hs2, rfl⟩ := hs
    set k'' := (kwSig.getD (s + 2) []).getD k 0 with hk''
    have hk''lt : k'' < 31 := kwSig_lt (s + 2) (by omega) k hk
    have hlet : (m4gen s)⁻¹ • kwRow k = kwRow k'' := by
      have := letter_smul_kwRow (l := -((s : ℤ) + 1)) (by omega) hk
      rw [← inv_wordProd_single _ (by omega), wordProd_m4gen_single] at this
      rw [this]
      congr 1
    refine ⟨k'', hk''lt, by rw [mul_smul, hyk, hlet], ?_⟩
    have hy := yJ_eq (i := 2 * k'' + s) (by omega)
    rw [show (2 * k'' + s) % 2 = s by omega, show (2 * k'' + s) / 2 = k'' by omega,
      hk'', kwSig_inv s hs2 k hk, ← hk''] at hy
    have e : (tJ k'')⁻¹ * ((m4gen s)⁻¹ * y) = (yJ (2 * k'' + s))⁻¹ * ((tJ k)⁻¹ * y) := by
      rw [hy]; group
    rw [e]
    exact Ycl.mul_mem (Ycl.inv_mem (Subgroup.subset_closure ⟨2 * k'' + s, by omega, rfl⟩)) hY

theorem mem_Ycl_iff
    (m : G₀) :
    m ∈ Ycl ↔ m ∈ CFSG.Quasithin.KGJ4.M4 ∧ m • kwRow 0 = kwRow 0 := by
  constructor
  · intro hm
    induction hm using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨yJ_mem i, yJ_smul hi⟩
    | one => exact ⟨Subgroup.one_mem _, one_smul _ _⟩
    | mul x y _ _ hx hy => exact ⟨Subgroup.mul_mem _ hx.1 hy.1, by rw [mul_smul, hy.2, hx.2]⟩
    | inv x _ hx =>
      refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
      calc x⁻¹ • kwRow 0 = x⁻¹ • (x • kwRow 0) := by rw [hx.2]
        _ = kwRow 0 := inv_smul_smul x _
  · rintro ⟨hm, hfix⟩
    obtain ⟨k, hk, hmk, hY⟩ := schreier_claim hm
    have hk0 : k = 0 := (kwRow_inj hk (by norm_num) (hmk.symm.trans hfix)).symm ▸ rfl
    rw [hk0, tJ_zero, inv_one, one_mul] at hY
    exact hY

theorem card_M4_eq :
    Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 31 * Nat.card ↥Ycl := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥CFSG.Quasithin.KGJ4.M4 (kwRow 0))
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_orbit_kwRow] at h1
  have h2 : (MulAction.stabilizer ↥CFSG.Quasithin.KGJ4.M4 (kwRow 0)).map
      CFSG.Quasithin.KGJ4.M4.subtype = Ycl := by
    ext m
    rw [mem_Ycl_iff]
    constructor
    · rintro ⟨⟨m, hm⟩, hfix, rfl⟩
      exact ⟨hm, hfix⟩
    · rintro ⟨hm, hfix⟩
      exact ⟨⟨m, hm⟩, hfix, rfl⟩
  have h3 : Nat.card ↥Ycl =
      Nat.card ↥(MulAction.stabilizer ↥CFSG.Quasithin.KGJ4.M4 (kwRow 0)) := by
    rw [← h2, Subgroup.card_map_of_injective CFSG.Quasithin.KGJ4.M4.subtype_injective]
  rw [h3]
  omega

theorem eq_of_eqRows_Mx {x y : G₀} {X Y : Array V2} (hx : Mx x = rowsMatrix X)
    (hy : Mx y = rowsMatrix Y) (h : eqRows X Y = true) : x = y :=
  Mx_injective (by rw [hx, hy, rowsMatrix_eq_of_eqRows h])

theorem rowsMatrix_ne_of_rowsDiffer {A B : Array V2} (h : rowsDiffer A B = true) :
    rowsMatrix A ≠ rowsMatrix B := by
  unfold rowsDiffer at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hd⟩ := h
  intro e
  apply differs_toVec hd
  funext j
  have := congrFun (congrFun e ⟨i, hi⟩) j
  rwa [rowsMatrix_apply, rowsMatrix_apply] at this

theorem Mx_gJ
    : Mx gJ = rowsMatrix (gRows ()) := Mx_wordProd_baseJ j4Facts.mat gWord

theorem Mx_gJ_inv : Mx gJ⁻¹ = rowsMatrix (gInvRows ()) := by
  rw [gJ, ← CFSG.Quasithin.KGC31.J4M4.wordProd_invW _ (by decide), Mx_wordProd_baseJ j4Facts.mat]
  rfl

@[expose] noncomputable def hJ (i : ℕ) : G₀ := gJ * yJ i * gJ⁻¹

@[expose] noncomputable def Kc : Subgroup G₀ := Ycl.map (MulAut.conj gJ).toMonoidHom

theorem card_Kc : Nat.card ↥Kc = Nat.card ↥Ycl :=
  Subgroup.card_map_of_injective (MulAut.conj gJ).injective

theorem Kc_eq_closure : Kc = Subgroup.closure {x | ∃ i < 62, x = hJ i} := by
  rw [Kc, Ycl, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨yJ i, ⟨i, hi, rfl⟩, rfl⟩

theorem Kc_le_Hj :
    Kc ≤ Hj := by
  rintro _ ⟨y, hy, rfl⟩
  have hfix := ((mem_Ycl_iff y).mp hy).2
  apply CFSG.Sporadic.J4.QT2.mem_Hj_of_smul_root j4Facts
  have h0 := kwRow_zero chkKW_true j4Facts.mat
  show (gJ * y * gJ⁻¹) • CFSG.Sporadic.J4.QT2.w₀ = CFSG.Sporadic.J4.QT2.w₀
  rw [mul_smul, mul_smul, ← h0, hfix, h0, smul_inv_smul]

section E


theorem eta_coord_bijective
    : Function.Bijective
    (fun c : Fin 2048 => (⟨eta uJ 11 c, eta_mem_Eg 11 le_rfl c⟩ : ↥(Eg uJ 11))) := by
  have hM := j4Facts.mat
  refine Function.Injective.bijective_of_nat_card_le (fun c d h => ?_) ?_
  · exact Fin.ext (eta_inj hM c (by have := c.2; omega) d (by have := d.2; omega)
      (congrArg Subtype.val h))
  · rw [card_Eg_uJ hM, Nat.card_fin]
    norm_num

@[expose] noncomputable def eE
    : Fin 2048 ≃ ↥(Eg uJ 11) := Equiv.ofBijective _ eta_coord_bijective

theorem eE_apply (c : Fin 2048)
    : ((eE c : ↥(Eg uJ 11)) : G₀) = eta uJ 11 c := rfl

theorem Hj_le_normalizer_E
    : Hj ≤ Subgroup.normalizer ((Eg uJ 11 : Subgroup G₀) : Set G₀) :=
  (normalizer_Eg_eq_Hj j4Facts).ge

@[expose] noncomputable def psiH
    : ↥Hj →* Equiv.Perm (Fin 2048) :=
  (Equiv.permCongrHom eE.symm).toMonoidHom.comp
    ((MulAut.toPerm _).comp ((Eg uJ 11).normalizerMonoidHom.comp
      (Subgroup.inclusion Hj_le_normalizer_E)))

theorem psiH_apply_eq_iff (h : ↥Hj)
    (c c' : Fin 2048) :
    psiH h c = c' ↔ (h : G₀) * eta uJ 11 c * (h : G₀)⁻¹ = eta uJ 11 c' := by
  have e1 : psiH h c = eE.symm ((Eg uJ 11).normalizerMonoidHom
      (Subgroup.inclusion Hj_le_normalizer_E h) (eE c)) := rfl
  rw [e1, Equiv.symm_apply_eq]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe, eE_apply, eE_apply] at this
  · intro h1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, eE_apply, eE_apply]
    exact h1

theorem mem_E_of_psiH_eq_one {h : ↥Hj}
    (h1 : psiH h = 1) : (h : G₀) ∈ Eg uJ 11 := by
  have hM := j4Facts.mat
  refine centralizer_Hj hM j4Facts h h.2 fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).mp hy
  have h2 := (psiH_apply_eq_iff h ⟨c, by omega⟩ ⟨c, by omega⟩).mp (by rw [h1]; rfl)
  calc (h : G₀) * eta uJ 11 c = (h : G₀) * eta uJ 11 c * (h : G₀)⁻¹ * h := by group
    _ = eta uJ 11 c * h := by rw [h2]

theorem psiH_eq_one_of_mem_E {h : ↥Hj}
    (hE : (h : G₀) ∈ Eg uJ 11) : psiH h = 1 := by
  have hM := j4Facts.mat
  refine Equiv.ext fun c => (psiH_apply_eq_iff h c c).mpr ?_
  rw [Eg_comm (elem_uJ hM) hE (eta_mem_Eg 11 le_rfl c), mul_inv_cancel_right]

theorem conj_eta_xorMasks {h : G₀}
    {ms : List ℕ}
    (hms : ∀ k < 11, h * eta uJ 11 (2 ^ k) * h⁻¹ = eta uJ 11 (ms.getD k 0)) (c : ℕ) :
    h * eta uJ 11 c * h⁻¹ = eta uJ 11 (xorMasks ms c) := by
  have hM := j4Facts.mat
  have key : ∀ m ≤ 11, h * eta uJ m c * h⁻¹ = eta uJ 11
      ((List.range m).foldl (fun acc k => if c.testBit k then acc ^^^ ms.getD k 0 else acc) 0) := by
    intro m
    induction m with
    | zero => intro _; simp [eta]
    | succ m ih =>
      intro hm
      rw [eta_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hum : uJ m = eta uJ 11 (2 ^ m) := (eta_two_pow (by omega)).symm
      by_cases hb : c.testBit m
      · rw [ite_eq_left hb, ite_eq_left hb, eta_xor (elem_uJ hM) le_rfl, ← ih (by omega),
          ← hms m (by omega), hum]
        group
      · rw [ite_eq_right hb, ite_eq_right hb, mul_one, ih (by omega)]
  exact key 11 le_rfl

end E

section Img


theorem chkMasks_parts : ∀ i < 62, ∀ k < 11,
    eqRows (mulRows (mulRows (hRows i) (etaRows (uTab (locMats ()) (locInvs ())) 11 (2 ^ k)))
      (hInvRows i)) (etaRows (uTab (locMats ()) (locInvs ())) 11 ((maskTab.getD i []).getD k 0)) =
      true := by
  have h := chk_parts.2.1
  simp only [chkMasks, chkMasksWith, List.all_eq_true, List.mem_range] at h
  exact h

theorem Mx_hJ (i : ℕ) : Mx (hJ i) = rowsMatrix (hRows i) := by
  rw [hJ, map_mul, map_mul, Mx_gJ, Mx_yJ, Mx_gJ_inv, hRows, rowsMatrix_mulRows, rowsMatrix_mulRows]
where
  Mx_yJ : Mx (yJ i) = rowsMatrix (wordRows (m4Mats ()) (m4Invs ()) (schWord i)) :=
    Mx_wordProd_m4gen j4Facts.mat (schWord i)

theorem Mx_hJ_inv {i : ℕ} (hi : i < 62)
    : Mx (hJ i)⁻¹ = rowsMatrix (hInvRows i) := by
  have e : (hJ i)⁻¹ = gJ * wordProd m4gen (invW (schWord i)) * gJ⁻¹ := by
    rw [CFSG.Quasithin.KGC31.J4M4.wordProd_invW _ (schWord_good hi).ne_zero, hJ, yJ]
    group
  rw [e, map_mul, map_mul, Mx_gJ, Mx_wordProd_m4gen j4Facts.mat, Mx_gJ_inv, hInvRows,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem hJ_conj_two_pow {i : ℕ}
    (hi : i < 62) {k : ℕ} (hk : k < 11) :
    hJ i * eta uJ 11 (2 ^ k) * (hJ i)⁻¹ = eta uJ 11 ((maskTab.getD i []).getD k 0) := by
  have hM := j4Facts.mat
  refine eq_of_eqRows_Mx ?_ (Mx_eta hM 11 le_rfl _) (chkMasks_parts i hi k hk)
  rw [map_mul, map_mul, Mx_hJ, Mx_eta hM 11 le_rfl, Mx_hJ_inv hi, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem maskTab_lt : ∀ i < 62, ∀ k < 11, (maskTab.getD i []).getD k 0 < 2 ^ 11 := by
  decide +kernel

theorem xorMasks_lt {ms : List ℕ} (hms : ∀ k < 11, ms.getD k 0 < 2 ^ 11) (c : ℕ) :
    xorMasks ms c < 2 ^ 11 := by
  have key : ∀ m ≤ 11, (List.range m).foldl
      (fun acc k => if c.testBit k then acc ^^^ ms.getD k 0 else acc) 0 < 2 ^ 11 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · exact Nat.xor_lt_two_pow (ih (by omega)) (hms m (by omega))
      · exact ih (by omega)
  exact key 11 le_rfl

theorem hJ_mem_Kc {i : ℕ} (hi : i < 62) : hJ i ∈ Kc :=
  ⟨yJ i, Subgroup.subset_closure ⟨i, hi, rfl⟩, rfl⟩

@[expose] noncomputable def psiK :
    ↥Kc →* Equiv.Perm (Fin 2048) :=
  psiH.comp (Subgroup.inclusion Kc_le_Hj)

theorem rep_psiK
    {i : ℕ} (hi : i < 62) :
    CFSG.Monster.B.Co2.Rep 2048 (psiArr i) (psiK ⟨hJ i, hJ_mem_Kc hi⟩) := by
  intro x
  have hlt := xorMasks_lt (maskTab_lt i hi) x
  have h1 : psiK ⟨hJ i, hJ_mem_Kc hi⟩ x = ⟨xorMasks (maskTab.getD i []) x, by omega⟩ := by
    refine (psiH_apply_eq_iff _ x _).mpr ?_
    exact conj_eta_xorMasks (fun k hk => hJ_conj_two_pow hi hk) x
  rw [h1, psiArr, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.2]

end Img

theorem psiS_size : (psiS ()).size = 71 := by
  simp [psiS, psiOrig]

@[expose] def psiBaseFin : List (Fin 2048) := [1, 2, 4, 32]

theorem psiBaseFin_nodup : psiBaseFin.Nodup := by decide

theorem psiBaseFin_val : (psiBaseFin.map Fin.val).toArray = psiBase.toArray := rfl

@[expose] noncomputable def Qpsi : CFSG.Certificates.RawSchreierDatum 2048 :=
  CFSG.Certificates.RawSchreierDatum.ofArrays 2048 (by norm_num) (psiS ()) 62
    (by rw [psiS_size]; norm_num) psiBaseFin psiBaseFin_nodup psiW

theorem chkPsi_parts :
    rawChainOK 2048 ((psiS ()).extract 0 62) (psiS ()) psiBase.toArray psiW 1 = true ∧
      rawOrbitSizes 2048 (psiS ()) psiBase.toArray = [120, 84, 16, 2] ∧
      ∀ i < 62, eqA 2048 (psiS ())[i]! (psiArr i) = true := by
  have h := chk_parts.2.2.2.2.1
  simp only [chkPsi, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_Qpsi : Nat.card Qpsi.originalSubgroup = 322560 := by
  obtain ⟨h1, h2, -⟩ := chkPsi_parts
  rw [← psiBaseFin_val] at h1 h2
  have hA := CFSG.Certificates.chainArrays_ofArrays (n := 2048) (hn := by norm_num) (k := 62)
    (hk := by rw [psiS_size]; norm_num) (hb := psiBaseFin_nodup) (W := psiW)
    (CFSG.Certificates.chainCheckFacts h1).strong_inv
  rw [Qpsi, CFSG.Certificates.card_originalSubgroup_of_chainOK hA (by norm_num) h1, h2]
  norm_num

theorem perm_psiS_eq
    {i : ℕ} (hi : i < 62) :
    CFSG.Monster.B.Co2.permOfArr 2048 (psiS ())[i]! = psiK ⟨hJ i, hJ_mem_Kc hi⟩ := by
  obtain ⟨h1, -, h3⟩ := chkPsi_parts
  have hinv := (CFSG.Certificates.chainCheckFacts h1).strong_inv i (by rw [psiS_size]; omega)
  exact CFSG.Monster.B.Co2.eq_of_eqA (CFSG.Monster.B.Co2.rep_permOfArr hinv).1 (rep_psiK hi)
    (h3 i hi)

theorem range_psiK :
    psiK.range = Qpsi.originalSubgroup := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hk⟩, rfl⟩
    have hk' : k ∈ Subgroup.closure {x | ∃ i < 62, x = hJ i} := Kc_eq_closure ▸ hk
    induction hk' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [← perm_psiS_eq hi]
      apply Subgroup.subset_closure
      show _ ∈ Qpsi.original.toList
      rw [Qpsi, CFSG.Certificates.RawSchreierDatum.mem_ofArrays_original]
      exact ⟨i, hi, rfl⟩
    | one =>
      have : (⟨1, hk⟩ : ↥Kc) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      have hxK : x ∈ Kc := Kc_eq_closure ▸ hx
      have hyK : y ∈ Kc := Kc_eq_closure ▸ hy
      have : (⟨x * y, hk⟩ : ↥Kc) = ⟨x, hxK⟩ * ⟨y, hyK⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (ihx hxK) (ihy hyK)
    | inv x hx ihx =>
      have hxK : x ∈ Kc := Kc_eq_closure ▸ hx
      have : (⟨x⁻¹, hk⟩ : ↥Kc) = (⟨x, hxK⟩ : ↥Kc)⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (ihx hxK)
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    obtain ⟨i, hi, rfl⟩ := (CFSG.Certificates.RawSchreierDatum.mem_ofArrays_original).mp hg
    rw [perm_psiS_eq hi]
    exact ⟨_, rfl⟩

theorem card_range_psiK :
    Nat.card psiK.range = 322560 := by
  rw [range_psiK, card_Qpsi]

theorem chkWit_parts : ∀ c < 1024,
    rowsDiffer (mulRows (mulRows (wRowsWith (uTab (locMats ()) (locInvs ())))
      ((fTab ())[witJ]?.getD idRows)) (wRowsWith (uTab (locMats ()) (locInvs ()))))
      (fRows (fTab ()) c) = true := by
  have h := chk_parts.2.2.1
  simp only [chkWit, chkWitWith, List.all_eq_true, List.mem_range] at h
  exact h

theorem chkKE_parts : ∀ j < 10,
    eqRows (wordRows (m4Mats ()) (m4Invs ()) (keWords.getD j []))
      (geRowsWith (uTab (locMats ()) (locInvs ())) (keMasks.getD j 0)) = true := by
  have h := chk_parts.2.2.2.2.2
  simp only [chkKE, chkKEWith, List.all_eq_true, List.mem_range] at h
  exact h

@[expose] noncomputable def wJ : G₀ := gJ⁻¹ * eta uJ 11 (2 ^ witK) * gJ

theorem Mx_wJ :
    Mx wJ = rowsMatrix (wRowsWith (uTab (locMats ()) (locInvs ()))) := by
  rw [wJ, map_mul, map_mul, Mx_gJ_inv, Mx_eta j4Facts.mat 11 le_rfl, Mx_gJ, wRowsWith,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem wJ_inv : wJ⁻¹ = wJ := by
  have hsq := eta_sq (elem_uJ j4Facts.mat) (2 ^ witK)
  have he : (eta uJ 11 (2 ^ witK))⁻¹ = eta uJ 11 (2 ^ witK) :=
    inv_eq_of_mul_eq_one_right hsq
  rw [wJ, mul_inv_rev, mul_inv_rev, he, inv_inv, mul_assoc]

theorem eta_four_not_mem_Kc :
    eta uJ 11 (2 ^ witK) ∉ Kc := by
  have hM := j4Facts.mat
  have hc := chkF_true
  rintro ⟨y, hy, hyc⟩
  have hyw : y = wJ := by
    rw [wJ, ← hyc]
    show y = gJ⁻¹ * (gJ * y * gJ⁻¹) * gJ
    group
  rw [hyw] at hy
  have hwM : wJ ∈ CFSG.Quasithin.KGJ4.M4 := ((mem_Ycl_iff wJ).mp hy).1
  have hwN := M4_le_eNorm hM hc hwM
  have hf : fJ 0 ∈ eSub (fJ_basis hM hc) := mem_eSub (fJ_basis hM hc) 0
  have hconj : wJ * fJ 0 * wJ⁻¹ ∈ eSub (fJ_basis hM hc) :=
    (Subgroup.mem_normalizer_iff.mp hwN _).mp hf
  obtain ⟨v, hv⟩ := (mem_eSub_iff (fJ_basis hM hc) _).mp hconj
  obtain ⟨c, hc1024, rfl⟩ := exists_codeVec v
  rw [eElt_fJ] at hv
  apply rowsMatrix_ne_of_rowsDiffer (chkWit_parts c hc1024)
  have h1 : Mx (eta fJn 10 c) = rowsMatrix (fRows (fTab ()) c) := Mx_eta_fJ hM 10 le_rfl c
  have h2 : Mx (wJ * fJ 0 * wJ⁻¹) = rowsMatrix (mulRows (mulRows
      (wRowsWith (uTab (locMats ()) (locInvs ()))) ((fTab ())[witJ]?.getD idRows))
      (wRowsWith (uTab (locMats ()) (locInvs ())))) := by
    have hf0 : Mx (fJ 0) = rowsMatrix ((fTab ())[witJ]?.getD idRows) :=
      Mx_fJn hM (n := 0) (by norm_num)
    rw [wJ_inv, map_mul, map_mul, Mx_wJ, hf0, rowsMatrix_mulRows, rowsMatrix_mulRows]
  rw [← h2, ← h1, hv]

theorem card_Kc_inf_E_le :
    Nat.card ↥(Kc ⊓ Eg uJ 11) ≤ 2 ^ 10 := by
  have hM := j4Facts.mat
  have hE := card_Eg_uJ hM
  have hlt : Kc ⊓ Eg uJ 11 < Eg uJ 11 := by
    refine lt_of_le_of_ne inf_le_right fun h => eta_four_not_mem_Kc ?_
    have hmem : eta uJ 11 (2 ^ witK) ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl _
    rw [← h] at hmem
    exact hmem.1
  have : Finite ↥(Eg uJ 11) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_dvd_of_le (inf_le_right : Kc ⊓ Eg uJ 11 ≤ Eg uJ 11)
  rw [hE] at h1 h2
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rw [hm'] at h1 ⊢
  have : m < 11 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem keMasks_lt : ∀ k < 11, keMasks.getD k 0 < 2 ^ 11 := by decide

@[expose] def xorKE (c : ℕ) : ℕ :=
  (List.range 10).foldl (fun acc k => if c.testBit k then acc ^^^ keMasks.getD k 0 else acc) 0

theorem xorKE_eq_zero : ∀ c < 1024, xorKE c = 0 → c = 0 := by
  unfold xorKE; decide +kernel

theorem xorKE_lt (c : ℕ) : xorKE c < 2 ^ 11 := by
  have key : ∀ m, (List.range m).foldl
      (fun acc k => if c.testBit k then acc ^^^ keMasks.getD k 0 else acc) 0 < 2 ^ 11 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · refine Nat.xor_lt_two_pow ih ?_
        by_cases hm : m < 11
        · exact keMasks_lt m hm
        · rw [List.getD_eq_default _ _ (by simp [keMasks]; omega)]
          norm_num
      · exact ih
  exact key 10

theorem eta_keMask_mem_Kc
    {j : ℕ} (hj : j < 10) :
    eta uJ 11 (keMasks.getD j 0) ∈ Kc := by
  have hM := j4Facts.mat
  set y := wordProd m4gen (keWords.getD j []) with hydef
  have hy : y = gJ⁻¹ * eta uJ 11 (keMasks.getD j 0) * gJ := by
    refine eq_of_eqRows_Mx (Mx_wordProd_m4gen hM _) ?_ (chkKE_parts j hj)
    rw [map_mul, map_mul, Mx_gJ_inv, Mx_eta hM 11 le_rfl, Mx_gJ, geRowsWith, rowsMatrix_mulRows,
      rowsMatrix_mulRows]
  have hfix : y • kwRow 0 = kwRow 0 := by
    have h0 := kwRow_zero chkKW_true hM
    have hE : eta uJ 11 (keMasks.getD j 0) • CFSG.Sporadic.J4.QT2.w₀ =
        CFSG.Sporadic.J4.QT2.w₀ :=
      CFSG.Sporadic.J4.QT2.smul_root_of_mem_Hj hM (Eg_le_Hj (eta_mem_Eg 11 le_rfl _))
    rw [hy, h0, mul_smul, mul_smul, smul_inv_smul, hE]
  have hyY : y ∈ Ycl := (mem_Ycl_iff y).mpr ⟨wordProd_mem _ m4gen_mem _, hfix⟩
  refine ⟨y, hyY, ?_⟩
  show gJ * y * gJ⁻¹ = _
  rw [hy]
  group

@[expose] noncomputable def keJ (j : Fin 10) : G₀ := eta uJ 11 (keMasks.getD j 0)

theorem eta_xorKE (c : ℕ) :
    eta (fun j => eta uJ 11 (keMasks.getD j 0)) 10 c = eta uJ 11 (xorKE c) := by
  have hM := j4Facts.mat
  have key : ∀ m, eta (fun j => eta uJ 11 (keMasks.getD j 0)) m c = eta uJ 11
      ((List.range m).foldl (fun acc k => if c.testBit k then acc ^^^ keMasks.getD k 0 else acc)
        0) := by
    intro m
    induction m with
    | zero => simp [eta]
    | succ m ih =>
      rw [eta_succ, ih, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · rw [eta_xor (elem_uJ hM) le_rfl]
      · rw [mul_one]
  exact key 10

theorem keJ_basis : EBasis keJ := by
  have hM := j4Facts.mat
  refine ⟨fun i => eta_sq (elem_uJ hM) _, fun i j => eta_comm (elem_uJ hM) _ _, fun v hv => ?_⟩
  obtain ⟨c, hc, rfl⟩ := exists_codeVec v
  have h1 : eElt keJ (codeVec c) = eta uJ 11 (xorKE c) := by
    rw [← eta_xorKE]
    exact eElt_codeVec_eq_eta (fun j => eta uJ 11 (keMasks.getD j 0)) 10 c
  rw [h1] at hv
  have h2 : xorKE c = 0 := by
    by_contra hne
    exact eta_ne_one hM hne (xorKE_lt c) hv
  rw [xorKE_eq_zero c hc h2]
  funext i
  simp [codeVec]

theorem card_Kc_inf_E_ge :
    2 ^ 10 ≤ Nat.card ↥(Kc ⊓ Eg uJ 11) := by
  have hle : eSub keJ_basis ≤ Kc ⊓ Eg uJ 11 := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨eta_keMask_mem_Kc j.2, eta_mem_Eg 11 le_rfl _⟩
  have : Finite ↥(Kc ⊓ Eg uJ 11) :=
    Nat.finite_of_card_ne_zero (by
      have h := card_Kc_inf_E_le
      intro h0
      have : Nat.card ↥(eSub keJ_basis) ≤ Nat.card ↥(Kc ⊓ Eg uJ 11) := by
        exact Subgroup.card_le_of_le hle
      rw [card_eSub, h0] at this
      norm_num at this)
  calc 2 ^ 10 = Nat.card ↥(eSub keJ_basis) := (card_eSub keJ_basis).symm
    _ ≤ Nat.card ↥(Kc ⊓ Eg uJ 11) := Subgroup.card_le_of_le hle

theorem card_ker_psiK :
    Nat.card psiK.ker = Nat.card ↥(Kc ⊓ Eg uJ 11) := by
  refine le_antisymm ?_ ?_
  · refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥Kc) : G₀), (k : ↥Kc).2,
      mem_E_of_psiH_eq_one (h := Subgroup.inclusion Kc_le_Hj k) k.2⟩) ?_
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  · refine Nat.card_le_card_of_injective (fun x => ⟨⟨x, x.2.1⟩,
      psiH_eq_one_of_mem_E (h := Subgroup.inclusion Kc_le_Hj ⟨x, x.2.1⟩) x.2.2⟩) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun k : psiK.ker => ((k : ↥Kc) : G₀)) h)

theorem card_Kc_eq :
    Nat.card ↥Kc = 2 ^ 10 * 322560 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup psiK.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange psiK).toEquiv, card_range_psiK,
    card_ker_psiK, le_antisymm card_Kc_inf_E_le card_Kc_inf_E_ge] at h
  rw [h]
  ring

theorem card_M4 :
    Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640 := by
  rw [card_M4_eq, ← card_Kc, card_Kc_eq]
  norm_num

end CFSG.Quasithin.J4M4Card
