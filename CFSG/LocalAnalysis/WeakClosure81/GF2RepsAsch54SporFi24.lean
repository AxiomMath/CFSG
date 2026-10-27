module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOut2
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporIndexTwo
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import Certificates.Certificate1208101

import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace SporFi24

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.LevelChain CFSG.Sporadic.LevelChain.Native
open CFSG.Sporadic.Fi23 (slpG slpG_eq rep_slpLetters slpInv_full)
open CFSG.Sporadic.Fi23.Native (slpOK slpLetters)
open CFSG.Sporadic.Fi24.Native (normWords genTables)
open CFSG.Sporadic.Fi24Pair.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem selT : ∀ k < chainT.sel.size, chainT.sel[k]! < W.size := by decide +kernel

theorem selA : ∀ k < chainA.sel.size, chainA.sel[k]! < W.size := by decide +kernel

theorem selB : ∀ k < chainB.sel.size, chainB.sel[k]! < W.size := by decide +kernel

theorem twT : ∀ k < chainT.ntw, twistOK W chainT.sel[k]! chainT.sel[k + chainT.ntw]! = true := by
  decide +kernel

theorem twA : ∀ k < chainA.ntw, twistOK W chainA.sel[k]! chainA.sel[k + chainA.ntw]! = true := by
  decide +kernel

theorem twB : ∀ k < chainB.ntw, twistOK W chainB.sel[k]! chainB.sel[k + chainB.ntw]! = true := by
  decide +kernel


theorem W_lineNA : W[lineNA]! = shiftWord normWords[0]! := by decide +kernel

theorem W_lineNB : W[lineNB]! = shiftWord normWords[1]! := by decide +kernel

theorem line_zero : line 0 = CFSG.Sporadic.Fi24.a := by rw [line_eq_gs (by norm_num), gs_zero]

theorem line_one : line 1 = CFSG.Sporadic.Fi24.b := by rw [line_eq_gs (by norm_num), gs_one]

theorem letter_eq {j : ℕ} {z : ℤ} (h3 : 3 ≤ z.natAbs) (hzj : z.natAbs - 3 < j) :
    (if z.natAbs ≤ 2 then genG z else if z.natAbs - 3 < j then
      (if 0 < z then slpG genG W (z.natAbs - 3) else (slpG genG W (z.natAbs - 3))⁻¹) else 1) =
      if 0 < z then line (z.natAbs - 3) else (line (z.natAbs - 3))⁻¹ := by
  rw [if_neg (by omega), if_pos hzj]
  rfl

theorem slpG_shiftWord {j : ℕ} (hj : 13 ≤ j) {w : List ℤ}
    (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13) (hW : W[j]! = shiftWord w) :
    line j = wordG genLetterG w := by
  unfold line
  rw [slpG_eq, hW]
  unfold wordG shiftWord
  rw [List.map_map]
  refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
  obtain ⟨hl0, hl13⟩ := hw l hl
  simp only [Function.comp_apply]
  unfold genLetterG
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · rw [if_neg (show ¬ (0 < l) by omega), letter_eq (by omega) (by omega),
      if_neg (show ¬ (0 < l - 2) by omega), show (l - 2).natAbs - 3 = l.natAbs - 1 by omega,
      line_eq_gs (j := l.natAbs - 1) (by omega), if_neg (show ¬ (0 < l) by omega)]
  · rw [if_pos hpos, letter_eq (by omega) (by omega), if_pos (show 0 < l + 2 by omega),
      show (l + 2).natAbs - 3 = l.natAbs - 1 by omega, line_eq_gs (j := l.natAbs - 1) (by omega),
      if_pos hpos]

theorem line_lineNA : line lineNA = nA := by
  unfold nA extWord
  exact slpG_shiftWord (by decide) (normWords_letters (by norm_num)) W_lineNA

theorem line_lineNB : line lineNB = nB := by
  unfold nB extWord
  exact slpG_shiftWord (by decide) (normWords_letters (by norm_num)) W_lineNB

theorem tAut_list_prod (l : List CFSG.Sporadic.Fi24.J) : tAut l.prod = (l.map fun x => tAut x).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil]; exact map_one tAut
  | cons x l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, map_mul tAut, ih]

theorem tAut_wordG (f : ℤ → CFSG.Sporadic.Fi24.J) (w : List ℤ) :
    tAut (wordG f w) = wordG (fun z => tAut (f z)) w := by
  unfold wordG
  rw [tAut_list_prod, List.map_map]
  rfl

theorem wordG_map (f : ℤ → CFSG.Sporadic.Fi24.J) (φ : ℤ → ℤ) (w : List ℤ) :
    wordG f (w.map φ) = wordG (fun z => f (φ z)) w := by
  unfold wordG
  rw [List.map_map]
  rfl

theorem tAut_line {g t : ℕ} (hg : g < W.size) (ht : twistOK W g t = true) :
    tAut (line g) = line t := by
  unfold twistOK at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ht
  obtain ⟨⟨hBt, hlet⟩, hwt⟩ := ht
  have hNA : lineNA = 13 := rfl
  have hNB : lineNB = 14 := rfl
  unfold line
  rw [slpG_eq genG W g, slpG_eq genG W t, hwt, tAut_wordG, wordG_map]
  unfold wordG
  refine congrArg List.prod (List.map_congr_left fun z hz => ?_)
  obtain ⟨h3, h15⟩ := hlet z hz
  have hzg : z.natAbs - 3 < g := by
    rcases (W_letter g hg z hz).2 with h | h <;> omega
  rw [letter_eq h3 hzg]
  rcases (by omega : z.natAbs = 3 ∨ z.natAbs = 4 ∨ 5 ≤ z.natAbs) with h | h | h
  ·
    rcases lt_or_gt_of_ne (show z ≠ 0 by omega) with hz0 | hz0
    · have htw : twistZ z = -16 := by
        unfold twistZ; rw [if_pos h, if_neg (by omega), hNA]; rfl
      rw [htw, letter_eq (by decide) (by omega), if_neg (show ¬ (0 < z) by omega),
        if_neg (show ¬ ((0 : ℤ) < -16) by decide), show z.natAbs - 3 = 0 by omega,
        show (-16 : ℤ).natAbs - 3 = lineNA from rfl,
        map_inv tAut, line_zero, tAut_a, line_lineNA]
    · have htw : twistZ z = 16 := by
        unfold twistZ; rw [if_pos h, if_pos hz0, hNA]; rfl
      rw [htw, letter_eq (by decide) (by omega), if_pos hz0,
        if_pos (show (0 : ℤ) < 16 by decide), show z.natAbs - 3 = 0 by omega,
        show (16 : ℤ).natAbs - 3 = lineNA from rfl,
        line_zero, tAut_a, line_lineNA]
  ·
    rcases lt_or_gt_of_ne (show z ≠ 0 by omega) with hz0 | hz0
    · have htw : twistZ z = -17 := by
        unfold twistZ; rw [if_neg (by omega), if_pos h, if_neg (by omega), hNB]; rfl
      rw [htw, letter_eq (by decide) (by omega), if_neg (show ¬ (0 < z) by omega),
        if_neg (show ¬ ((0 : ℤ) < -17) by decide), show z.natAbs - 3 = 1 by omega,
        show (-17 : ℤ).natAbs - 3 = lineNB from rfl,
        map_inv tAut, line_one, tAut_b, line_lineNB]
    · have htw : twistZ z = 17 := by
        unfold twistZ; rw [if_neg (by omega), if_pos h, if_pos hz0, hNB]; rfl
      rw [htw, letter_eq (by decide) (by omega), if_pos hz0,
        if_pos (show (0 : ℤ) < 17 by decide), show z.natAbs - 3 = 1 by omega,
        show (17 : ℤ).natAbs - 3 = lineNB from rfl,
        line_one, tAut_b, line_lineNB]
  ·
    have htw : twistZ z = z := by
      unfold twistZ; rw [if_neg (by omega), if_neg (by omega)]
    rw [htw, letter_eq h3 (by omega)]
    have hfix : tAut (line (z.natAbs - 3)) = line (z.natAbs - 3) := by
      rw [line_eq_gs (j := z.natAbs - 3) (by omega)]
      exact tAut_of_mem_stabilizer (gs_mem_stabilizer (by omega) (by omega))
    split_ifs
    · exact hfix
    · rw [map_inv tAut, hfix]

theorem clvl_zero_le {D E : ChainData} (hE0 : E.starts[0]! = 0)
    (h : ∀ j < D.starts[1]!, ∃ k < E.starts[1]!, D.sel[j]! = E.sel[k]!) :
    clvl D 0 ≤ clvl E 0 := by
  refine lvlGroup_le (cgs D) _ fun j _ hj2 => ?_
  rw [zero_add] at hj2
  obtain ⟨k, hk, he⟩ := h j hj2
  have e : cgs D j = cgs E k := by unfold cgs; rw [he]
  rw [e]
  exact gs_mem_lvlGroup (cgs E) (by rw [hE0]; omega) (by rw [zero_add]; exact hk)

noncomputable abbrev T0 : Subgroup CFSG.Sporadic.Fi24.J := clvl chainT 0

noncomputable abbrev A0 : Subgroup CFSG.Sporadic.Fi24.J := clvl chainA 0

noncomputable abbrev B0 : Subgroup CFSG.Sporadic.Fi24.J := clvl chainB 0

theorem card_T0 : Nat.card T0 = 2 ^ 21 := Certificates.certificate1208101.card_T
theorem card_A0 : Nat.card A0 = 2 ^ 21 * 27 := Certificates.certificate1208101.card_A
theorem card_B0 : Nat.card B0 = 2 ^ 21 * 9 := Certificates.certificate1208101.card_B

theorem T0_le_A0 : T0 ≤ A0 := clvl_zero_le (by decide) (by decide)
theorem T0_le_B0 : T0 ≤ B0 := clvl_zero_le (by decide) (by decide)

theorem sup_A0_B0 : A0 ⊔ B0 = ⊤ := Certificates.certificate1208101.sup

theorem isSylowIn_T0 : IsSylowIn 2 T0 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card card_T0, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := T0.index_mul_card
  rw [card_T0, card_J] at h
  omega

theorem A0_ne_top : A0 ≠ ⊤ := by
  intro h
  have := card_A0
  rw [h, Subgroup.card_top, card_J] at this
  omega

theorem B0_ne_top : B0 ≠ ⊤ := by
  intro h
  have := card_B0
  rw [h, Subgroup.card_top, card_J] at this
  omega

noncomputable abbrev ιJ : CFSG.Sporadic.Fi24.J →* R := Subgroup.inclusion J_le_R

theorem ιJ_injective : Function.Injective ιJ := Subgroup.inclusion_injective J_le_R

noncomputable abbrev up (X : Subgroup CFSG.Sporadic.Fi24.J) : Subgroup R := X.map ιJ ⊔ Subgroup.zpowers tR

theorem tR_mul_tR : tR * tR = 1 := Subtype.ext tT_mul_tT

theorem tR_not_mem (X : Subgroup CFSG.Sporadic.Fi24.J) : tR ∉ X.map ιJ := by
  rintro ⟨x, -, hx⟩
  apply tT_not_mem
  have e : ((ιJ x : R) : GL (Fin 781) (ZMod 3)) = (x : GL (Fin 781) (ZMod 3)) := rfl
  rw [← show ((tR : R) : GL (Fin 781) (ZMod 3)) = tT from rfl, ← hx, e]
  exact x.2

theorem conj_tR_eq (x : CFSG.Sporadic.Fi24.J) : tR * ιJ x * tR⁻¹ = ιJ (tAut x) := by
  refine Subtype.ext ?_
  change tT * (x : GL (Fin 781) (ZMod 3)) * tT⁻¹ = ((tAut x : CFSG.Sporadic.Fi24.J) : GL (Fin 781) (ZMod 3))
  rw [coe_tAut, tT_inv]

theorem conj_tR_clvl {D : ChainData} (hsel : ∀ k < D.sel.size, D.sel[k]! < W.size)
    (hst1 : D.starts[1]! = 2 * D.ntw)
    (htw : ∀ k < D.ntw, twistOK W D.sel[k]! D.sel[k + D.ntw]! = true) (hD0 : D.starts[0]! = 0)
    (hsz : 2 * D.ntw ≤ D.sel.size) :
    ∀ y ∈ (clvl D 0).map ιJ, tR * y * tR⁻¹ ∈ (clvl D 0).map ιJ := by
  have hpair : ∀ k < D.ntw, tAut (cgs D k) = cgs D (k + D.ntw) := fun k hk =>
    tAut_line (hsel _ (by omega)) (htw k hk)
  have hmem : ∀ k < 2 * D.ntw, cgs D k ∈ clvl D 0 := fun k hk =>
    gs_mem_lvlGroup (cgs D) (by rw [hD0]; omega) (by rw [zero_add, hst1]; exact hk)
  have hgen : ∀ k < 2 * D.ntw, tAut (cgs D k) ∈ clvl D 0 := by
    intro k hk
    by_cases hkn : k < D.ntw
    · rw [hpair k hkn]
      exact hmem _ (by omega)
    · have e : k = (k - D.ntw) + D.ntw := by omega
      rw [e, ← hpair _ (by omega), tAut_tAut]
      exact hmem _ (by omega)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ lettersGroup (levelLv D.starts 0) (pairG (cgs D)) := hx
  clear hx
  unfold lettersGroup at hx'
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rw [mem_levelLv (by rw [hD0]; exact Nat.zero_le _), hD0, hst1] at hl
    rw [conj_tR_eq]
    refine Subgroup.mem_map_of_mem ιJ ?_
    unfold pairG
    split_ifs
    · exact hgen _ (by omega)
    · rw [map_inv tAut]
      exact (clvl D 0).inv_mem (hgen _ (by omega))
  | one =>
    rw [map_one ιJ, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have e : tR * ιJ (a * b) * tR⁻¹ = (tR * ιJ a * tR⁻¹) * (tR * ιJ b * tR⁻¹) := by
      rw [map_mul ιJ]; group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : tR * ιJ a⁻¹ * tR⁻¹ = (tR * ιJ a * tR⁻¹)⁻¹ := by
      rw [map_inv ιJ]; group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem card_map_ιJ (X : Subgroup CFSG.Sporadic.Fi24.J) : Nat.card (X.map ιJ) = Nat.card X := by
  rw [← Nat.card_congr (X.equivMapOfInjective ιJ ιJ_injective).toEquiv]

theorem card_up {X : Subgroup CFSG.Sporadic.Fi24.J} (hX : ∀ y ∈ X.map ιJ, tR * y * tR⁻¹ ∈ X.map ιJ) :
    Nat.card (up X) = 2 * Nat.card X := by
  have h1 : Nat.card ↥(X.map ιJ ⊔ Subgroup.zpowers tR) = 2 * Nat.card ↥(X.map ιJ) :=
    card_sup_zpowers_eq_two_mul tR_mul_tR (tR_not_mem X) hX
  rw [card_map_ιJ] at h1
  exact h1

theorem up_sup_eq_top {A B : Subgroup CFSG.Sporadic.Fi24.J} (h : A ⊔ B = ⊤) : up A ⊔ up B = ⊤ := by
  refine eq_top_of_index_eq_two index_JR ?_ (t := tR)
    (mem_sup_left (mem_sup_right (mem_zpowers tR))) (by rw [mem_JR_iff]; exact tT_not_mem)
  intro y hy
  rw [mem_JR_iff] at hy
  have hmem : (⟨y, hy⟩ : CFSG.Sporadic.Fi24.J) ∈ A ⊔ B := by rw [h]; trivial
  have hy' : ιJ ⟨y, hy⟩ = y := rfl
  have := Subgroup.mem_map_of_mem ιJ hmem
  rw [Subgroup.map_sup, hy'] at this
  exact (sup_le_sup le_sup_left le_sup_left : A.map ιJ ⊔ B.map ιJ ≤ up A ⊔ up B) this

theorem card_upT : Nat.card (up T0) = 2 ^ 22 := by
  rw [card_up (conj_tR_clvl selT (by decide) twT (by decide) (by decide)), card_T0]
  norm_num

theorem card_upA : Nat.card (up A0) = 2 ^ 22 * 27 := by
  rw [card_up (conj_tR_clvl selA (by decide) twA (by decide) (by decide)), card_A0]
  norm_num

theorem card_upB : Nat.card (up B0) = 2 ^ 22 * 9 := by
  rw [card_up (conj_tR_clvl selB (by decide) twB (by decide) (by decide)), card_B0]
  norm_num

theorem isSylowIn_upT : IsSylowIn 2 (up T0) ⊤ := by
  refine ⟨le_top, IsPGroup.of_card card_upT, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := (up T0).index_mul_card
  rw [card_upT, card_R] at h
  omega

theorem isLPair_J : IsLPair IsCalL0 T0 A0 B0 where
  le_left := T0_le_A0
  le_right := T0_le_B0
  ne_top_left := A0_ne_top
  ne_top_right := B0_ne_top
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 21) (N := 2 ^ 21 * 27)
    (by decide +kernel) (by rw [card_A0])
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 21) (N := 2 ^ 21 * 27)
    (by decide +kernel) (by rw [card_B0]; exact Dvd.intro 3 (by norm_num))
  sup_eq_top := sup_A0_B0

theorem isLPair_R : IsLPair IsCalL0 (up T0) (up A0) (up B0) where
  le_left := sup_le_sup_right (Subgroup.map_mono T0_le_A0) _
  le_right := sup_le_sup_right (Subgroup.map_mono T0_le_B0) _
  ne_top_left := by
    intro h
    have := card_upA
    rw [h, Subgroup.card_top, card_R] at this
    omega
  ne_top_right := by
    intro h
    have := card_upB
    rw [h, Subgroup.card_top, card_R] at this
    omega
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 22) (N := 2 ^ 22 * 27)
    (by decide +kernel) (by rw [card_upA])
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 22) (N := 2 ^ 22 * 27)
    (by decide +kernel) (by rw [card_upB]; exact Dvd.intro 3 (by norm_num))
  sup_eq_top := up_sup_eq_top sup_A0_B0


abbrev GrpEquiv (G H : Type*) [Group G] [Group H] : Type _ := G ≃* H

noncomputable def fi24GrpEquivJ : GrpEquiv Blueprint.NativeSporadic.Fi24prime CFSG.Sporadic.Fi24.J := fi24EquivJ

theorem nonempty_mulEquiv_J (X : Type) [Group X]
    (hX : CFSG.Models.IsSporadic X .Fi24Prime) : Nonempty (GrpEquiv X CFSG.Sporadic.Fi24.J) := by
  let : Mul TauCeti.SporadicName.Fi24Prime.Group := Monoid.toMul
  obtain ⟨e₁⟩ := hX
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact ⟨(e₁.trans e₂.symm).trans fi24GrpEquivJ⟩


theorem card_outer_J : Nat.card (Outer CFSG.Sporadic.Fi24.J) = 2 := by
  rw [← CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime]
  exact Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence fi24GrpEquivJ).toEquiv.symm

noncomputable def autGrpEquivR : GrpEquiv (MulAut Blueprint.NativeSporadic.Fi24prime) R :=
  CFSG.Sporadic.Schreier.Fi24.autEquivR

noncomputable def autJEquivR : GrpEquiv (MulAut CFSG.Sporadic.Fi24.J) R :=
  (MulAut.congr fi24GrpEquivJ).symm.trans autGrpEquivR

end SporFi24

open SporFi24 CFSG.Sporadic.Fi24 in
theorem asch54SporGenAt_fi24Prime :
    Asch54SporGenAt .Fi24Prime :=
  asch54SporGenAt_of_isLPair_of_card_outer_eq_two (C := CFSG.Sporadic.Fi24.J) (D := R) nonempty_mulEquiv_J
    card_outer_J autJEquivR isSylowIn_T0 isLPair_J isSylowIn_upT isLPair_R

end CFSG.LocalAnalysis.WeakClosure81

end
