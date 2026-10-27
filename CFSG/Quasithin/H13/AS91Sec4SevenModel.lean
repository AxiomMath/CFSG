module

public import CFSG.Quasithin.H13.AS91Sec4SixModel
public import Certificates.Certificate89407

public section

namespace CFSG.Quasithin.H13.AS91.Two

open Subgroup CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem baseOK47_spec :
    (∀ p ∈ p2Rows, (Std.HashSet.ofList (enumGrp pRows)).contains p = true) ∧
      gensOKb iRows = true ∧ idR ∈ enumGrp iRows ∧ closedCheck iRows (enumGrp iRows) = true ∧
      (enumGrp iRows).dedup.length = 4 ∧ (∀ r ∈ iRows, r ∈ enumGrp ebRows ∧ r ∈ enumGrp p2Rows) ∧
      ∀ x ∈ enumGrp ebRows, x ∈ enumGrp p2Rows → x ∈ enumGrp iRows := by
  have h := Certificates.certificate89407
  simp only [ok47, Bool.and_eq_true] at h
  have h1 := h.1.1
  simp only [baseOK47, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩ := h1
  refine ⟨g1, g2, g3, g4, g5, g6, fun x hx hxP => ?_⟩
  rcases g7 x hx with h' | h'
  · exact absurd (List.contains_iff_mem.mpr hxP) (by rw [h']; exact Bool.false_ne_true)
  · exact h'

theorem fOK47_spec (i : Fin 3) :
    gensOKb (fRows i) = true ∧ idR ∈ enumGrp (fRows i) ∧
      closedCheck (fRows i) (enumGrp (fRows i)) = true ∧ (enumGrp (fRows i)).dedup.length = 8 ∧
      (∀ r ∈ fRows i, r ∈ enumGrp ebRows) ∧
      ∀ j : Fin 3, i ≠ j → fGen.getD i idR ∉ enumGrp (fRows j) := by
  have h := Certificates.certificate89407
  simp only [ok47, Bool.and_eq_true] at h
  have h2 := h.1.2
  simp only [fOK47, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true', List.mem_range] at h2
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := h2 i i.2
  refine ⟨g1, g2, g3, g4, g5, fun j hij hmem => ?_⟩
  rcases g6 j j.2 with h' | h'
  · exact hij (Fin.ext h')
  · exact absurd (List.contains_iff_mem.mpr hmem) (by rw [h']; exact Bool.false_ne_true)

theorem gOK47_spec : ∀ x ∈ g1List (),
    (∀ F ∈ fLists (), ∃ F' ∈ fLists (), ∀ f ∈ F, ∃ f' ∈ F', mulR x f = mulR f' x) ∧
      ((∀ F ∈ fLists (), ∀ f ∈ F, ∃ f' ∈ F, mulR x f = mulR f' x) →
        ∃ e ∈ enumGrp ebRows, ∃ p ∈ enumGrp p2Rows, mulR p e = x) := by
  have h := Certificates.certificate89407
  simp only [ok47, Bool.and_eq_true] at h
  have h3 := h.2
  simp only [gOK47, conjInto, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h3
  intro x hx
  obtain ⟨ha, hb⟩ := h3 x hx
  refine ⟨ha, fun hF => ?_⟩
  rcases hb with h' | h'
  · exfalso
    revert h'
    rw [imp_false, Bool.not_eq_false, List.all_eq_true]
    intro F hFm
    rw [List.all_eq_true]
    intro f hf
    rw [List.any_eq_true]
    obtain ⟨f', hf', he⟩ := hF F hFm f hf
    exact ⟨f', hf', beq_iff_eq.mpr he⟩
  · exact h'

theorem mem_g1List {x : Array ℕ} :
    x ∈ g1List () ↔ x ∈ enumGrp gZRows ∧ ∀ c ∈ w1List, appN x c ∈ w1List := by
  simp only [g1List, List.mem_filter, List.all_eq_true, List.contains_iff_mem]

theorem mem_fLists {F : List (Array ℕ)} : F ∈ fLists () ↔ ∃ i : Fin 3, enumGrp (fRows i) = F := by
  simp only [fLists, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem mem_W1_of_inZ {v : V12} (hv : InZ v) : v ∈ W1 := by
  have h : zList.contains (codeOf v) = true := hv
  have hz : ∀ c ∈ zList, c ∈ w1List := by decide
  exact mem_W1_iff.mpr (hz _ (List.contains_iff_mem.mp h))

theorem w1Mask_mem_w5 : w1Mask () ∈ w5 () := by
  refine mem_w5.mpr ⟨w1Mask_mem_w1Orbit, ?_, ?_, ?_⟩ <;> rw [w1Mask, testBit_maskOf] <;> decide

theorem p2Grp_le_pGrp :
    p2Grp ≤ pGrp :=
  genGrp_le_of_rep fun p hp => rep_of_contains gensOK_pRows (baseOK47_spec.1 p hp)

abbrev iGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp iRows

theorem gensOK_i : GensOK iRows :=
  gensOK_of_gensOKb baseOK47_spec.2.1

theorem card_iGrp : Nat.card iGrp = 4 := by
  obtain ⟨-, -, hid, hc, hn, -⟩ := baseOK47_spec
  rw [card_genGrp (enumGrp_sound gensOK_i) hid hc, hn]

theorem iGrp_le_eb :
    iGrp ≤ ebGrp :=
  genGrp_le_of_rep fun r hr => enumGrp_sound gensOK_eb r (baseOK47_spec.2.2.2.2.2.1 r hr).1

theorem iGrp_le_p2 :
    iGrp ≤ p2Grp :=
  genGrp_le_of_rep fun r hr => enumGrp_sound gensOK_p2 r (baseOK47_spec.2.2.2.2.2.1 r hr).2

theorem eb_inf_p2 :
    ebGrp ⊓ p2Grp = iGrp := by
  refine le_antisymm (fun U hU => ?_) (le_inf iGrp_le_eb iGrp_le_p2)
  obtain ⟨-, -, -, -, hid, hc, -⟩ := ebOK46_spec
  obtain ⟨r, hr, hUr⟩ := complete hid hc U hU.1
  obtain ⟨-, -, -, -, -, -, -, hid2, hc2, -⟩ := zGrpOK44_spec
  obtain ⟨r', hr', hUr'⟩ := complete hid2 hc2 U hU.2
  have e : r = r' := (rowsOf_eq (enumGrp_sound gensOK_eb r hr).1 hUr).symm.trans
    (rowsOf_eq (enumGrp_sound gensOK_p2 r' hr').1 hUr')
  rw [← e] at hr'
  obtain ⟨-, V, hV, hVr⟩ := enumGrp_sound gensOK_i r (baseOK47_spec.2.2.2.2.2.2 r hr hr')
  rw [show U = V from LinearEquiv.ext fun v => (hUr v).trans (hVr v).symm]
  exact hV

theorem rep_gen {gs : List (Array ℕ)} (hgs : GensOK gs) {r : Array ℕ} (hr : r ∈ gs) :
    Rep (genGrp gs) r :=
  ⟨(hgs r hr).1, _, gen_mem hgs hr, fun _ => rfl⟩

abbrev fGrp (i : Fin 3) : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp (fRows i)

theorem gensOK_f (i : Fin 3) : GensOK (fRows i) :=
  gensOK_of_gensOKb (fOK47_spec i).1

theorem card_fGrp (i : Fin 3) : Nat.card (fGrp i) = 8 := by
  obtain ⟨-, hid, hc, hn, -⟩ := fOK47_spec i
  rw [card_genGrp (enumGrp_sound (gensOK_f i)) hid hc, hn]

theorem fGrp_le_eb (i : Fin 3) :
    fGrp i ≤ ebGrp :=
  genGrp_le_of_rep fun r hr => enumGrp_sound gensOK_eb r ((fOK47_spec i).2.2.2.2.1 r hr)

theorem iGrp_le_fGrp (i : Fin 3) : iGrp ≤ fGrp i :=
  genGrp_le_of_rep fun r hr => rep_gen (gensOK_f i) (by simp [fRows, hr])

theorem fGen_mem_fRows (i : Fin 3) : fGen.getD i idR ∈ fRows i := by
  simp [fRows]

@[expose] noncomputable def fElt (i : Fin 3) :
    V12 ≃ₗ[ZMod 2] V12 :=
  eqvOf (fGen.getD i idR) (invR (fGen.getD i idR)) (gensOK_f i _ (fGen_mem_fRows i)).2.2.1
    (gensOK_f i _ (fGen_mem_fRows i)).2.2.2

theorem fElt_mem (i : Fin 3) : fElt i ∈ fGrp i :=
  gen_mem (gensOK_f i) (fGen_mem_fRows i)

theorem fElt_not_mem {i j : Fin 3} (hij : i ≠ j) :
    fElt i ∉ fGrp j := by
  intro hmem
  obtain ⟨-, hid, hc, -⟩ := fOK47_spec j
  obtain ⟨r, hr, hUr⟩ := complete hid hc _ hmem
  have hok := (gensOK_f i _ (fGen_mem_fRows i)).1
  have hok' := (enumGrp_sound (gensOK_f j) r hr).1
  have e : fGen.getD i idR = r := rows_eq (okRows_spec hok).1 (okRows_spec hok').1
    (okRows_spec hok).2 (okRows_spec hok').2 fun v => hUr v
  exact (fOK47_spec i).2.2.2.2.2 j hij (e ▸ hr)

theorem conj_fGrp
    {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ gZGrp) (hW : ⇑U '' W1 = W1) :
    (∀ i : Fin 3, ∃ j : Fin 3, ∀ f ∈ fGrp i, U * f * U⁻¹ ∈ fGrp j) ∧
      ((∀ i : Fin 3, ∀ f ∈ fGrp i, U * f * U⁻¹ ∈ fGrp i) →
        ∃ p ∈ p2Grp, ∃ e ∈ ebGrp, U = p * e) := by
  obtain ⟨-, -, -, -, hid, hc, -⟩ := zGrpOK44_spec
  obtain ⟨x, hxX, hUx⟩ := complete hid hc U hU
  have hxok := (enumGrp_sound gensOK_gZ x hxX).1
  have hx1 : x ∈ g1List () := by
    refine mem_g1List.mpr ⟨hxX, fun c hc' => ?_⟩
    have hcW : vecOf c ∈ W1 := (vecOf_mem_W1 (w1List_lt c hc')).mpr hc'
    have h1 : U (vecOf c) ∈ W1 := by
      rw [← hW]
      exact Set.mem_image_of_mem _ hcW
    rw [hUx, ← vecOf_appN, vecOf_mem_W1 (appN_lt (okRows_spec hxok).2 _)] at h1
    exact h1
  obtain ⟨ha, hb⟩ := gOK47_spec x hx1
  have key : ∀ {i j : Fin 3},
      (∀ f ∈ enumGrp (fRows i), ∃ f' ∈ enumGrp (fRows j), mulR x f = mulR f' x) →
        ∀ f ∈ fGrp i, U * f * U⁻¹ ∈ fGrp j := by
    intro i j hij f hf
    obtain ⟨-, hid', hc', -⟩ := fOK47_spec i
    obtain ⟨r, hr, hfr⟩ := complete hid' hc' f hf
    obtain ⟨r', hr', he⟩ := hij r hr
    obtain ⟨-, V, hV, hVr⟩ := enumGrp_sound (gensOK_f j) r' hr'
    have hUf : U * f = V * U := LinearEquiv.ext fun v => by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfr, hUx, hUx, hVr, ← linOfRows_mulR, he,
        linOfRows_mulR]
    rw [hUf, mul_inv_cancel_right]
    exact hV
  refine ⟨fun i => ?_, fun hn => ?_⟩
  · obtain ⟨F', hF', hFF'⟩ := ha _ (mem_fLists.mpr ⟨i, rfl⟩)
    obtain ⟨j, rfl⟩ := mem_fLists.mp hF'
    exact ⟨j, key hFF'⟩
  · have hc'' : ∀ F ∈ fLists (), ∀ f ∈ F, ∃ f' ∈ F, mulR x f = mulR f' x := by
      intro F hF f hf
      obtain ⟨i, rfl⟩ := mem_fLists.mp hF
      obtain ⟨hfok, W', hW', hW'f⟩ := enumGrp_sound (gensOK_f i) f hf
      obtain ⟨-, hid', hc', -⟩ := fOK47_spec i
      obtain ⟨f', hf', hf'e⟩ := complete hid' hc' _ (hn i W' hW')
      have hf'ok := (enumGrp_sound (gensOK_f i) f' hf').1
      refine ⟨f', hf', rows_eq (by rw [size_mulR]; exact (okRows_spec hfok).1)
        (by rw [size_mulR]; exact (okRows_spec hxok).1) (lt_of_mem_mulR (okRows_spec hxok).2)
        (lt_of_mem_mulR (okRows_spec hf'ok).2) fun v => ?_⟩
      have hcv : (U * W' * U⁻¹) (U v) = U (W' v) := by
        rw [← LinearEquiv.mul_apply, inv_mul_cancel_right, LinearEquiv.mul_apply]
      rw [linOfRows_mulR, linOfRows_mulR, ← hW'f, ← hUx, ← hUx, ← hf'e, hcv]
    obtain ⟨e, he, p, hp, hpe⟩ := hb hc''
    obtain ⟨-, E', hE', hE'e⟩ := enumGrp_sound gensOK_eb e he
    obtain ⟨-, P', hP', hP'p⟩ := enumGrp_sound gensOK_p2 p hp
    refine ⟨P', hP', E', hE', LinearEquiv.ext fun v => ?_⟩
    rw [hUx, ← hpe, linOfRows_mulR, LinearEquiv.mul_apply, hP'p, hE'e]

end CFSG.Quasithin.H13.AS91.Two
