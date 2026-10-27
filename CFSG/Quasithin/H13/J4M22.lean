module

public import CFSG.Quasithin.H13.J4Normal3
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Mathieu.M22
public meta import Certificates.Data.CFSGNative.H13.J4Local
public meta import CFSG.Quasithin.H13.J4QuotGroup
import Certificates.Data.CFSGNative.H13.J4Local
public import Certificates.Certificate7012
public import Certificates.Certificate7013
public import Certificates.Certificate7014
public import Certificates.Certificate7015
public import Certificates.Certificate7016
public import Certificates.Certificate7018
public import CFSG.Quasithin.H13.J4M22Inputs
public import Certificates.Certificate7027
public import Certificates.Certificate3029

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Quasithin.H13.J4.Native TauCeti

theorem xq_mem_CQ :
    xq ∈ CQ := mem_CQ_iff.2 localChecks_spec.2.2.2.2.1

theorem yq_mem_CQ :
    yq ∈ CQ := mem_CQ_iff.2 localChecks_spec.2.2.2.2.2.1

abbrev ZC :
    Subgroup CQ := Zq.subgroupOf CQ

@[expose] def xC :
    CQ := ⟨xq, xq_mem_CQ⟩

@[expose] def yC :
    CQ := ⟨yq, yq_mem_CQ⟩

theorem card_CQ :
    Nat.card CQ = 1330560 := by
  have h := Subgroup.card_mul_index CQ
  rw [index_CQ, card_QW] at h
  omega

theorem card_ZC :
    Nat.card ZC = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Zq_le_CQ).toEquiv, card_Zq]

theorem card_CmodZ :
    Nat.card (CQ ⧸ ZC) = 443520 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ZC
  rw [card_CQ, card_ZC] at h
  omega

theorem mem_ZC_iff
    {c : CQ} :
    c ∈ ZC ↔ (c : QW) ∈ Zq := Subgroup.mem_subgroupOf

theorem mem_Zq_iff
    {g : QW} :
    g ∈ Zq ↔ g = 1 ∨ g = zq ∨ g = zq * zq := by
  classical
  have hfin : IsOfFinOrder zq := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, zq_pow_three⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, orderOf_zq, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_range] at ha
    interval_cases a
    · left; exact pow_zero _
    · right; left; exact pow_one _
    · right; right; exact sq _
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp, pow_zero _⟩
    · exact ⟨1, by simp, pow_one _⟩
    · exact ⟨2, by simp, sq _⟩

theorem xq_not_mem_Zq :
    xq ∉ Zq := by
  intro h
  have hx2 := localChecks_spec.2.2.2.2.2.2.1
  rcases mem_Zq_iff.1 h with h | h | h
  · exact localChecks_spec.2.2.2.2.2.2.2.2.2 h
  · apply zq_ne_one
    have h2 : zq ^ 2 = 1 := by rw [← h, hx2]
    calc zq = zq ^ 3 * (zq ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, zq_pow_three]; group
  · apply zq_ne_one
    have h4 : zq ^ 4 = 1 := by rw [show zq ^ 4 = (zq * zq) ^ 2 by rw [← sq, ← pow_mul], ← h, hx2]
    calc zq = zq ^ 4 * (zq ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, zq_pow_three]; group

theorem m22Rels_eq : Sporadic.m22Presentation.relatorLetters = m22Rels :=
  Sporadic.m22Presentation_relatorLetters

theorem genW_eq (i : ℕ) (hi : i < 2) :
    CFSG.Sporadic.Bridge.M22.genWord i = genW.getD i [] := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

theorem m22Checks_eq : m22Checks = true :=
  Certificates.certificate7027

@[expose] def xyQ
    (i : ℕ) :
    QW := if i = 0 then xq else if i = 1 then yq else 1

@[expose] def abQ
    (i : ℕ) :
    QW :=
  if i = 0 then CFSG.Sporadic.Bridge.wordProd xyQ alphaW
  else if i = 1 then CFSG.Sporadic.Bridge.wordProd xyQ betaW else 1

theorem PrRep12.bword {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12}
    (h : ∀ i, PrRep12 (gs i) (xs[i]?.getD pr12One)) (w : List (ℕ × Bool)) :
    PrRep12 (CFSG.Sporadic.Bridge.wordProd gs w) (pr12BWord xs w) := by
  unfold CFSG.Sporadic.Bridge.wordProd pr12BWord
  suffices ∀ (acc : Pr12) (g : GL (Fin 12) (ZMod 2)), PrRep12 g acc →
      PrRep12 (g * (w.map fun l => if l.2 then gs l.1 else (gs l.1)⁻¹).prod)
        (w.foldl (fun acc l => pr12Mul acc
          (if l.2 then xs[l.1]?.getD pr12One else pr12Inv (xs[l.1]?.getD pr12One))) acc) by
    simpa using this pr12One 1 PrRep12.one
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ih _ _ (hg.mul ?_)
    split_ifs
    · exact h _
    · exact (h _).inv

theorem eq_mod_Zq_of
    {g h : QW} {X Y : Array ℕ} {zP : Pr12}
    (hz : CFSG.Sporadic.SmallF2.rowsMatrix 12 zP.1 = ((qHom zq : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (hg : CFSG.Sporadic.SmallF2.rowsMatrix 12 X = ((qHom g : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (hh : CFSG.Sporadic.SmallF2.rowsMatrix 12 Y = ((qHom h : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (e : eqModZ zP X Y = true) : h⁻¹ * g ∈ Zq := by
  simp only [eqModZ, Bool.or_eq_true, beq_iff_eq] at e
  rcases e with (e | e) | e
  · have : g = h := qHom_injective (Units.ext (by rw [← hg, ← hh, e]))
    rw [this, inv_mul_cancel]
    exact Zq.one_mem
  · have : g = h * zq := qHom_injective (Units.ext (by
      rw [← hg, e, CFSG.Sporadic.SmallF2.rowsMatrix_mulRows, hh, hz, map_mul, Units.val_mul]))
    rw [this, inv_mul_cancel_left]
    exact Subgroup.mem_zpowers zq
  · have : g = h * zq * zq := qHom_injective (Units.ext (by
      rw [← hg, e, CFSG.Sporadic.SmallF2.rowsMatrix_mulRows,
        CFSG.Sporadic.SmallF2.rowsMatrix_mulRows, hh, hz, map_mul, map_mul, Units.val_mul,
        Units.val_mul]))
    rw [this, mul_assoc, inv_mul_cancel_left]
    exact Zq.mul_mem (Subgroup.mem_zpowers zq) (Subgroup.mem_zpowers zq)

theorem prRep12_xyQ
    (i : ℕ) :
    PrRep12 (qHom (xyQ i)) ((#[xPair, yPair] : Array Pr12)[i]?.getD pr12One) := by
  rcases i with _ | _ | i
  · exact prRep12_xq
  · exact prRep12_yq
  · have : xyQ (i + 2) = 1 := by unfold xyQ; simp
    rw [this, map_one]
    exact PrRep12.one

theorem prRep12_abQ
    (i : ℕ) :
    PrRep12 (qHom (abQ i)) ((#[aPair, bPair] : Array Pr12)[i]?.getD pr12One) := by
  rcases i with _ | _ | i
  · show PrRep12 (qHom (CFSG.Sporadic.Bridge.wordProd xyQ alphaW)) aPair
    rw [CFSG.Sporadic.Bridge.map_wordProd]
    exact PrRep12.bword prRep12_xyQ _
  · show PrRep12 (qHom (CFSG.Sporadic.Bridge.wordProd xyQ betaW)) bPair
    rw [CFSG.Sporadic.Bridge.map_wordProd]
    exact PrRep12.bword prRep12_xyQ _
  · have : abQ (i + 2) = 1 := by unfold abQ; simp
    rw [this, map_one]
    exact PrRep12.one

theorem prRep12_abWord
    (w : List (ℕ × Bool)) :
    PrRep12 (qHom (CFSG.Sporadic.Bridge.wordProd abQ w)) (pr12BWord #[aPair, bPair] w) := by
  rw [CFSG.Sporadic.Bridge.map_wordProd]
  exact PrRep12.bword prRep12_abQ w

theorem m22Checks_spec :
    (∀ r ∈ m22Rels, CFSG.Sporadic.Bridge.wordProd abQ r ∈ Zq) ∧
      xq⁻¹ * CFSG.Sporadic.Bridge.wordProd abQ (genW.getD 0 []) ∈ Zq ∧
      yq⁻¹ * CFSG.Sporadic.Bridge.wordProd abQ (genW.getD 1 []) ∈ Zq := by
  have h := m22Checks_eq
  simp only [m22Checks, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have := eq_mod_Zq_of (h := 1) prRep12_zq.1 (prRep12_abWord r).1
      (by rw [map_one]; exact rowsMatrix12_idRows_eq) (h1 r hr)
    rwa [inv_one, one_mul] at this
  · exact eq_mod_Zq_of prRep12_zq.1 (prRep12_abWord _).1 prRep12_xq.1 h2
  · exact eq_mod_Zq_of prRep12_zq.1 (prRep12_abWord _).1 prRep12_yq.1 h3

theorem xyQ_mem_CQ
    (i : ℕ) :
    xyQ i ∈ CQ := by
  unfold xyQ
  split_ifs
  · exact xq_mem_CQ
  · exact yq_mem_CQ
  · exact CQ.one_mem

theorem abQ_mem_CQ
    (i : ℕ) :
    abQ i ∈ CQ := by
  unfold abQ
  split_ifs
  · exact CFSG.Sporadic.Bridge.wordProd_mem xyQ_mem_CQ _
  · exact CFSG.Sporadic.Bridge.wordProd_mem xyQ_mem_CQ _
  · exact CQ.one_mem

@[expose] def abBar
    (i : ℕ) :
    CQ ⧸ ZC := QuotientGroup.mk ⟨abQ i, abQ_mem_CQ i⟩

theorem abBar_wordProd
    (w : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd abBar w =
      QuotientGroup.mk ⟨CFSG.Sporadic.Bridge.wordProd abQ w,
        CFSG.Sporadic.Bridge.wordProd_mem abQ_mem_CQ w⟩ := by
  show CFSG.Sporadic.Bridge.wordProd (fun i => (QuotientGroup.mk' ZC) ⟨abQ i, abQ_mem_CQ i⟩) w = _
  rw [← CFSG.Sporadic.Bridge.map_wordProd, QuotientGroup.mk'_apply]
  congr 1
  apply Subtype.ext
  rw [CFSG.Sporadic.Bridge.coe_wordProd]

theorem mk_eq_one_of_mem
    {c : CQ} (h : (c : QW) ∈ Zq) :
    (QuotientGroup.mk c : CQ ⧸ ZC) = 1 :=
  (QuotientGroup.eq_one_iff c).2 (mem_ZC_iff.2 h)

theorem relators_abBar :
    ∀ v ∈ Sporadic.m22Presentation.relatorLetters,
    CFSG.Sporadic.Bridge.wordProd abBar v = 1 := by
  intro v hv
  rw [m22Rels_eq] at hv
  rw [abBar_wordProd]
  exact mk_eq_one_of_mem (m22Checks_spec.1 v hv)

@[expose] def presToC :
    Sporadic.m22Presentation.Group →* CQ ⧸ ZC :=
  CFSG.Sporadic.Bridge.presHom _ abBar relators_abBar

@[expose] def presToNative :
    Sporadic.m22Presentation.Group →* ↥CFSG.Blueprint.NativeSporadic.M22 :=
  CFSG.Sporadic.Bridge.presHom _ CFSG.Sporadic.Bridge.M22.img
    CFSG.Sporadic.Bridge.M22.relators_eval

theorem genWord_letters (i : ℕ) (hi : i < 2) :
    ∀ l ∈ CFSG.Sporadic.Bridge.M22.genWord i, l.1 < Sporadic.m22Presentation.generatorCount := by
  rw [CFSG.Sporadic.Bridge.M22.generatorCount_eq]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

theorem presToNative_genWord (i : ℕ) (hi : i < 2) :
    presToNative (CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.presGen _)
      (CFSG.Sporadic.Bridge.M22.genWord i)) =
      ⟨CFSG.Sporadic.Bridge.M22.gen i, CFSG.Sporadic.Bridge.M22.gen_mem i⟩ := by
  rw [presToNative, CFSG.Sporadic.Bridge.presHom_wordProd _ _ _ _ (genWord_letters i hi)]
  apply Subtype.ext
  rw [CFSG.Sporadic.Bridge.coe_wordProd]
  exact (CFSG.Sporadic.Bridge.M22.gen_eq_wordProd i (by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp)).symm

theorem presToNative_bijective :
    Function.Bijective presToNative := by
  have hsurj : Function.Surjective presToNative := by
    have hgen : ∀ i < 2, (⟨CFSG.Sporadic.Bridge.M22.gen i, CFSG.Sporadic.Bridge.M22.gen_mem i⟩ :
        ↥CFSG.Blueprint.NativeSporadic.M22) ∈ presToNative.range :=
      fun i hi => ⟨_, presToNative_genWord i hi⟩
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    rintro ⟨g, hg⟩ -
    suffices H : ∀ y (hy : y ∈ CFSG.Blueprint.NativeSporadic.M22),
        (⟨y, hy⟩ : ↥CFSG.Blueprint.NativeSporadic.M22) ∈ presToNative.range from H g hg
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact hgen 0 (by norm_num)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hgen 1 (by norm_num)
    | one => exact presToNative.range.one_mem
    | mul x y hx hy ihx ihy => exact presToNative.range.mul_mem ihx ihy
    | inv x hx ih => exact presToNative.range.inv_mem ih
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact hsurj.bijective_of_nat_card_le (by rw [CFSG.Sporadic.Mathieu.card_M22]; exact hcard)

@[expose] def presEquiv :
    Sporadic.m22Presentation.Group ≃* ↥CFSG.Blueprint.NativeSporadic.M22 :=
  MulEquiv.ofBijective presToNative presToNative_bijective

@[expose] def m22ToC :
    ↥CFSG.Blueprint.NativeSporadic.M22 →* CQ ⧸ ZC :=
  presToC.comp presEquiv.symm.toMonoidHom

theorem xyQ_zero' :
    xyQ 0 = xq := by simp only [xyQ, ↓reduceIte]

theorem xyQ_one' :
    xyQ 1 = yq := by simp only [xyQ, one_ne_zero, ↓reduceIte]

theorem m22ToC_gen
    (i : ℕ) (hi : i < 2) :
    m22ToC ⟨CFSG.Sporadic.Bridge.M22.gen i, CFSG.Sporadic.Bridge.M22.gen_mem i⟩ =
      QuotientGroup.mk ⟨xyQ i, xyQ_mem_CQ i⟩ := by
  have e : presEquiv.symm ⟨CFSG.Sporadic.Bridge.M22.gen i,
      CFSG.Sporadic.Bridge.M22.gen_mem i⟩ = CFSG.Sporadic.Bridge.wordProd
        (CFSG.Sporadic.Bridge.presGen _) (CFSG.Sporadic.Bridge.M22.genWord i) := by
    rw [MulEquiv.symm_apply_eq]
    exact (presToNative_genWord i hi).symm
  have e2 : m22ToC ⟨CFSG.Sporadic.Bridge.M22.gen i, CFSG.Sporadic.Bridge.M22.gen_mem i⟩ =
      presToC (presEquiv.symm ⟨CFSG.Sporadic.Bridge.M22.gen i,
        CFSG.Sporadic.Bridge.M22.gen_mem i⟩) := rfl
  rw [e2, e, presToC, CFSG.Sporadic.Bridge.presHom_wordProd _ _ _ _ (genWord_letters i hi),
    abBar_wordProd, QuotientGroup.eq, mem_ZC_iff, Subgroup.coe_mul, Subgroup.coe_inv,
    genW_eq i hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · show (CFSG.Sporadic.Bridge.wordProd abQ (genW.getD 0 []))⁻¹ * xyQ 0 ∈ Zq
    rw [xyQ_zero']
    simpa using Zq.inv_mem m22Checks_spec.2.1
  · show (CFSG.Sporadic.Bridge.wordProd abQ (genW.getD 1 []))⁻¹ * xyQ 1 ∈ Zq
    rw [xyQ_one']
    simpa using Zq.inv_mem m22Checks_spec.2.2

theorem m22ToC_injective :
    Function.Injective m22ToC := by
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hsimple.eq_bot_or_eq_top_of_normal m22ToC.ker with h | h
  · exact h
  · exfalso
    have hx : (⟨CFSG.Sporadic.Bridge.M22.gen 0, CFSG.Sporadic.Bridge.M22.gen_mem 0⟩ :
        ↥CFSG.Blueprint.NativeSporadic.M22) ∈ m22ToC.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, m22ToC_gen 0 (by norm_num), QuotientGroup.eq_one_iff,
      mem_ZC_iff] at hx
    exact xq_not_mem_Zq hx

theorem m22ToC_bijective :
    Function.Bijective m22ToC :=
  m22ToC_injective.bijective_of_nat_card_le (by rw [card_CmodZ, CFSG.Sporadic.Mathieu.card_M22])

@[expose] def m22EquivC :
    ↥CFSG.Blueprint.NativeSporadic.M22 ≃* CQ ⧸ ZC :=
  MulEquiv.ofBijective m22ToC m22ToC_bijective

end CFSG.Quasithin.H13.J4
