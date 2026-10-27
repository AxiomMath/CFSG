module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public meta import CFSG.RankThree.PartTwo.Toolkit.RawGL
public meta import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public meta import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStdInputs
public import Certificates.Certificate8172

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

noncomputable abbrev Lstd (i : Fin 3) : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
  Submodule.span (ZMod 3) {Pi.single i 1}

theorem translate_span_singleton (g : GL33) (v : Fin 3 → ZMod 3) :
    translate g (Submodule.span (ZMod 3) {v}) =
      Submodule.span (ZMod 3) {(g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v} := by
  rw [SubgroupLists.translate, Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply]

theorem single_ne_zero (j : Fin 3) : (Pi.single j 1 : Fin 3 → ZMod 3) ≠ 0 := by
  intro h
  have := congrFun h j
  simp at this

theorem gl_mulVec_ne_zero (g : GL33) {v : Fin 3 → ZMod 3} (hv : v ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← gl_inv_mulVec_mulVec g v, h, Matrix.mulVec_zero]

theorem translate_Lstd_eq_iff (g : GL33) (i j : Fin 3) :
    translate g (Lstd i) = Lstd j ↔
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 ∈ Lstd j := by
  rw [translate_span_singleton]
  constructor
  · intro h
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact gl_mulVec_ne_zero g (single_ne_zero i) ha.symm
    rw [← ha, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha0)]

theorem ofVec_mulVec_single (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (i : Fin 3) :
    ofVec (M *ᵥ Pi.single i 1) = colV (ofMat M) i := by
  fin_cases i <;> simp [ofVec, colV, ofMat, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ofVec_single (j : Fin 3) : ofVec (Pi.single j 1) = unitV j := by
  fin_cases j <;> simp [ofVec, unitV]

theorem ofVec_smul (a : ZMod 3) (v : Fin 3 → ZMod 3) : ofVec (a • v) = vsmulR a (ofVec v) :=
  rfl

theorem mem_span_iff_inSpanR (u w : Fin 3 → ZMod 3) :
    u ∈ Submodule.span (ZMod 3) {w} ↔ inSpanR (ofVec u) (ofVec w) = true := by
  rw [Submodule.mem_span_singleton, inSpanR, List.any_eq_true]
  have hv : ∀ z : ZMod 3, z ∈ vals := by decide
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, hv a, by rw [beq_iff_eq, ofVec_smul]⟩
  · rintro ⟨a, -, h⟩
    rw [beq_iff_eq, ← ofVec_smul] at h
    exact ⟨a, ofVec_injective h.symm⟩

theorem mem_Lstd_iff (u : Fin 3 → ZMod 3) (j : Fin 3) :
    u ∈ Lstd j ↔ inSpanR (ofVec u) (unitV j) = true := by
  rw [mem_span_iff_inSpanR, ofVec_single]

theorem mono_check : monoCheck = true :=
  Certificates.certificate8172

theorem mc_ok :
    mc1 = true ∧ mc2 = true ∧ mc3 = true ∧ mc4 = true ∧ mc5 = true ∧ mc6 = true ∧
    mc7 = true := by
  have h := mono_check
  simp only [monoCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem isMonColR_eq (x y z : ZMod 3) : isMonColR ⟨x, y, z⟩ = monCol3 x.val y.val z.val := by
  revert x y z
  decide

theorem mem_monRaw_of_cols
    {M : R9} (hM : ∀ i < 3, isMonColR (colV M i) = true)
    (hdet : rdet M ≠ 0) : M ∈ monRaw := by
  have h := mc_ok.1
  rw [mc1, List.all_eq_true] at h
  have hc := h (code M) (List.mem_range.2 (code_lt M))
  have h0 := hM 0 (by norm_num)
  have h1 := hM 1 (by norm_num)
  have h2 := hM 2 (by norm_num)
  change isMonColR ⟨M.a, M.d, M.g⟩ = true at h0
  change isMonColR ⟨M.b, M.e, M.h⟩ = true at h1
  change isMonColR ⟨M.c, M.f, M.i⟩ = true at h2
  rw [isMonColR_eq] at h0 h1 h2
  simp only [mono1At, code_d0, code_d1, code_d2, code_d3, code_d4, code_d5, code_d6, code_d7,
    code_d8, ndet_code, h0, h1, h2, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · exact absurd ((ZMod.val_eq_zero _).1 hc) hdet
  · obtain ⟨N, hN, e⟩ := List.mem_map.1 (testBit_codeMask.1 hc)
    rw [← code_injective e]
    exact hN

theorem monRaw_props {M : R9} (hM : M ∈ monRaw) :
    (∀ i < 3, isMonColR (colV M i) = true) ∧ rdet M ≠ 0 ∧ ∃ N ∈ monRaw, rmul M N = rone := by
  have h := mc_ok.2.1
  simp only [mc2, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    beq_iff_eq, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h M hM
  exact ⟨h1, h2, h3⟩

theorem n0Raw_iff
    {M : R9} : M ∈ n0Raw ↔ M ∈ monRaw ∧ rdet M = 1 := by
  have h := mc_ok.2.2.1
  simp only [mc3, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem, beq_iff_eq, decide_eq_true_eq] at h
  constructor
  · exact h.1.1.2 M
  · rintro ⟨h1, h2⟩
    rcases h.1.1.1 M h1 with h' | h'
    · exact absurd h2 h'
    · exact h'

theorem n0Raw_nodup : n0Raw.Nodup ∧ n0Raw.length = 24 := by
  have h := mc_ok.2.2.1
  simp only [mc3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem psiTab_props :
    (∀ A ∈ n0Raw, ∀ B ∈ n0Raw,
      toP4 (psiTabR (rmul A B)) = toP4 (psiTabR A) * toP4 (psiTabR B)) ∧
    (∀ A ∈ n0Raw, ∀ B ∈ n0Raw, toP4 (psiTabR A) = toP4 (psiTabR B) → A = B) ∧
    (∀ M ∈ n0Raw, (Equiv.Perm.sign (toP4 (psiTabR M)) = 1 ↔ M ∈ g0Raw)) ∧
    (∀ M ∈ g0Raw, M ∈ n0Raw) := by
  have h := mc_ok.2.2.2.1
  simp only [mc4, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun A hA B hB hAB => ?_, fun M hM => ?_, fun M hM => ?_⟩
  · rcases h2 A hA B hB with h | h
    · exact absurd hAB h
    · exact h
  · have := h3 M hM
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem] at this
    exact this
  · exact List.contains_iff_mem.1 (h4 M hM)

theorem mc5_prop
    {M : R9} (hM : M ∈ monRaw) : M ∈ n0Raw ∨ rmul negR M ∈ n0Raw := by
  have h := mc_ok.2.2.2.2.1
  simp only [mc5, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
  exact h M hM

theorem mc6_prop {M₁ M₂ : R9} (h₁ : M₁ ∈ monRaw) (h₂ : M₂ ∈ monRaw)
    (hc₁ : inSpanR (colV M₁ 0) (unitV 1) = true) (hc₂ : inSpanR (colV M₂ 0) (unitV 2) = true) :
    rpowR M₁ 4 ∈ c3Raw ∨ rpowR M₂ 4 ∈ c3Raw ∨ rpowR (rmul M₁ M₂) 4 ∈ c3Raw := by
  have h := mc_ok.2.2.2.2.2.1
  simp only [mc6, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  rcases h M₁ h₁ M₂ h₂ with (((h | h) | h) | h) | h
  · rw [hc₁] at h; exact absurd h Bool.noConfusion
  · rw [hc₂] at h; exact absurd h Bool.noConfusion
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem mc7_fix
    {c : R9} (hc : c ∈ c3Raw) : fixVecR c ≠ vzero ∧ rmv c (fixVecR c) = fixVecR c := by
  have h := mc_ok.2.2.2.2.2.2
  simp only [mc7, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact h.1.1.1 c hc

theorem mc7_gen {c h : R9} (hc : c ∈ c3Raw) (hh : h ∈ monRaw)
    (hmove : inSpanR (rmv h (fixVecR c)) (fixVecR c) = false) :
    ∃ C P L n : ℕ, treeOKP [code c, code h] C P L n = true ∧
      ∀ g ∈ g0Raw, ∃ k < n, pk 20 C k = code g := by
  have h' := mc_ok.2.2.2.2.2.2
  simp only [mc7, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h'
  obtain ⟨⟨⟨-, h8⟩, h48⟩, hij⟩ := h'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have hat := hij i (h8 ▸ hi) j (h48 ▸ hj)
  rw [mono7At, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hmove,
    Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hat
  refine ⟨_, _, _, _, hat.1, fun g hg => ?_⟩
  have hm := hat.2 g hg
  rw [treeMask, testBit_codeMask, List.mem_map] at hm
  obtain ⟨k, hk, e⟩ := hm
  exact ⟨k, List.mem_range.1 hk, e⟩

theorem isMonColR_iff {v : V3} :
    isMonColR v = true ↔ v ≠ vzero ∧ ∃ j < 3, inSpanR v (unitV j) = true := by
  simp [isMonColR, bne_iff_ne, List.any_eq_true, List.mem_range]

theorem mem_monRaw_of_mem {g : GL33} (hg : g ∈ linePermuting Lstd) :
    ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ monRaw := by
  refine mem_monRaw_of_cols (fun i hi => ?_) ?_
  · obtain ⟨j, hj⟩ := (hg ⟨i, hi⟩).1
    rw [translate_Lstd_eq_iff, mem_Lstd_iff, ofVec_mulVec_single] at hj
    rw [isMonColR_iff]
    refine ⟨fun h0 => ?_, j, j.2, hj⟩
    have h1 := ofVec_mulVec_single (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ⟨i, hi⟩
    rw [h0, ← ofVec_zero] at h1
    exact gl_mulVec_ne_zero g (single_ne_zero ⟨i, hi⟩) (ofVec_injective h1)
  · rw [rdet_ofMat]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero

theorem translate_Lstd_of_monRaw {g : GL33}
    (hg : ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ monRaw) (i : Fin 3) :
    ∃ j, translate g (Lstd i) = Lstd j := by
  have h := ((monRaw_props hg).1 i i.2)
  rw [isMonColR_iff] at h
  obtain ⟨-, j, hj, hj'⟩ := h
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [translate_Lstd_eq_iff, mem_Lstd_iff, ofVec_mulVec_single]
  exact hj'

theorem mem_linePermuting_std_iff (g : GL33) :
    g ∈ linePermuting Lstd ↔ ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ monRaw := by
  refine ⟨mem_monRaw_of_mem, fun hg i => ⟨translate_Lstd_of_monRaw hg i, ?_⟩⟩
  obtain ⟨N, hN, hgN⟩ := (monRaw_props hg).2.2
  have hinv := ofMat_inv_of_rmul hgN
  exact translate_Lstd_of_monRaw (hinv ▸ hN) i

theorem mem_N0std_iff (g : GL33) :
    g ∈ monomialDetOne Lstd ↔ ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ n0Raw := by
  rw [monomialDetOne, Subgroup.mem_inf, mem_linePermuting_std_iff, mem_statedSL_iff, n0Raw_iff,
    rdet_ofMat]

theorem card_N0std : Nat.card (monomialDetOne Lstd) = 24 := by
  classical
  have hnd := n0Raw_nodup.1
  let φ : monomialDetOne Lstd → {r // r ∈ n0Raw} :=
    fun g => ⟨ofMat (g.1 : Matrix (Fin 3) (Fin 3) (ZMod 3)), (mem_N0std_iff g.1).1 g.2⟩
  have hinj : Function.Injective φ := fun g h e =>
    Subtype.ext (gl_eq_iff.2 (congrArg Subtype.val e))
  have hsurj : Function.Surjective φ := by
    rintro ⟨r, hr⟩
    have hdet : rdet r ≠ 0 := by rw [(n0Raw_iff.1 hr).2]; exact one_ne_zero
    exact ⟨⟨glOf r hdet, (mem_N0std_iff _).2 (by rw [ofMat_glOf]; exact hr)⟩,
      Subtype.ext (ofMat_glOf r hdet)⟩
  rw [Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩),
    ← Nat.card_congr (List.Nodup.getEquiv _ hnd), Nat.card_eq_fintype_card, Fintype.card_fin,
    n0Raw_nodup.2]

theorem ofMat_mem_n0 (g : monomialDetOne Lstd) :
    ofMat ((g : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ n0Raw :=
  (mem_N0std_iff g.1).1 g.2

noncomputable def psiStd :
    monomialDetOne Lstd →* Equiv.Perm (Fin 4) where
  toFun g := toP4 (psiTabR (ofMat ((g : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))))
  map_one' := by
    have h := psiTab_props.1 _ (ofMat_mem_n0 1) _ (ofMat_mem_n0 1)
    rw [← ofMat_glMul] at h
    simp only [OneMemClass.coe_one, mul_one] at h ⊢
    exact mul_eq_left.1 h.symm
  map_mul' g h := by
    change toP4 (psiTabR (ofMat (((g * h : monomialDetOne Lstd) : GL33) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)))) = _
    rw [Subgroup.coe_mul, ofMat_glMul]
    exact psiTab_props.1 _ (ofMat_mem_n0 g) _ (ofMat_mem_n0 h)

theorem psiStd_injective :
    Function.Injective psiStd := fun g h hgh =>
  Subtype.ext (gl_eq_iff.2 (psiTab_props.2.1 _ (ofMat_mem_n0 g) _ (ofMat_mem_n0 h) hgh))

theorem psiStd_bijective : Function.Bijective psiStd := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨psiStd_injective, ?_⟩
  rw [card_N0std, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

noncomputable def psiEquiv :
    monomialDetOne Lstd ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective psiStd psiStd_bijective

noncomputable def G0std : Subgroup GL33 :=
  ((alternatingGroup (Fin 4)).comap psiStd).map (monomialDetOne Lstd).subtype

theorem G0std_le : G0std ≤ monomialDetOne Lstd := map_subtype_le _

theorem G0std_subgroupOf :
    G0std.subgroupOf (monomialDetOne Lstd) = (alternatingGroup (Fin 4)).comap psiStd :=
  Subgroup.comap_map_eq_self_of_injective (monomialDetOne Lstd).subtype_injective _

theorem index_G0std :
    (G0std.subgroupOf (monomialDetOne Lstd)).index = 2 := by
  rw [G0std_subgroupOf, (alternatingGroup (Fin 4)).index_comap_of_surjective psiStd_bijective.2,
    alternatingGroup.index_eq_two]

noncomputable def G0Equiv : G0std ≃* alternatingGroup (Fin 4) :=
  (Subgroup.equivMapOfInjective _ _ (monomialDetOne Lstd).subtype_injective).symm.trans
    ((MulEquiv.subgroupMap psiEquiv ((alternatingGroup (Fin 4)).comap psiStd)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective psiStd_bijective.2 _)))

theorem mem_G0std_iff (g : GL33) :
    g ∈ G0std ↔ ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ g0Raw := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup] at hn
    exact (psiTab_props.2.2.1 _ (ofMat_mem_n0 n)).1 hn
  · intro hg
    have hN : g ∈ monomialDetOne Lstd := (mem_N0std_iff g).2 (psiTab_props.2.2.2 _ hg)
    refine ⟨⟨g, hN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    exact (psiTab_props.2.2.1 _ ((mem_N0std_iff g).1 hN)).2 hg

theorem mem_zpowers_neg_one_iff {x : GL33} : x ∈ zpowers (-1) ↔ x = 1 ∨ x = -1 := by
  have h2 : (-1 : GL33) ^ 2 = 1 := by rw [sq, neg_one_mul, neg_neg]
  have hfin : IsOfFinOrder (-1 : GL33) := isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, h2⟩
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (hfin.mem_zpowers_iff_mem_range_orderOf.1 hx)
    rw [Finset.mem_range] at hk
    have hle : orderOf (-1 : GL33) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) h2
    have hk2 : k < 2 := lt_of_lt_of_le hk hle
    interval_cases k <;> simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem ofMat_neg_one : ofMat ((-1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = negR := by
  rw [Units.val_neg, Units.val_one]
  decide

theorem N0_inf_neg_one (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    monomialDetOne L ⊓ zpowers (-1) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hx⟩ := Subgroup.mem_inf.1 hx
  rcases mem_zpowers_neg_one_iff.1 hx with rfl | rfl
  · exact one_mem _
  · exfalso
    have := (Subgroup.mem_inf.1 hxN).2
    rw [mem_statedSL_iff, Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one] at this
    revert this
    decide

theorem le_N0std_sup
    {G : Subgroup GL33} (hle : G ≤ linePermuting Lstd) :
    G ≤ monomialDetOne Lstd ⊔ zpowers (-1) := by
  intro g hg
  rcases mc5_prop (mem_monRaw_of_mem (hle hg)) with h | h
  · exact Subgroup.mem_sup_left ((mem_N0std_iff g).2 h)
  · have hn : (-1) * g ∈ monomialDetOne Lstd := by
      rw [mem_N0std_iff, ofMat_glMul, ofMat_neg_one]
      exact h
    have : g = (-1) * ((-1) * g) := by rw [← mul_assoc, neg_one_mul, neg_neg, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers _)) (Subgroup.mem_sup_left hn)

theorem G0std_le_of
    {G : Subgroup GL33} (hle : G ≤ linePermuting Lstd)
    (htr : ∀ i j, ∃ g ∈ G, translate g (Lstd i) = Lstd j) (hirr : IsIrreducibleOn G) :
    G0std ≤ G := by
  obtain ⟨h₁, h₁G, hh₁⟩ := htr 0 1
  obtain ⟨h₂, h₂G, hh₂⟩ := htr 0 2
  have hc₁ : inSpanR (colV (ofMat (h₁ : Matrix (Fin 3) (Fin 3) (ZMod 3))) 0) (unitV 1) = true := by
    rw [translate_Lstd_eq_iff, mem_Lstd_iff, ofVec_mulVec_single] at hh₁
    exact hh₁
  have hc₂ : inSpanR (colV (ofMat (h₂ : Matrix (Fin 3) (Fin 3) (ZMod 3))) 0) (unitV 2) = true := by
    rw [translate_Lstd_eq_iff, mem_Lstd_iff, ofVec_mulVec_single] at hh₂
    exact hh₂
  obtain ⟨c₀, hc₀G, hc₀⟩ : ∃ c₀ ∈ G, ofMat (c₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ c3Raw := by
    rcases mc6_prop (mem_monRaw_of_mem (hle h₁G)) (mem_monRaw_of_mem (hle h₂G)) hc₁ hc₂ with
      h | h | h
    · exact ⟨h₁ ^ 4, G.pow_mem h₁G 4, by rw [ofMat_glPow]; exact h⟩
    · exact ⟨h₂ ^ 4, G.pow_mem h₂G 4, by rw [ofMat_glPow]; exact h⟩
    · exact ⟨(h₁ * h₂) ^ 4, G.pow_mem (G.mul_mem h₁G h₂G) 4, by
        rw [ofMat_glPow, ofMat_glMul]; exact h⟩
  set w : Fin 3 → ZMod 3 := toVec (fixVecR (ofMat (c₀ : Matrix (Fin 3) (Fin 3) (ZMod 3))))
    with hw
  have hw0 : w ≠ 0 := fun h0 => (mc7_fix hc₀).1 (by rw [← ofVec_toVec (fixVecR _), ← hw, h0,
    ofVec_zero])
  obtain ⟨h, hhG, hhw⟩ : ∃ h ∈ G, (h : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∉
      Submodule.span (ZMod 3) {w} := by
    by_contra hcon
    push Not at hcon
    rcases hirr (Submodule.span (ZMod 3) {w}) (fun g hg u hu => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ (hcon g hg)) with h | h
    · exact hw0 ((Submodule.span_singleton_eq_bot).1 h)
    · have h1 := congrArg (fun W : Submodule (ZMod 3) (Fin 3 → ZMod 3) =>
        Module.finrank (ZMod 3) W) h
      rw [finrank_span_singleton hw0, finrank_top, Module.finrank_fin_fun] at h1
      norm_num at h1
  have hmove : inSpanR (rmv (ofMat (h : Matrix (Fin 3) (Fin 3) (ZMod 3)))
      (fixVecR (ofMat (c₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)))))
      (fixVecR (ofMat (c₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)))) = false := by
    rw [Bool.eq_false_iff]
    intro hin
    apply hhw
    rw [mem_span_iff_inSpanR, ofVec_mulVec, hw, ofVec_toVec]
    exact hin
  obtain ⟨C, P, L, n, hT, hcov⟩ := mc7_gen hc₀ (mem_monRaw_of_mem (hle hhG)) hmove
  intro x hx
  obtain ⟨k, hk, hkx⟩ := hcov _ ((mem_G0std_iff x).1 hx)
  have hmul : ∀ a b : GL33, ofMat ((a * b : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      rmul (ofMat (a : Matrix (Fin 3) (Fin 3) (ZMod 3))) (ofMat (b : Matrix _ _ _)) :=
    ofMat_glMul
  obtain ⟨y, hy, hyx⟩ := treeOKP_mem (fun a : GL33 =>
    ofMat (a : Matrix (Fin 3) (Fin 3) (ZMod 3))) hmul ofMat_glOne [c₀, h] (by simpa using hT) k hk
  have hyx' : y = x := gl_eq_iff.2 (code_injective (hyx.trans hkx))
  rw [← hyx']
  refine (Subgroup.closure_le G).2 ?_ hy
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hz
  rcases hz with rfl | rfl
  · exact hc₀G
  · exact hhG

end CFSG.RankThree.PartTwo.Toolkit
