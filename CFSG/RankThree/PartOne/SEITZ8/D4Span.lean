module

public import CFSG.RankThree.PartOne.SEITZ8.D4Triple
public import CFSG.RankThree.PartOne.SEITZ8.D4Mono

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

section Act


theorem smul_eq_end (g : adjointGroup d4 K) (x : RootModule d4 K) :
    g • x = ((g : ModGL d4 K) : Module.End K (RootModule d4 K)) x := rfl

theorem smul_smul_comm' (g : adjointGroup d4 K) (c : K) (x : RootModule d4 K) :
    g • (c • x) = c • (g • x) := by
  simp only [smul_eq_end, map_smul]

noncomputable abbrev rv (p : ℕ) : RootModule d4 K := rootVec d4 K (d4Root p)

@[expose] def rI (p : ℕ) (h : p < 24) : DIdx := Sum.inr ⟨p, by rw [len_d4]; exact h⟩

theorem toVec_rI (p : ℕ) (h : p < 24) :
    toVec (Tag.rootCertificate_check d4) K (some (rI p h, 1)) = rv p := by
  rw [toVec_some, Int.cast_one, one_smul]
  exact single_toLabel_inr (Tag.rootCertificate_check d4) K _

end Act

structure Rat3 (σ : K →+* K) (k : Subfield K) : Prop where
  stable : ∀ a ∈ k, σ a ∈ k
  ind : MonoInd k (RingHom.restrict σ k k stable)

@[expose] def Rat3.res {σ : K →+* K} {k : Subfield K} (h : Rat3 σ k) : k →+* k :=
  RingHom.restrict σ k k h.stable

theorem Rat3.res_apply {σ : K →+* K} {k : Subfield K} (h : Rat3 σ k) (a : k) :
    ((h.res a : k) : K) = σ a := rfl

@[expose] def vanishX : Bool :=
  (List.range 4).all fun k₀ => (List.range 4).all fun k₁ => (List.range 4).all fun k₃ =>
    decide (k₀ < 2 ∧ k₁ < 2 ∧ k₃ < 2) || (comp3 xg k₀ k₁ k₃ (rI 2 (by decide)) == none)

@[expose] def vanishY : Bool :=
  (List.range 4).all fun k₀ => (List.range 4).all fun k₁ => (List.range 4).all fun k₃ =>
    decide (k₀ < 2 ∧ k₁ < 2 ∧ k₃ < 2) || (comp3 yg k₀ k₁ k₃ (rI 8 (by decide)) == none)

theorem vanishX_eq : vanishX = true := by decide +kernel
theorem vanishY_eq : vanishY = true := by decide +kernel

theorem valsX :
    comp3 xg 0 0 1 (rI 2 (by decide)) = some (rI 9 (by decide), 1) ∧
    comp3 xg 0 1 0 (rI 2 (by decide)) = some (rI 7 (by decide), 1) ∧
    comp3 xg 0 1 1 (rI 2 (by decide)) = some (rI 15 (by decide), 1) ∧
    comp3 xg 1 0 0 (rI 2 (by decide)) = some (rI 5 (by decide), 1) ∧
    comp3 xg 1 0 1 (rI 2 (by decide)) = some (rI 13 (by decide), 1) ∧
    comp3 xg 1 1 0 (rI 2 (by decide)) = some (rI 12 (by decide), 1) := by
  decide +kernel

theorem valsY :
    comp3 yg 0 0 1 (rI 8 (by decide)) = some (rI 16 (by decide), 1) ∧
    comp3 yg 0 1 0 (rI 8 (by decide)) = some (rI 14 (by decide), 1) ∧
    comp3 yg 0 1 1 (rI 8 (by decide)) = some (rI 20 (by decide), 1) ∧
    comp3 yg 1 0 0 (rI 8 (by decide)) = some (rI 11 (by decide), 1) ∧
    comp3 yg 1 0 1 (rI 8 (by decide)) = some (rI 18 (by decide), 1) ∧
    comp3 yg 1 1 0 (rI 8 (by decide)) = some (rI 17 (by decide), 1) := by
  decide +kernel

section Span

variable [CharP K 2]

@[expose] def longOrbit (R : Subgroup (adjointGroup d4 K)) : Set (RootModule d4 K) :=
  {x | ∃ r ∈ R, ∃ p ∈ longPos, x = r • rv p}

omit [CharP K 2] in
theorem smul_mem_span (k : Subfield K) {R : Subgroup (adjointGroup d4 K)}
    {r : adjointGroup d4 K} (hr : r ∈ R) {w : RootModule d4 K}
    (hw : w ∈ Submodule.span k (longOrbit R)) : r • w ∈ Submodule.span k (longOrbit R) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r', hr', σ, hσ, rfl⟩ := hx
    exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', σ, hσ, (mul_smul r r' _).symm⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : r • (a • x) = a • (r • x) := smul_smul_comm' r (a : K) x
    rw [this]
    exact Submodule.smul_mem _ a hx

omit [CharP K 2] in
theorem rv_eq_single (p : ℕ) (h : p < 24) :
    rv p = Finsupp.single (toLabel (Tag.rootCertificate_check d4) (rI p h)) (1 : K) :=
  (single_toLabel_inr (Tag.rootCertificate_check d4) K ⟨p, by rw [len_d4]; exact h⟩).symm

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

omit [CharP K 2] in
theorem rv_long_mem {p : ℕ} (hp : p ∈ longPos) : rv p ∈ Submodule.span k (longOrbit R) :=
  Submodule.subset_span ⟨1, R.one_mem, p, hp, by rw [one_smul]⟩

omit [CharP K 2] in
theorem smul_coe_eq (c : k) (v : RootModule d4 K) : c • v = (c : K) • v := rfl

omit [CharP K 2] in
theorem coe_char (hk : Rat3 σ k) (a : k) (m : ℕ × ℕ × ℕ) :
    (((RingHom.restrict σ k k hk.stable) ((RingHom.restrict σ k k hk.stable) a) ^ m.1 *
        (RingHom.restrict σ k k hk.stable) a ^ m.2.1 * a ^ m.2.2 : k) : K) =
      σ (σ a) ^ m.1 * σ a ^ m.2.1 * (a : K) ^ m.2.2 := by
  simp only [Subfield.coe_mul, SubmonoidClass.coe_pow]
  rfl

theorem vanish_of_vanishX (m : ℕ × ℕ × ℕ)
    (hm : m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4)
    (hm2 : m ∉ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2) :
    comp3 xg m.2.2 m.2.1 m.1 (rI 2 (by decide)) = none := by
  have h := vanishX_eq
  simp only [vanishX, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  simp only [Finset.mem_product, Finset.mem_range] at hm hm2
  rcases h m.2.2 hm.2.2 m.2.1 hm.2.1 m.1 hm.1 with h1 | h1
  · exfalso
    exact hm2 ⟨h1.2.2, h1.2.1, h1.1⟩
  · exact h1

theorem vanish_of_vanishY (m : ℕ × ℕ × ℕ)
    (hm : m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4)
    (hm2 : m ∉ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2) :
    comp3 yg m.2.2 m.2.1 m.1 (rI 8 (by decide)) = none := by
  have h := vanishY_eq
  simp only [vanishY, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  simp only [Finset.mem_product, Finset.mem_range] at hm hm2
  rcases h m.2.2 hm.2.2 m.2.1 hm.2.1 m.1 hm.1 with h1 | h1
  · exfalso
    exact hm2 ⟨h1.2.2, h1.2.1, h1.1⟩
  · exact h1

omit [CharP K 2] in
theorem extractX (hk : Rat3 σ k)
    (hA : ∀ a ∈ k, (xe 0 a * xe 1 (σ a) * xe 3 (σ (σ a)) : adjointGroup d4 K) ∈ R) :
    ∀ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      toVec (Tag.rootCertificate_check d4) K (comp3 xg m.2.2 m.2.1 m.1 (rI 2 (by decide))) ∈
        Submodule.span k (longOrbit R) := by
  refine extract8 hk.ind (Submodule.span k (longOrbit R))
    (fun m => toVec (Tag.rootCertificate_check d4) K (comp3 xg m.2.2 m.2.1 m.1 (rI 2 (by decide))))
    fun a => ?_
  have hv : rv 2 ∈ Submodule.span k (longOrbit R) := rv_long_mem (by simp [longPos])
  have hmem := smul_mem_span k (hA a a.2) hv
  have hexp : (xe 0 (a : K) * xe 1 (σ a) * xe 3 (σ (σ a)) : adjointGroup d4 K) • rv 2 =
      ∑ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
        (σ (σ a) ^ m.1 * σ a ^ m.2.1 * (a : K) ^ m.2.2) •
          toVec (Tag.rootCertificate_check d4) K
            (comp3 xg m.2.2 m.2.1 m.1 (rI 2 (by decide))) := by
    rw [mul_smul, mul_smul, xe_smul_simple (nd 3) d4Root_simple_3,
      xe_smul_simple (nd 1) d4Root_simple_1, xe_smul_simple (nd 0) d4Root_simple_0,
      rv_eq_single 2 (by decide), triple_expand_x]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro m hm
      simp only [Finset.mem_product, Finset.mem_range] at hm ⊢
      omega
    · intro m hm hm2
      rw [vanish_of_vanishX m hm hm2, toVec_none, smul_zero]
  rw [hexp] at hmem
  convert hmem using 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_coe_eq, coe_char hk]

omit [CharP K 2] in
theorem extractY (hk : Rat3 σ k)
    (hA : ∀ a ∈ k, (xe 4 a * xe 6 (σ a) * xe 10 (σ (σ a)) : adjointGroup d4 K) ∈ R) :
    ∀ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      toVec (Tag.rootCertificate_check d4) K (comp3 yg m.2.2 m.2.1 m.1 (rI 8 (by decide))) ∈
        Submodule.span k (longOrbit R) := by
  refine extract8 hk.ind (Submodule.span k (longOrbit R))
    (fun m => toVec (Tag.rootCertificate_check d4) K (comp3 yg m.2.2 m.2.1 m.1 (rI 8 (by decide))))
    fun a => ?_
  have hv : rv 8 ∈ Submodule.span k (longOrbit R) := rv_long_mem (by simp [longPos])
  have hmem := smul_mem_span k (hA a a.2) hv
  have hexp : (xe 4 (a : K) * xe 6 (σ a) * xe 10 (σ (σ a)) : adjointGroup d4 K) • rv 8 =
      ∑ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
        (σ (σ a) ^ m.1 * σ a ^ m.2.1 * (a : K) ^ m.2.2) •
          toVec (Tag.rootCertificate_check d4) K
            (comp3 yg m.2.2 m.2.1 m.1 (rI 8 (by decide))) := by
    rw [mul_smul, mul_smul, xe_smul_neg_simple (nd 3) d4Root_neg_3,
      xe_smul_neg_simple (nd 1) d4Root_neg_1, xe_smul_neg_simple (nd 0) d4Root_neg_0,
      rv_eq_single 8 (by decide), triple_expand_y]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro m hm
      simp only [Finset.mem_product, Finset.mem_range] at hm ⊢
      omega
    · intro m hm hm2
      rw [vanish_of_vanishY m hm hm2, toVec_none, smul_zero]
  rw [hexp] at hmem
  convert hmem using 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_coe_eq, coe_char hk]

structure SpanHyp (σ : K →+* K) (k : Subfield K) (R : Subgroup (adjointGroup d4 K)) : Prop where
  rat : Rat3 σ k
  A : ∀ a ∈ k, (xe 0 a * xe 1 (σ a) * xe 3 (σ (σ a)) : adjointGroup d4 K) ∈ R
  Am : ∀ a ∈ k, (xe 4 a * xe 6 (σ a) * xe 10 (σ (σ a)) : adjointGroup d4 K) ∈ R
  x2 : (xe 2 1 : adjointGroup d4 K) ∈ R
  y2 : (xe 8 1 : adjointGroup d4 K) ∈ R
  n0 : weylElement d4 K (nd 2) ∈ R
  n1 : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ R

omit [CharP K 2] in
theorem xOp_single_eq (Op : Fin d4.rank → K → Module.End K (RootModule d4 K))
    (Co : Fin d4.rank → ℕ → Module.End K (RootModule d4 K))
    (F : Fin d4.rank → ℕ → DIdx → Col (Tag.rootCertificate d4))
    (hOp : ∀ i c, Op i c = ∑ k ∈ Finset.range 4, c ^ k • Co i k)
    (hCo : ∀ i k b, Co i k (Finsupp.single (toLabel (Tag.rootCertificate_check d4) b) 1) =
      toVec (Tag.rootCertificate_check d4) K (F i k b))
    (i : Fin d4.rank) (c : DIdx)
    (c₀ c₁ c₂ c₃ : Col (Tag.rootCertificate d4))
    (h0 : bindCol (Tag.rootCertificate d4) (F i 0) (some (c, 1)) = c₀)
    (h1 : bindCol (Tag.rootCertificate d4) (F i 1) (some (c, 1)) = c₁)
    (h2 : bindCol (Tag.rootCertificate d4) (F i 2) (some (c, 1)) = c₂)
    (h3 : bindCol (Tag.rootCertificate d4) (F i 3) (some (c, 1)) = c₃) :
    Op i 1 (Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) 1) =
      toVec (Tag.rootCertificate_check d4) K c₀ + toVec (Tag.rootCertificate_check d4) K c₁ +
        toVec (Tag.rootCertificate_check d4) K c₂ + toVec (Tag.rootCertificate_check d4) K c₃ := by
  have e1 : Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) (1 : K) =
      toVec (Tag.rootCertificate_check d4) K (some (c, 1)) := by
    rw [toVec_some, Int.cast_one, one_smul]
  rw [e1, op_toVec Op Co F hOp hCo]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, one_smul, h0, h1, h2,
    h3]

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

omit [CharP K 2] in
theorem move2y (hR : (xe 8 1 : adjointGroup d4 K) ∈ R) (p p' : ℕ) (hp : p < 24) (hp' : p' < 24)
    (h0 : bindCol (Tag.rootCertificate d4) (yg (nd 2) 0) (some (rI p hp, 1)) = some (rI p hp, 1))
    (h1 : bindCol (Tag.rootCertificate d4) (yg (nd 2) 1) (some (rI p hp, 1)) =
      some (rI p' hp', 1))
    (h2 : bindCol (Tag.rootCertificate d4) (yg (nd 2) 2) (some (rI p hp, 1)) = none)
    (h3 : bindCol (Tag.rootCertificate d4) (yg (nd 2) 3) (some (rI p hp, 1)) = none)
    (hv : rv p ∈ Submodule.span k (longOrbit R)) : rv p' ∈ Submodule.span k (longOrbit R) := by
  have hexp : (xe 8 1 : adjointGroup d4 K) • (rv p : RootModule d4 K) = rv p + rv p' := by
    rw [xe_smul_neg_simple (nd 2) d4Root_neg_2, rv_eq_single p hp,
      xOp_single_eq (yOp d4 K) (yCoeff d4 K) yg (fun i c => yOp_eq_sum_yCoeff i c)
        (fun i k b => yCoeff_toLabel (Tag.rootCertificate_check d4) K
          (Tag.stringData_check d4) i k b) (nd 2) (rI p hp) _ _ _ _ h0 h1 h2 h3]
    simp only [toVec_none, toVec_rI, add_zero]
    rw [rv_eq_single p hp]
  have hm := smul_mem_span k hR hv
  rw [hexp] at hm
  have := Submodule.sub_mem _ hm hv
  rwa [add_sub_cancel_left] at this

omit [CharP K 2] in
theorem move2x (hR : (xe 2 1 : adjointGroup d4 K) ∈ R) (p p' : ℕ) (hp : p < 24) (hp' : p' < 24)
    (h0 : bindCol (Tag.rootCertificate d4) (xg (nd 2) 0) (some (rI p hp, 1)) = some (rI p hp, 1))
    (h1 : bindCol (Tag.rootCertificate d4) (xg (nd 2) 1) (some (rI p hp, 1)) =
      some (rI p' hp', 1))
    (h2 : bindCol (Tag.rootCertificate d4) (xg (nd 2) 2) (some (rI p hp, 1)) = none)
    (h3 : bindCol (Tag.rootCertificate d4) (xg (nd 2) 3) (some (rI p hp, 1)) = none)
    (hv : rv p ∈ Submodule.span k (longOrbit R)) : rv p' ∈ Submodule.span k (longOrbit R) := by
  have hexp : (xe 2 1 : adjointGroup d4 K) • (rv p : RootModule d4 K) = rv p + rv p' := by
    rw [xe_smul_simple (nd 2) d4Root_simple_2, rv_eq_single p hp,
      xOp_single_eq (xOp d4 K) (xCoeff d4 K) xg (fun i c => xOp_eq_sum_xCoeff i c)
        (fun i k b => xCoeff_toLabel (Tag.rootCertificate_check d4) K
          (Tag.stringData_check d4) i k b) (nd 2) (rI p hp) _ _ _ _ h0 h1 h2 h3]
    simp only [toVec_none, toVec_rI, add_zero]
    rw [rv_eq_single p hp]
  have hm := smul_mem_span k hR hv
  rw [hexp] at hm
  have := Submodule.sub_mem _ hm hv
  rwa [add_sub_cancel_left] at this

theorem moves2y_check :
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 0) (some (rI 9 (by decide), 1)) =
      some (rI 9 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 1) (some (rI 9 (by decide), 1)) =
      some (rI 3 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 2) (some (rI 9 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 3) (some (rI 9 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 0) (some (rI 7 (by decide), 1)) =
      some (rI 7 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 1) (some (rI 7 (by decide), 1)) =
      some (rI 1 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 2) (some (rI 7 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 3) (some (rI 7 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 0) (some (rI 5 (by decide), 1)) =
      some (rI 5 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 1) (some (rI 5 (by decide), 1)) =
      some (rI 0 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 2) (some (rI 5 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (yg (nd 2) 3) (some (rI 5 (by decide), 1)) = none := by
  decide +kernel

theorem moves2x_check :
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 0) (some (rI 16 (by decide), 1)) =
      some (rI 16 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 1) (some (rI 16 (by decide), 1)) =
      some (rI 10 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 2) (some (rI 16 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 3) (some (rI 16 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 0) (some (rI 14 (by decide), 1)) =
      some (rI 14 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 1) (some (rI 14 (by decide), 1)) =
      some (rI 6 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 2) (some (rI 14 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 3) (some (rI 14 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 0) (some (rI 11 (by decide), 1)) =
      some (rI 11 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 1) (some (rI 11 (by decide), 1)) =
      some (rI 4 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 2) (some (rI 11 (by decide), 1)) = none ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 3) (some (rI 11 (by decide), 1)) = none := by
  decide +kernel

omit [CharP K 2] in
theorem rv_mem_span (h : SpanHyp σ k R) {p : ℕ} (hp : p < 24) :
    rv p ∈ Submodule.span k (longOrbit R) := by
  have hX := extractX h.rat h.A
  have hY := extractY h.rat h.Am
  obtain ⟨hv9, hv7, hv15, hv5, hv13, hv12⟩ := valsX
  obtain ⟨hw16, hw14, hw20, hw11, hw18, hw17⟩ := valsY
  obtain ⟨y9a, y9b, y9c, y9d, y7a, y7b, y7c, y7d, y5a, y5b, y5c, y5d⟩ := moves2y_check
  obtain ⟨x16a, x16b, x16c, x16d, x14a, x14b, x14c, x14d, x11a, x11b, x11c, x11d⟩ :=
    moves2x_check
  have m9 : rv 9 ∈ Submodule.span k (longOrbit R) := by
    have := hX (1, 0, 0) (by simp)
    simp only [hv9, toVec_rI] at this
    exact this
  have m7 : rv 7 ∈ Submodule.span k (longOrbit R) := by
    have := hX (0, 1, 0) (by simp)
    simp only [hv7, toVec_rI] at this
    exact this
  have m15 : rv 15 ∈ Submodule.span k (longOrbit R) := by
    have := hX (1, 1, 0) (by simp)
    simp only [hv15, toVec_rI] at this
    exact this
  have m5 : rv 5 ∈ Submodule.span k (longOrbit R) := by
    have := hX (0, 0, 1) (by simp)
    simp only [hv5, toVec_rI] at this
    exact this
  have m13 : rv 13 ∈ Submodule.span k (longOrbit R) := by
    have := hX (1, 0, 1) (by simp)
    simp only [hv13, toVec_rI] at this
    exact this
  have m12 : rv 12 ∈ Submodule.span k (longOrbit R) := by
    have := hX (0, 1, 1) (by simp)
    simp only [hv12, toVec_rI] at this
    exact this
  have m16 : rv 16 ∈ Submodule.span k (longOrbit R) := by
    have := hY (1, 0, 0) (by simp)
    simp only [hw16, toVec_rI] at this
    exact this
  have m14 : rv 14 ∈ Submodule.span k (longOrbit R) := by
    have := hY (0, 1, 0) (by simp)
    simp only [hw14, toVec_rI] at this
    exact this
  have m20 : rv 20 ∈ Submodule.span k (longOrbit R) := by
    have := hY (1, 1, 0) (by simp)
    simp only [hw20, toVec_rI] at this
    exact this
  have m11 : rv 11 ∈ Submodule.span k (longOrbit R) := by
    have := hY (0, 0, 1) (by simp)
    simp only [hw11, toVec_rI] at this
    exact this
  have m18 : rv 18 ∈ Submodule.span k (longOrbit R) := by
    have := hY (1, 0, 1) (by simp)
    simp only [hw18, toVec_rI] at this
    exact this
  have m17 : rv 17 ∈ Submodule.span k (longOrbit R) := by
    have := hY (0, 1, 1) (by simp)
    simp only [hw17, toVec_rI] at this
    exact this
  have m3 := move2y h.y2 9 3 (by decide) (by decide) y9a y9b y9c y9d m9
  have m1 := move2y h.y2 7 1 (by decide) (by decide) y7a y7b y7c y7d m7
  have m0 := move2y h.y2 5 0 (by decide) (by decide) y5a y5b y5c y5d m5
  have m10 := move2x h.x2 16 10 (by decide) (by decide) x16a x16b x16c x16d m16
  have m6 := move2x h.x2 14 6 (by decide) (by decide) x14a x14b x14c x14d m14
  have m4 := move2x h.x2 11 4 (by decide) (by decide) x11a x11b x11c x11d m11
  interval_cases p
  · exact m0
  · exact m1
  · exact rv_long_mem (by simp [longPos])
  · exact m3
  · exact m4
  · exact m5
  · exact m6
  · exact m7
  · exact rv_long_mem (by simp [longPos])
  · exact m9
  · exact m10
  · exact m11
  · exact m12
  · exact m13
  · exact m14
  · exact m15
  · exact m16
  · exact m17
  · exact m18
  · exact rv_long_mem (by simp [longPos])
  · exact m20
  · exact rv_long_mem (by simp [longPos])
  · exact rv_long_mem (by simp [longPos])
  · exact rv_long_mem (by simp [longPos])

theorem h2cols_check :
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 0) (some (rI 8 (by decide), 1)) =
      some (rI 8 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 1) (some (rI 8 (by decide), 1)) =
      some (Sum.inl (nd 2), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 2) (some (rI 8 (by decide), 1)) =
      some (rI 2 (by decide), 1) ∧
    bindCol (Tag.rootCertificate d4) (xg (nd 2) 3) (some (rI 8 (by decide), 1)) = none := by
  decide +kernel

omit [CharP K 2] in
theorem xe2_smul_rv8 :
    (xe 2 1 : adjointGroup d4 K) • (rv 8 : RootModule d4 K) = rv 8 + hVec d4 K (nd 2) + rv 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := h2cols_check
  rw [xe_smul_simple (nd 2) d4Root_simple_2, rv_eq_single 8 (by decide),
    xOp_single_eq (xOp d4 K) (xCoeff d4 K) xg (fun i c => xOp_eq_sum_xCoeff i c)
      (fun i k b => xCoeff_toLabel (Tag.rootCertificate_check d4) K
        (Tag.stringData_check d4) i k b) (nd 2) (rI 8 (by decide)) _ _ _ _ c0 c1 c2 c3]
  simp only [toVec_none, add_zero, toVec_some, Int.cast_one, one_smul]
  rw [rv_eq_single 2 (by decide)]
  rfl

omit [CharP K 2] in
theorem h2_mem_span (h : SpanHyp σ k R) :
    hVec d4 K (nd 2) ∈ Submodule.span k (longOrbit R) := by
  have h8 : rv 8 ∈ Submodule.span k (longOrbit R) := rv_long_mem (by simp [longPos])
  have h2 : rv 2 ∈ Submodule.span k (longOrbit R) := rv_long_mem (by simp [longPos])
  have hm := smul_mem_span k h.x2 h8
  rw [xe2_smul_rv8] at hm
  have e : hVec d4 K (nd 2) = (rv 8 + hVec d4 K (nd 2) + rv 2) - rv 8 - rv 2 := by abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hm h8) h2

theorem cartan_natAbs_check :
    (d4.cartan (nd 2) (nd 3)).natAbs = 1 ∧ (d4.cartan (nd 2) (nd 1)).natAbs = 1 ∧
    (d4.cartan (nd 2) (nd 0)).natAbs = 1 ∧ (d4.cartan (nd 3) (nd 1)).natAbs = 0 ∧
    (d4.cartan (nd 3) (nd 0)).natAbs = 0 ∧ (d4.cartan (nd 1) (nd 0)).natAbs = 0 := by
  decide +kernel

theorem vec_add_self (x : RootModule d4 K) : x + x = 0 := by
  rw [← two_smul K x, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]

theorem Wn_smul_h2 :
    (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
        adjointGroup d4 K) • hVec d4 K (nd 2) =
      hVec d4 K (nd 2) + hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) := by
  obtain ⟨a23, a21, a20, a31, a30, a10⟩ := cartan_natAbs_check
  have hneg : ∀ x : RootModule d4 K, -x = x := fun x => neg_eq_of_add_eq_zero_right (vec_add_self x)
  have hw3_2 : (weylElt d4 K (nd 3) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 2)) =
      hVec d4 K (nd 2) - hVec d4 K (nd 3) := by
    rw [weylElt_hVec, a23]
    simp
  have hw1_2 : (weylElt d4 K (nd 1) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 2)) =
      hVec d4 K (nd 2) - hVec d4 K (nd 1) := by
    rw [weylElt_hVec, a21]
    simp
  have hw1_3 : (weylElt d4 K (nd 1) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 3)) =
      hVec d4 K (nd 3) := by
    rw [weylElt_hVec, a31]
    simp
  have hw0_2 : (weylElt d4 K (nd 0) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 2)) =
      hVec d4 K (nd 2) - hVec d4 K (nd 0) := by
    rw [weylElt_hVec, a20]
    simp
  have hw0_1 : (weylElt d4 K (nd 0) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 1)) =
      hVec d4 K (nd 1) := by
    rw [weylElt_hVec, a10]
    simp
  have hw0_3 : (weylElt d4 K (nd 0) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 3)) =
      hVec d4 K (nd 3) := by
    rw [weylElt_hVec, a30]
    simp
  rw [mul_smul, mul_smul]
  show (weylElt d4 K (nd 0) 1 : Module.End K (RootModule d4 K))
      ((weylElt d4 K (nd 1) 1 : Module.End K (RootModule d4 K))
        ((weylElt d4 K (nd 3) 1 : Module.End K (RootModule d4 K)) (hVec d4 K (nd 2)))) = _
  rw [hw3_2, map_sub, hw1_2, hw1_3, map_sub, map_sub, hw0_2, hw0_1, hw0_3]
  simp only [sub_eq_add_neg, hneg]

theorem t2_mem_span (h : SpanHyp σ k R) :
    hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) ∈
      Submodule.span k (longOrbit R) := by
  have hm := Submodule.add_mem _ (smul_mem_span k h.n1 (h2_mem_span h)) (h2_mem_span h)
  rw [Wn_smul_h2] at hm
  have e : hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) =
      hVec d4 K (nd 2) + hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3) +
        hVec d4 K (nd 2) := by
    have := vec_add_self (hVec d4 K (nd 2))
    calc hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3)
        = (hVec d4 K (nd 0) + hVec d4 K (nd 1) + hVec d4 K (nd 3)) + 0 := by rw [add_zero]
      _ = _ := by rw [← this]; abel
  rw [e]
  exact hm

end Span

end CFSG.RankThree.PartOne.SEITZ8
