module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Levi1

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem mem_stdF_two {w : Ix3 → F} :
    w ∈ stdF F 2 ↔ w (.inl 1) = 0 ∧ w (.inl 2) = 0 ∧ w (.inr 0) = 0 ∧ w (.inr 1) = 0 := by
  rw [mem_stdF]
  conv_lhs => rw [q6_eta w]
  rw [inF_q6_iff]
  constructor
  · rintro ⟨-, h1, h2, h3, h4, -⟩
    exact ⟨h1 (by norm_num), h2 (by norm_num), h3 (by norm_num), h4 (by norm_num)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, fun _ => h1, fun _ => h2, fun _ => h3, fun _ => h4, by omega⟩

@[expose] def upart (w : Ix3 → F) : Fin 2 → F := ![w (.inl 0), w (.inr 2)]

omit [CharP F 2] in
theorem upart_add (w w' : Ix3 → F) : upart (w + w') = upart w + upart w' := by
  funext i
  fin_cases i <;> rfl

omit [CharP F 2] in
theorem upart_smul (c : F) (w : Ix3 → F) : upart (c • w) = c • upart w := by
  funext i
  fin_cases i <;> rfl

@[expose] def levi2Mat (g : ↥(cayleyGroup F)) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => upart (g2Act g (q6 (if j = 0 then 1 else 0) 0 0 0 0
    (if j = 1 then 1 else 0))) i

theorem levi2Mat_apply (g : ↥(cayleyGroup F)) (i j : Fin 2) :
    levi2Mat g i j = upart (g2Act g (q6 (if j = 0 then 1 else 0) 0 0 0 0
      (if j = 1 then 1 else 0))) i := rfl

omit [CharP F 2] in
theorem q6_F2_decomp (a f : F) :
    q6 a 0 0 0 0 f = a • q6 1 0 0 0 0 0 + f • q6 0 0 0 0 0 1 := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem upart_act (g : ↥(cayleyGroup F)) {w : Ix3 → F} (hw : w ∈ stdF F 2) :
    upart (g2Act g w) = levi2Mat g *ᵥ upart w := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.mp hw
  have hw' : w = q6 (w (.inl 0)) 0 0 0 0 (w (.inr 2)) := by
    conv_lhs => rw [q6_eta w]
    rw [h1, h2, h3, h4]
  rw [hw', q6_F2_decomp, map_add, g2Act_smul, g2Act_smul]
  simp only [upart_add, upart_smul]
  funext i
  fin_cases i <;>
    (simp [upart, levi2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q6]; try ring)

theorem levi2Mat_mul {g h : ↥(cayleyGroup F)} (hh : h ∈ stabQ (stdF F 2)) :
    levi2Mat (g * h) = levi2Mat g * levi2Mat h := by
  ext i j
  have hmem : q6 (if j = 0 then (1 : F) else 0) 0 0 0 0 (if j = 1 then 1 else 0) ∈ stdF F 2 :=
    mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  have e1 : levi2Mat (g * h) i j =
      upart (g2Act g (g2Act h (q6 (if j = 0 then 1 else 0) 0 0 0 0
        (if j = 1 then 1 else 0)))) i := by
    rw [← g2Act_mul_apply]
    rfl
  rw [e1, upart_act g ((mem_stabQ.mp hh _).mp hmem), Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem levi2Mat_one : levi2Mat (1 : ↥(cayleyGroup F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levi2Mat, upart, q6, AddMonoid.End.coe_one]

@[expose] def stabQ2Det (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) where
  carrier := {g | g ∈ stabQ (stdF F 2) ∧ (levi2Mat g).det = 1}
  one_mem' := ⟨(stabQ (stdF F 2)).one_mem, by rw [levi2Mat_one, det_one]⟩
  mul_mem' := fun {a b} ha hb => ⟨(stabQ (stdF F 2)).mul_mem ha.1 hb.1, by
    rw [levi2Mat_mul hb.1, det_mul, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨(stabQ (stdF F 2)).inv_mem ha.1, by
    have h := levi2Mat_mul (g := a) ((stabQ (stdF F 2)).inv_mem ha.1)
    rw [mul_inv_cancel, levi2Mat_one] at h
    have h2 := congrArg Matrix.det h
    rw [det_one, det_mul, ha.2, one_mul] at h2
    exact h2.symm⟩

theorem det_levi2Mat_inv {a : ↥(cayleyGroup F)} (ha : a ∈ stabQ (stdF F 2)) :
    (levi2Mat a).det * (levi2Mat a⁻¹).det = 1 := by
  have h := levi2Mat_mul (g := a) ((stabQ (stdF F 2)).inv_mem ha)
  rw [mul_inv_cancel, levi2Mat_one] at h
  have h2 := congrArg Matrix.det h
  rw [det_one, det_mul] at h2
  exact h2.symm

theorem commutator_stabQ_two_le : ⁅stabQ (stdF F 2), stabQ (stdF F 2)⁆ ≤ stabQ2Det F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅a, b⁆ ∈ stabQ (stdF F 2) :=
    Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha hb)
  refine ⟨hab, ?_⟩
  have hai := (stabQ (stdF F 2)).inv_mem ha
  have hbi := (stabQ (stdF F 2)).inv_mem hb
  rw [commutatorElement_def, levi2Mat_mul hbi, levi2Mat_mul hai, levi2Mat_mul hb, det_mul,
    det_mul, det_mul]
  have e1 := det_levi2Mat_inv ha
  have e2 := det_levi2Mat_inv hb
  linear_combination (levi2Mat b).det * (levi2Mat b⁻¹).det * e1 + e2

theorem perfectCore_stabQ_two_le : perfectCore (stabQ (stdF F 2)) ≤ stabQ2Det F :=
  (perfectCore_le_derivedSeriesOf _ 1).trans commutator_stabQ_two_le

@[expose] noncomputable def levi2 :
    ↥(perfectCore (stabQ (stdF F 2))) →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨levi2Mat g.1, (perfectCore_stabQ_two_le g.2).2⟩
  map_one' := Subtype.ext levi2Mat_one
  map_mul' _ h := Subtype.ext (levi2Mat_mul (perfectCore_le _ h.2))

theorem levi2_apply (g : ↥(perfectCore (stabQ (stdF F 2)))) :
    ((levi2 g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = levi2Mat g.1 := rfl

theorem levi2Mat_x1 (t : F) : levi2Mat (g2X ![0, t, 0]) = !![1, 0; t, 1] := by
  ext i j
  rw [levi2Mat_apply, g2Act_x1q]
  fin_cases i <;> fin_cases j <;> simp [upart, q6]

theorem levi2Mat_y1 (t : F) : levi2Mat (g2Y ![0, t, 0]) = !![1, t; 0, 1] := by
  ext i j
  rw [levi2Mat_apply, g2Act_y1q]
  fin_cases i <;> fin_cases j <;> simp [upart, q6]

theorem levi2_surjective [Finite F] (h4 : 4 ≤ Nat.card F) :
    Function.Surjective (levi2 (F := F)) := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (by omega : 2 < Nat.card F)
  have hle : sl2E1 F ≤ perfectCore (stabQ (stdF F 2)) :=
    le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0 hc1)
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine ⟨⟨g2Y ![0, t, 0], hle (Subgroup.subset_closure ⟨t, Or.inr rfl⟩)⟩, Subtype.ext ?_⟩
    rw [levi2_apply, levi2Mat_y1, CFSG.LinearGroups.coe_transvection]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · refine ⟨⟨g2X ![0, t, 0], hle (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)⟩, Subtype.ext ?_⟩
    rw [levi2_apply, levi2Mat_x1, CFSG.LinearGroups.coe_transvection]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · exact absurd rfl hij

theorem adj_row2 {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 1 = (A : Matrix (Fin 3) (Fin 3) F) 2 1 ∧
      adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 1 1 := by
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  refine ⟨?_, ?_, ?_⟩ <;> simp [adjugate_fin_three, a0, a1, a2, CharTwo.neg_eq]

theorem act_v2_decomp (α β γ : F) {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A) (q6 0 0 0 0 0 1) =
      q6 (β * (A : Matrix (Fin 3) (Fin 3) F) 1 1 + γ * (A : Matrix (Fin 3) (Fin 3) F) 2 1) 0 0 0
        ((A : Matrix (Fin 3) (Fin 3) F) 2 1) ((A : Matrix (Fin 3) (Fin 3) F) 1 1) := by
  obtain ⟨d0, d1, d2⟩ := adj_row2 hA
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_g2A, d0, d1, d2, g2Act_y12q, g2Act_x0q]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem ker_levi2_le {g : ↥(perfectCore (stabQ (stdF F 2)))} (hg : levi2 g = 1) :
    g.1 ∈ U0 F := by
  obtain ⟨g, hgP⟩ := g
  have hgP2 : g ∈ stabQ (stdF F 2) := perfectCore_le _ hgP
  have hM : levi2Mat g = 1 := by
    have h1 := congrArg (fun N : SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F))
      hg
    simpa only [levi2_apply, Matrix.SpecialLinearGroup.coe_one] using h1
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp [levi2Mat, upart] at h00 h01 h10 h11
  have hu : g ∈ stabV0 F := by
    have hmem : q6 (1 : F) 0 0 0 0 0 ∈ stdF F 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp ((mem_stabQ.mp hgP2 _).mp hmem)
    rw [mem_stabV0, eu_eq_q6, q6_eta (g2Act g (q6 1 0 0 0 0 0)), h00, b1, b2, b3, b4, h10]
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hu
  have hmem2 : q6 (0 : F) 0 0 0 0 1 ∈ stdF F 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨-, -, -, c4⟩ := mem_stdF_two.mp ((mem_stabQ.mp hgP2 _).mp hmem2)
  rw [act_v2_decomp α β γ hA] at h01 h11 c4
  simp [q6] at h01 h11 c4
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := det_block_of_fix hA
  rw [h11, c4] at hdet
  have hA22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by linear_combination hdet
  rw [h11, c4] at h01
  have hβ : β = 0 := by simpa using h01
  subst hβ
  have hAu : A = uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1)
      ((A : Matrix (Fin 3) (Fin 3) F) 0 2) ((A : Matrix (Fin 3) (Fin 3) F) 1 2) := by
    apply Subtype.ext
    have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1) ((A : Matrix (Fin 3) (Fin 3) F) 0 2)
        ((A : Matrix (Fin 3) (Fin 3) F) 1 2) : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (A : Matrix (Fin 3) (Fin 3) F) 0 1, (A : Matrix (Fin 3) (Fin 3) F) 0 2;
          0, 1, (A : Matrix (Fin 3) (Fin 3) F) 1 2; 0, 0, 1] := rfl
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, h11, c4, hA22]
  change g2X ![α, 0, 0] * g2Y ![0, 0, γ] * g2A A ∈ U0 F
  rw [hAu]
  exact (U0 F).mul_mem ((U0 F).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 0 γ)) (g2A_mem_U0 _ _ _)

theorem isPGroup_ker_levi2 : IsPGroup 2 ↥(levi2 (F := F)).ker := by
  intro x
  obtain ⟨k, hk⟩ := isPGroup_U0 (F := F) ⟨x.1.1, ker_levi2_le (MonoidHom.mem_ker.mp x.2)⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8
