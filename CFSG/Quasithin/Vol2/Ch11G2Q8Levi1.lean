module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Par1

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

@[expose] def MapsF3 (g : ↥(cayleyGroup F)) : Prop := ∀ w ∈ stdF F 3, g2Act g w ∈ stdF F 3

omit [CharP F 2] in
theorem mem_stdF_three {w : Ix3 → F} :
    w ∈ stdF F 3 ↔ w (.inl 1) = 0 ∧ w (.inl 2) = 0 ∧ w (.inr 0) = 0 := by
  rw [mem_stdF]
  conv_lhs => rw [q6_eta w]
  rw [inF_q6_iff]
  constructor
  · rintro ⟨-, h1, h2, h3, -, -⟩
    exact ⟨h1 (by norm_num), h2 (by norm_num), h3 (by norm_num)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, fun _ => h1, fun _ => h2, fun _ => h3, by omega, by omega⟩

theorem mapsF3_mul {g h : ↥(cayleyGroup F)} (hg : MapsF3 g) (hh : MapsF3 h) : MapsF3 (g * h) :=
  fun w hw => by
    rw [g2Act_mul_apply]
    exact hg _ (hh w hw)

theorem mapsF3_g2X (α : F) : MapsF3 (g2X ![α, 0, 0]) := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  rw [q6_eta w, g2Act_x0q, mem_stdF_three]
  simp [q6, h1, h2, h3]

theorem mapsF3_g2Y (β γ : F) : MapsF3 (g2Y ![0, β, γ]) := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  rw [q6_eta w, g2Act_y12q, mem_stdF_three]
  simp [q6, h1, h2, h3]

omit [CharP F 2] in
theorem adj_col0 {A : SL3 F} (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  have h2 := congrFun hA 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem mapsF3_g2A {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) : MapsF3 (g2A A) := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  rw [q6_eta w, g2Act_g2A, mem_stdF_three]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  rw [h1, h2, h3, a1, a2, adjugate_fin_three]
  simp [a1, a2]

theorem mapsF3_of_mem {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) : MapsF3 g := by
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hg
  exact mapsF3_mul (mapsF3_mul (mapsF3_g2X α) (mapsF3_g2Y β γ)) (mapsF3_g2A hA)

theorem stabV0_le_stabQ_three : stabV0 F ≤ stabQ (stdF F 3) := fun g hg =>
  mem_stabQ.mpr fun w => ⟨mapsF3_of_mem hg w, fun h => by
    have h1 := mapsF3_of_mem ((stabV0 F).inv_mem hg) _ h
    rwa [g2Act_inv_apply] at h1⟩

@[expose] def vpart (w : Ix3 → F) : Fin 2 → F := ![w (.inr 1), w (.inr 2)]

omit [CharP F 2] in
theorem vpart_add (w w' : Ix3 → F) : vpart (w + w') = vpart w + vpart w' := by
  funext i
  fin_cases i <;> rfl

omit [CharP F 2] in
theorem vpart_smul (c : F) (w : Ix3 → F) : vpart (c • w) = c • vpart w := by
  funext i
  fin_cases i <;> rfl

@[expose] def levi1Mat (g : ↥(cayleyGroup F)) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => vpart (g2Act g (q6 0 0 0 0 (if j = 0 then 1 else 0)
    (if j = 1 then 1 else 0))) i

theorem levi1Mat_apply (g : ↥(cayleyGroup F)) (i j : Fin 2) :
    levi1Mat g i j = vpart (g2Act g (q6 0 0 0 0 (if j = 0 then 1 else 0)
      (if j = 1 then 1 else 0))) i := rfl

omit [CharP F 2] in
theorem q6_F3_decomp (a e f : F) :
    q6 a 0 0 0 e f = a • eu 0 1 + (e • q6 0 0 0 0 1 0 + f • q6 0 0 0 0 0 1) := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem vpart_act {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) {w : Ix3 → F}
    (hw : w ∈ stdF F 3) : vpart (g2Act g w) = levi1Mat g *ᵥ vpart w := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  have hw' : w = q6 (w (.inl 0)) 0 0 0 (w (.inr 1)) (w (.inr 2)) := by
    conv_lhs => rw [q6_eta w]
    rw [h1, h2, h3]
  rw [hw', q6_F3_decomp, map_add, map_add, g2Act_smul, g2Act_smul, g2Act_smul,
    show g2Act g (eu 0 1) = eu 0 1 from hg]
  simp only [vpart_add, vpart_smul]
  funext i
  fin_cases i <;>
    (simp [vpart, levi1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q6]; try ring)

theorem levi1Mat_mul {g h : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) (hh : h ∈ stabV0 F) :
    levi1Mat (g * h) = levi1Mat g * levi1Mat h := by
  ext i j
  have hmem : q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) ∈ stdF F 3 :=
    mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have e1 : levi1Mat (g * h) i j =
      vpart (g2Act g (g2Act h (q6 0 0 0 0 (if j = 0 then 1 else 0)
        (if j = 1 then 1 else 0)))) i := by
    rw [← g2Act_mul_apply]
    rfl
  rw [e1, vpart_act hg (mapsF3_of_mem hh _ hmem), Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem levi1Mat_one : levi1Mat (1 : ↥(cayleyGroup F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levi1Mat, vpart, q6, AddMonoid.End.coe_one]

theorem levi1Mat_g2A {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    levi1Mat (g2A A) = !![(A : Matrix (Fin 3) (Fin 3) F) 2 2, (A : Matrix (Fin 3) (Fin 3) F) 2 1;
      (A : Matrix (Fin 3) (Fin 3) F) 1 2, (A : Matrix (Fin 3) (Fin 3) F) 1 1] := by
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  ext i j
  rw [levi1Mat_apply, g2Act_g2A]
  fin_cases i <;> fin_cases j <;>
    simp [vpart, q6, adjugate_fin_three, a0, a1, a2, CharTwo.neg_eq]

theorem levi1Mat_g2X (α : F) : levi1Mat (g2X ![α, 0, 0]) = 1 := by
  ext i j
  rw [levi1Mat_apply, g2Act_x0q]
  fin_cases i <;> fin_cases j <;> simp [vpart, q6]

theorem levi1Mat_g2Y (β γ : F) : levi1Mat (g2Y ![0, β, γ]) = 1 := by
  ext i j
  rw [levi1Mat_apply, g2Act_y12q]
  fin_cases i <;> fin_cases j <;> simp [vpart, q6]

theorem levi1Mat_decomp {α β γ : F} {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    levi1Mat (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A) = levi1Mat (g2A A) := by
  rw [levi1Mat_mul ((stabV0 F).mul_mem (g2X_e0_mem_stabV0 α) (g2Y_mem_stabV0 β γ))
    (g2A_mem_stabV0 hA), levi1Mat_mul (g2X_e0_mem_stabV0 α) (g2Y_mem_stabV0 β γ),
    levi1Mat_g2X, levi1Mat_g2Y, one_mul, one_mul]

omit [CharP F 2] in
theorem det_block_of_fix {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 1 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 -
      (A : Matrix (Fin 3) (Fin 3) F) 1 2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 1 := by
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := A.2
  rw [det_fin_three, a0, a1, a2] at hdet
  linear_combination hdet

theorem det_levi1Mat {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) : (levi1Mat g).det = 1 := by
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hg
  rw [levi1Mat_decomp hA, levi1Mat_g2A hA, det_fin_two_of]
  linear_combination det_block_of_fix hA

@[expose] noncomputable def levi1 : ↥(stabV0 F) →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨levi1Mat g.1, det_levi1Mat g.2⟩
  map_one' := Subtype.ext levi1Mat_one
  map_mul' g h := Subtype.ext (levi1Mat_mul g.2 h.2)

theorem levi1_apply (g : ↥(stabV0 F)) :
    ((levi1 g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = levi1Mat g.1 := rfl

@[expose] def blockSL (N : SpecialLinearGroup (Fin 2) F) : SL3 F :=
  ⟨!![1, 0, 0; 0, (N : Matrix (Fin 2) (Fin 2) F) 1 1, (N : Matrix (Fin 2) (Fin 2) F) 1 0;
    0, (N : Matrix (Fin 2) (Fin 2) F) 0 1, (N : Matrix (Fin 2) (Fin 2) F) 0 0], by
    have h := N.2
    rw [det_fin_two] at h
    simp [det_fin_three]
    linear_combination h⟩

omit [CharP F 2] in
theorem blockSL_mulVec_e0 (N : SpecialLinearGroup (Fin 2) F) :
    ((blockSL N : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [blockSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem levi1_surjective : Function.Surjective (levi1 (F := F)) := by
  intro N
  refine ⟨⟨g2A (blockSL N), g2A_mem_stabV0 (blockSL_mulVec_e0 N)⟩, Subtype.ext ?_⟩
  rw [levi1_apply, levi1Mat_g2A (blockSL_mulVec_e0 N)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockSL]

theorem ker_levi1_le {g : ↥(stabV0 F)} (hg : levi1 g = 1) : g.1 ∈ U0 F := by
  obtain ⟨g, hgS⟩ := g
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hgS
  have hM : levi1Mat (g2A A) = 1 := by
    have h1 := congrArg (fun N : SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F))
      hg
    simp only [levi1_apply, Matrix.SpecialLinearGroup.coe_one] at h1
    rw [← levi1Mat_decomp hA]
    exact h1
  rw [levi1Mat_g2A hA] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp at e00 e01 e10 e11
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hAu : A = uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1)
      ((A : Matrix (Fin 3) (Fin 3) F) 0 2) 0 := by
    apply Subtype.ext
    have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) F) 0 1) ((A : Matrix (Fin 3) (Fin 3) F) 0 2) 0 :
        SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, (A : Matrix (Fin 3) (Fin 3) F) 0 1,
          (A : Matrix (Fin 3) (Fin 3) F) 0 2; 0, 1, 0; 0, 0, 1] := rfl
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, e00, e01, e10, e11]
  change g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A ∈ U0 F
  rw [hAu]
  exact (U0 F).mul_mem ((U0 F).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 β γ)) (g2A_mem_U0 _ _ _)

theorem isPGroup_ker_levi1 : IsPGroup 2 ↥(levi1 (F := F)).ker := by
  intro x
  obtain ⟨k, hk⟩ := isPGroup_U0 (F := F) ⟨x.1.1, ker_levi1_le (MonoidHom.mem_ker.mp x.2)⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8
