module

public import CFSG.RankThree.PartOne.S13K.Sp6Lin
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG.RankThree.PartOne.KFQ

open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def UPres (g : AutV K) : Prop :=
  (∀ u : QV K (Fin 3), u 2 = 0 → g u 2 = 0) ∧
    ∀ (c : Qext K) (u : QV K (Fin 3)), u 2 = 0 → g (c • u) = c • g u

@[expose] noncomputable def dMat (g : AutV K) : Matrix (Fin 2) (Fin 2) (Qext K) :=
  !![g (sg 0 1) 0, g (sg 1 1) 0; g (sg 0 1) 1, g (sg 1 1) 1]

theorem decomp_U (u : QV K (Fin 3)) (hu : u 2 = 0) : u = u 0 • sg 0 1 + u 1 • sg 1 1 := by
  funext i
  fin_cases i <;> simp [hu]

theorem UPres_apply0 {g : AutV K} (hg : UPres g) {u : QV K (Fin 3)} (hu : u 2 = 0) :
    g u 0 = dMat g 0 0 * u 0 + dMat g 0 1 * u 1 := by
  have h1 : g u = u 0 • g (sg 0 1) + u 1 • g (sg 1 1) := by
    conv_lhs => rw [decomp_U u hu]
    rw [map_add, hg.2 _ _ (by simp), hg.2 _ _ (by simp)]
  rw [h1]
  simp [dMat, mul_comm]

theorem UPres_apply1 {g : AutV K} (hg : UPres g) {u : QV K (Fin 3)} (hu : u 2 = 0) :
    g u 1 = dMat g 1 0 * u 0 + dMat g 1 1 * u 1 := by
  have h1 : g u = u 0 • g (sg 0 1) + u 1 • g (sg 1 1) := by
    conv_lhs => rw [decomp_U u hu]
    rw [map_add, hg.2 _ _ (by simp), hg.2 _ _ (by simp)]
  rw [h1]
  simp [dMat, mul_comm]

theorem UPres_one : UPres (1 : AutV K) :=
  ⟨fun _ hu => hu, fun _ _ _ => rfl⟩

theorem UPres_mul {g h : AutV K} (hg : UPres g) (hh : UPres h) : UPres (g * h) :=
  ⟨fun u hu => hg.1 _ (hh.1 u hu), fun c u hu => by
    change g (h (c • u)) = c • g (h u)
    rw [hh.2 c u hu, hg.2 c _ (hh.1 u hu)]⟩

theorem dMat_one : dMat (1 : AutV K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMat]

theorem dMat_mul {g h : AutV K} (hg : UPres g) (hh : UPres h) : dMat (g * h) = dMat g * dMat h := by
  have hs0 : (h (sg 0 1)) 2 = 0 := hh.1 _ (by simp)
  have hs1 : (h (sg 1 1)) 2 = 0 := hh.1 _ (by simp)
  ext a b
  fin_cases a <;> fin_cases b
  · have := UPres_apply0 hg hs0
    simpa [dMat, Matrix.mul_apply, Fin.sum_univ_two] using this
  · have := UPres_apply0 hg hs1
    simpa [dMat, Matrix.mul_apply, Fin.sum_univ_two] using this
  · have := UPres_apply1 hg hs0
    simpa [dMat, Matrix.mul_apply, Fin.sum_univ_two] using this
  · have := UPres_apply1 hg hs1
    simpa [dMat, Matrix.mul_apply, Fin.sum_univ_two] using this


theorem UPres_symm {g : AutV K} (hg : UPres g) (hfix : ∀ a, g (sg 2 a) = sg 2 a) :
    UPres g.symm := by
  have hU : ∀ u : QV K (Fin 3), u 2 = 0 → g.symm u 2 = 0 := by
    intro u hu
    set w := g.symm u with hw
    have hwu : g w = u := by rw [hw, LinearEquiv.apply_symm_apply]
    have h1 : (w - sg 2 (w 2)) 2 = 0 := by simp
    have h2 := hg.1 _ h1
    have h3 : g w 2 = w 2 := by
      calc g w 2 = g ((w - sg 2 (w 2)) + sg 2 (w 2)) 2 := by rw [sub_add_cancel]
        _ = g (w - sg 2 (w 2)) 2 + g (sg 2 (w 2)) 2 := by rw [map_add]; rfl
        _ = w 2 := by rw [h2, hfix]; simp
    rw [hwu] at h3
    rw [← h3, hu]
  refine ⟨hU, fun c u hu => ?_⟩
  have hw := hU u hu
  rw [LinearEquiv.symm_apply_eq]
  rw [hg.2 c _ hw, LinearEquiv.apply_symm_apply]

@[expose] def dBlk (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup ↥(M10 K) where
  carrier := {g | (∀ a : Qext K, g.1 (sg 2 a) = sg 2 a) ∧ UPres g.1 ∧ (dMat g.1).det = 1}
  mul_mem' {g h} hg hh := by
    obtain ⟨hg1, hg2, hg3⟩ := hg
    obtain ⟨hh1, hh2, hh3⟩ := hh
    refine ⟨fun a => ?_, UPres_mul hg2 hh2, ?_⟩
    · change g.1 (h.1 (sg 2 a)) = _
      rw [hh1, hg1]
    · change (dMat (g.1 * h.1)).det = 1
      rw [dMat_mul hg2 hh2, Matrix.det_mul, hg3, hh3, one_mul]
  one_mem' := ⟨fun a => rfl, UPres_one, by simp [show dMat (1 : AutV K) = 1 from dMat_one]⟩
  inv_mem' {g} hg := by
    obtain ⟨hg1, hg2, hg3⟩ := hg
    have hs : UPres g.1.symm := UPres_symm hg2 hg1
    refine ⟨fun a => ?_, hs, ?_⟩
    · change g.1.symm (sg 2 a) = _
      rw [LinearEquiv.symm_apply_eq, hg1]
    · have h1 : dMat (g.1.symm * g.1) = dMat g.1.symm * dMat g.1 := dMat_mul hs hg2
      have h2 : g.1.symm * g.1 = 1 := by
        refine LinearEquiv.ext fun v => ?_
        simp
      rw [h2, dMat_one] at h1
      have h3 := congrArg Matrix.det h1
      rw [Matrix.det_mul, hg3, mul_one, Matrix.det_one] at h3
      change (dMat g.1.symm).det = 1
      exact h3.symm

theorem mem_dBlk_iff {g : ↥(M10 K)} : g ∈ dBlk K ↔
    (∀ a : Qext K, g.1 (sg 2 a) = sg 2 a) ∧ UPres g.1 ∧ (dMat g.1).det = 1 := Iff.rfl

theorem trQ_pairing_zero {d : Qext K} (h : ∀ c, trQ (c * d) = 0) : d = 0 := by
  by_contra hd
  obtain ⟨y, hy⟩ : ∃ y : Qext K, trQ y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact trQ_ne_zero (LinearMap.ext hall)
  apply hy
  have := h (y * d⁻¹)
  rwa [mul_assoc, inv_mul_cancel₀ hd, mul_one] at this

theorem formQ_U {x y : QV K (Fin 3)} (hx : x 2 = 0) (hy : y 2 = 0) :
    formQ K x y = trQ (x 0 * frobQ K (y 0) + x 1 * frobQ K (y 1)) := by
  rw [formQ_apply, hx, hy, qForm_apply, qForm_apply, qForm_apply, map_zero, mul_zero, map_zero,
    add_zero, map_add]

theorem dMat_transpose_mul {g : AutV K} (hg : g ∈ M10 K) (hU : UPres g) :
    (dMat g)ᵀ * (dMat g).map (frobQ K) = 1 := by
  have key : ∀ (k j : Fin 2), ∀ c : Qext K, trQ (c * ((dMat g)ᵀ * (dMat g).map (frobQ K)) k j) =
      trQ (c * (1 : Matrix (Fin 2) (Fin 2) (Qext K)) k j) := by
    intro k j c
    have hk : ∀ k : Fin 2, ∃ u : QV K (Fin 3), u 2 = 0 ∧ u 0 = (if k = 0 then c else 0) ∧
        u 1 = (if k = 1 then c else 0) := by
      intro k
      fin_cases k
      · exact ⟨sg 0 c, by simp, by simp, by simp⟩
      · exact ⟨sg 1 c, by simp, by simp, by simp⟩
    have hj : ∀ j : Fin 2, ∃ w : QV K (Fin 3), w 2 = 0 ∧ w 0 = (if j = 0 then 1 else 0) ∧
        w 1 = (if j = 1 then 1 else 0) := by
      intro j
      fin_cases j
      · exact ⟨sg 0 1, by simp, by simp, by simp⟩
      · exact ⟨sg 1 1, by simp, by simp, by simp⟩
    obtain ⟨u, hu2, hu0, hu1⟩ := hk k
    obtain ⟨w, hw2, hw0, hw1⟩ := hj j
    have h1 := formQ_map hg u w
    have hgu2 := hU.1 u hu2
    have hgw2 := hU.1 w hw2
    rw [formQ_U hgu2 hgw2, formQ_U hu2 hw2, UPres_apply0 hU hu2, UPres_apply1 hU hu2,
      UPres_apply0 hU hw2, UPres_apply1 hU hw2, hu0, hu1, hw0, hw1] at h1
    fin_cases k <;> fin_cases j
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_two,
        Matrix.one_apply_eq] at h1 ⊢
      simp at h1 ⊢
      rw [← h1]
      rw [← map_add]
      congr 1
      ring
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_two] at h1 ⊢
      simp at h1 ⊢
      rw [← h1]
      rw [← map_add]
      congr 1
      ring
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_two] at h1 ⊢
      simp at h1 ⊢
      rw [← h1]
      rw [← map_add]
      congr 1
      ring
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_two] at h1 ⊢
      simp at h1 ⊢
      rw [← h1]
      rw [← map_add]
      congr 1
      ring
  ext k j
  have := trQ_pairing_zero (d := ((dMat g)ᵀ * (dMat g).map (frobQ K)) k j - (1 : Matrix (Fin 2) (Fin 2) (Qext K)) k j)
    (fun c => by rw [mul_sub, map_sub, key k j c, sub_self])
  exact sub_eq_zero.mp this

theorem unitaryFieldData_qext {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f (Qext K) := by
  refine ⟨Nat.prime_two, hf, ?_⟩
  rw [FiniteField.natCard_extension K 2 2, hK, ← pow_mul, mul_comm]

theorem bar_eq_frobQ {f : ℕ} (hK : Nat.card K = 2 ^ f) (h : UnitaryFieldData 2 f (Qext K))
    (x : Qext K) : h.bar x = frobQ K x := by
  rw [UnitaryFieldData.bar_apply, frobQ_apply, hK]

@[expose] noncomputable def dBlkToSL : ↥(dBlk K) →* Matrix.SpecialLinearGroup (Fin 2) (Qext K) where
  toFun g := ⟨dMat g.1.1, g.2.2.2⟩
  map_one' := Subtype.ext dMat_one
  map_mul' g h := Subtype.ext (dMat_mul g.2.2.1 h.2.2.1)

theorem dBlkToSL_coe (g : ↥(dBlk K)) : ((dBlkToSL g : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    Matrix (Fin 2) (Fin 2) (Qext K)) = dMat g.1.1 := rfl

theorem dBlkToSL_injective : Function.Injective (dBlkToSL : ↥(dBlk K) →* _) := by
  intro g g' hgg
  have hM : dMat g.1.1 = dMat g'.1.1 := by
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (Qext K) =>
      (A : Matrix (Fin 2) (Fin 2) (Qext K))) hgg
    simpa [dBlkToSL_coe] using this
  have hcol : ∀ b : Fin 2, ∀ a : Qext K, g.1.1 (sg (b.castSucc) a) = g'.1.1 (sg (b.castSucc) a) := by
    intro b a
    have hs : sg (b.castSucc) a = a • sg (b.castSucc) 1 := by
      funext i
      by_cases h : i = b.castSucc
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    have hs2 : (sg (b.castSucc) (1 : Qext K)) 2 = 0 := by
      fin_cases b <;> simp
    rw [hs, g.2.2.1.2 _ _ hs2, g'.2.2.1.2 _ _ hs2]
    congr 1
    funext i
    fin_cases i
    · have := congrFun₂ hM 0 b
      fin_cases b <;> simpa [dMat] using this
    · have := congrFun₂ hM 1 b
      fin_cases b <;> simpa [dMat] using this
    · exact (g.2.2.1.1 _ hs2).trans (g'.2.2.1.1 _ hs2).symm
  apply Subtype.ext
  apply Subtype.ext
  refine autV_ext_sg (fun a => hcol 0 a) (fun a => hcol 1 a) (fun a => ?_)
  rw [g.2.1, g'.2.1]

@[expose] noncomputable def dLin (A : Matrix (Fin 2) (Fin 2) (Qext K)) :
    QV K (Fin 3) →ₗ[K] QV K (Fin 3) where
  toFun v := ![A 0 0 * v 0 + A 0 1 * v 1, A 1 0 * v 0 + A 1 1 * v 1, v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [Algebra.smul_def] <;> ring

theorem dLin_apply0 (A : Matrix (Fin 2) (Fin 2) (Qext K)) (v : QV K (Fin 3)) :
    dLin A v 0 = A 0 0 * v 0 + A 0 1 * v 1 := rfl

theorem dLin_apply1 (A : Matrix (Fin 2) (Fin 2) (Qext K)) (v : QV K (Fin 3)) :
    dLin A v 1 = A 1 0 * v 0 + A 1 1 * v 1 := rfl

theorem dLin_apply2 (A : Matrix (Fin 2) (Fin 2) (Qext K)) (v : QV K (Fin 3)) :
    dLin A v 2 = v 2 := rfl

theorem dLin_mul (A B : Matrix (Fin 2) (Fin 2) (Qext K)) : dLin (A * B) = dLin A ∘ₗ dLin B := by
  refine LinearMap.ext fun v => ?_
  funext i
  fin_cases i <;> simp [dLin, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem dLin_one : dLin (1 : Matrix (Fin 2) (Fin 2) (Qext K)) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  funext i
  fin_cases i <;> simp [dLin]

@[expose] noncomputable def dRho (A : GL (Fin 2) (Qext K)) : AutV K :=
  LinearEquiv.ofLinearMap (dLin (A : Matrix (Fin 2) (Fin 2) (Qext K)))
    (dLin ((A⁻¹ : GL (Fin 2) (Qext K)) : Matrix (Fin 2) (Fin 2) (Qext K)))
    (by rw [← dLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, dLin_one])
    (by rw [← dLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, dLin_one])

theorem dRho_apply0 (A : GL (Fin 2) (Qext K)) (v : QV K (Fin 3)) :
    dRho A v 0 = (A : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0 * v 0 +
      (A : Matrix (Fin 2) (Fin 2) (Qext K)) 0 1 * v 1 := rfl

theorem dRho_apply1 (A : GL (Fin 2) (Qext K)) (v : QV K (Fin 3)) :
    dRho A v 1 = (A : Matrix (Fin 2) (Fin 2) (Qext K)) 1 0 * v 0 +
      (A : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1 * v 1 := rfl

theorem dRho_apply2 (A : GL (Fin 2) (Qext K)) (v : QV K (Fin 3)) : dRho A v 2 = v 2 := rfl

theorem dRho_fix2 (A : GL (Fin 2) (Qext K)) (a : Qext K) : dRho A (sg 2 a) = sg 2 a := by
  funext i
  fin_cases i <;> simp [dRho_apply0, dRho_apply1, dRho_apply2]

theorem dRho_UPres (A : GL (Fin 2) (Qext K)) : UPres (dRho A) := by
  refine ⟨fun u hu => by rw [dRho_apply2]; exact hu, fun c u hu => ?_⟩
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, dRho_apply0, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Fin.mk_one, dRho_apply1, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Fin.reduceFinMk, dRho_apply2, Pi.smul_apply]

theorem dMat_dRho (A : GL (Fin 2) (Qext K)) : dMat (dRho A) = (A : Matrix (Fin 2) (Fin 2) (Qext K)) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMat, dRho_apply0, dRho_apply1]

theorem dRho_mem_M10 {A : GL (Fin 2) (Qext K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) (Qext K))ᵀ *
      (A : Matrix (Fin 2) (Fin 2) (Qext K)).map (frobQ K) = 1) : dRho A ∈ M10 K := by
  have e : ∀ k j : Fin 2, ∑ a, (A : Matrix (Fin 2) (Fin 2) (Qext K)) a k *
      frobQ K ((A : Matrix (Fin 2) (Fin 2) (Qext K)) a j) = if k = j then 1 else 0 := by
    intro k j
    have := congrFun₂ hA k j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Fin.sum_univ_two, ite_true, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, ite_false] at e00 e01 e10 e11
  rw [mem_M10_iff']
  intro x y
  simp only [dRho_apply0, dRho_apply1, dRho_apply2, qForm_apply]
  rw [← map_add, ← map_add, ← map_add, ← map_add]
  congr 1
  simp only [map_add, map_mul]
  linear_combination (x 0 * frobQ K (y 0)) * e00 + (x 0 * frobQ K (y 1)) * e01 +
    (x 1 * frobQ K (y 0)) * e10 + (x 1 * frobQ K (y 1)) * e11

@[expose] noncomputable def dBlkToGL : ↥(dBlk K) →* GL (Fin 2) (Qext K) :=
  Matrix.SpecialLinearGroup.toGL.comp dBlkToSL

theorem dBlkToGL_coe (g : ↥(dBlk K)) :
    ((dBlkToGL g : GL (Fin 2) (Qext K)) : Matrix (Fin 2) (Fin 2) (Qext K)) = dMat g.1.1 := rfl

theorem dBlkToGL_mem {f : ℕ} (hK : Nat.card K = 2 ^ f) (h : UnitaryFieldData 2 f (Qext K))
    (g : ↥(dBlk K)) : dBlkToGL g ∈ gramSU h (idGram (Qext K) 2) := by
  refine ⟨?_, ?_⟩
  · have h1 := dMat_transpose_mul g.1.2 g.2.2.1
    have h2 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2
    rw [dBlkToGL_coe, show idGram (Qext K) 2 = 1 by simp [idGram]]
    rw [Matrix.mul_one]
    convert h2 using 3
    ext a b
    simp [Matrix.map_apply, bar_eq_frobQ hK h]
  · rw [dBlkToGL_coe]
    exact g.2.2.2

theorem dBlkToGL_injective : Function.Injective (dBlkToGL : ↥(dBlk K) →* _) := by
  intro g g' hgg
  apply dBlkToSL_injective
  apply Subtype.ext
  have := congrArg (fun A : GL (Fin 2) (Qext K) => (A : Matrix (Fin 2) (Fin 2) (Qext K))) hgg
  simpa [dBlkToGL_coe, dBlkToSL_coe] using this

@[expose] noncomputable def dBlkToGram {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (h : UnitaryFieldData 2 f (Qext K)) :
    ↥(dBlk K) →* ↥(gramSU h (idGram (Qext K) 2)) :=
  dBlkToGL.codRestrict _ (dBlkToGL_mem hK h)

theorem dBlkToGram_bijective {f : ℕ} (hK : Nat.card K = 2 ^ f) (h : UnitaryFieldData 2 f (Qext K)) :
    Function.Bijective (dBlkToGram hK h) := by
  constructor
  · intro g g' hgg
    apply dBlkToGL_injective
    have := congrArg (fun B : ↥(gramSU h (idGram (Qext K) 2)) => B.1) hgg
    simpa [dBlkToGram] using this
  · intro B
    obtain ⟨hB1, hB2⟩ := B.2
    obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (Qext K),
        M = ((B.1 : GL (Fin 2) (Qext K)) : Matrix (Fin 2) (Fin 2) (Qext K)) := ⟨_, rfl⟩
    rw [← hMdef] at hB1 hB2
    have hB1' : Mᵀ * M.map (frobQ K) = 1 := by
      have h2 := congrArg Matrix.transpose hB1
      rw [show idGram (Qext K) 2 = 1 by simp [idGram], Matrix.mul_one] at h2
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2
      convert h2 using 2
      ext a b
      simp [Matrix.map_apply, bar_eq_frobQ hK h]
    have hA1 : (B.1 : Matrix (Fin 2) (Fin 2) (Qext K))ᵀ *
        (B.1 : Matrix (Fin 2) (Fin 2) (Qext K)).map (frobQ K) = 1 := by
      rw [← hMdef]
      exact hB1'
    have hmem : dRho B.1 ∈ M10 K := dRho_mem_M10 hA1
    refine ⟨⟨⟨dRho B.1, hmem⟩, fun a => dRho_fix2 B.1 a, dRho_UPres B.1, ?_⟩, ?_⟩
    · change (dMat (dRho B.1)).det = 1
      rw [dMat_dRho, ← hMdef]
      exact hB2
    · apply Subtype.ext
      apply Units.ext
      change dMat (dRho B.1) = _
      rw [dMat_dRho]

@[expose] noncomputable def dBlkEquiv {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (h : UnitaryFieldData 2 f (Qext K)) :
    ↥(dBlk K) ≃* ↥(gramSU h (idGram (Qext K) 2)) :=
  MulEquiv.ofBijective (dBlkToGram hK h) (dBlkToGram_bijective hK h)

theorem dBlk_model {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    CFSG.IsQuasisimple ↥(dBlk K) ∧ Subgroup.center ↥(dBlk K) = ⊥ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(dBlk K) .PSL 2 2 f := by
  have h := unitaryFieldData_qext hK (by omega)
  obtain ⟨e⟩ : Nonempty (↥(dBlk K) ≃* ↥(gramSU h (idGram (Qext K) 2))) := ⟨dBlkEquiv hK h⟩
  obtain ⟨hQ, hZ, F, hF, hFin, hcard, ⟨ψ⟩⟩ := CFSG.RankThree.PartOne.KFU.su2_model h hf
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ,
    by rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot],
    ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, hF, hFin, hcard, ⟨e.trans ψ⟩⟩
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega

theorem autV_ext_U {g h : AutV K} (hU : ∀ u : QV K (Fin 3), u 2 = 0 → g u = h u)
    (h2 : ∀ a, g (sg 2 a) = h (sg 2 a)) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v = (v - sg 2 (v 2)) + sg 2 (v 2) := by rw [sub_add_cancel]
  have h1 : (v - sg 2 (v 2)) 2 = 0 := by simp
  calc g v = g ((v - sg 2 (v 2)) + sg 2 (v 2)) := by rw [← hv]
    _ = h ((v - sg 2 (v 2)) + sg 2 (v 2)) := by rw [map_add, map_add, hU _ h1, h2]
    _ = h v := by rw [← hv]

theorem torusEquiv_U {x : Fin 3 → (Qext K)ˣ} (hx : x 0 = x 1) {u : QV K (Fin 3)} (hu : u 2 = 0) :
    torusEquiv x u = (x 0 : Qext K) • u := by
  funext i
  fin_cases i
  · simp [torusEquiv_apply]
  · simp [torusEquiv_apply, hx]
  · simp [torusEquiv_apply, hu]

theorem dBlk_comm_tor {g : ↥(M10 K)} (hg : g ∈ dBlk K) {x : Fin 3 → (Qext K)ˣ} (hx : x 0 = x 1) :
    g.1 * torusEquiv x = torusEquiv x * g.1 := by
  obtain ⟨hg1, hg2, -⟩ := hg
  refine autV_ext_U (fun u hu => ?_) (fun a => ?_)
  · change g.1 (torusEquiv x u) = torusEquiv x (g.1 u)
    rw [torusEquiv_U hx hu, torusEquiv_U hx (hg2.1 u hu), hg2.2 _ u hu]
  · change g.1 (torusEquiv x (sg 2 a)) = torusEquiv x (g.1 (sg 2 a))
    rw [torusEquiv_sg, hg1, hg1, torusEquiv_sg]

@[expose] def CommTorD (p : ℕ) (m : AutV K) : Prop :=
  ∀ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) → x 0 = x 1 → m * torusEquiv x = torusEquiv x * m

theorem CommTorD.symm {p : ℕ} {m : AutV K} (h : CommTorD p m) : CommTorD p m.symm := by
  intro x hx hx01
  have hm := h x hx hx01
  refine LinearEquiv.ext fun v => ?_
  have h1 := congrArg (fun f : AutV K => f (m.symm v)) hm
  simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h1
  change m.symm (torusEquiv x v) = torusEquiv x (m.symm v)
  rw [LinearEquiv.symm_apply_eq, ← h1]

theorem CommTorD.sg_two {p : ℕ} {m : AutV K} (h : CommTorD p m) {ζ : (Qext K)ˣ} (hζp : ζ ^ p = 1)
    (hζ : ζ ≠ 1) (a : Qext K) : m (sg 2 a) = sg 2 (m (sg 2 a) 2) := by
  have hx : ∀ i, (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζp]
  have hm := h ![ζ, ζ, 1] hx (by simp)
  have hfix : torusEquiv (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) (m (sg 2 a)) = m (sg 2 a) := by
    have := congrArg (fun f : AutV K => f (sg 2 a)) hm
    simp only [LinearEquiv.mul_apply, torusEquiv_sg] at this
    simpa using this.symm
  have hne : ((ζ : (Qext K)ˣ) : Qext K) - 1 ≠ 0 := by
    intro h0
    apply hζ
    apply Units.ext
    simpa [sub_eq_zero] using h0
  have hc : ∀ j : Fin 3, j ≠ 2 → m (sg 2 a) j = 0 := by
    intro j hj
    have := congrFun hfix j
    fin_cases j
    · simp only [torusEquiv_apply] at this
      have h' : ((ζ : (Qext K)ˣ) : Qext K) * m (sg 2 a) 0 = m (sg 2 a) 0 := by simpa using this
      have : (((ζ : (Qext K)ˣ) : Qext K) - 1) * m (sg 2 a) 0 = 0 := by rw [sub_mul, h']; ring
      exact (mul_eq_zero.mp this).resolve_left hne
    · simp only [torusEquiv_apply] at this
      have h' : ((ζ : (Qext K)ˣ) : Qext K) * m (sg 2 a) 1 = m (sg 2 a) 1 := by simpa using this
      have : (((ζ : (Qext K)ˣ) : Qext K) - 1) * m (sg 2 a) 1 = 0 := by rw [sub_mul, h']; ring
      exact (mul_eq_zero.mp this).resolve_left hne
    · exact absurd rfl hj
  funext j
  by_cases hj : j = 2
  · subst hj; simp
  · rw [hc j hj]
    simp [Pi.single_eq_of_ne hj]

theorem CommTorD.U {p : ℕ} {m : AutV K} (h : CommTorD p m) {ζ : (Qext K)ˣ} (hζp : ζ ^ p = 1)
    (hζ : ζ ≠ 1) {u : QV K (Fin 3)} (hu : u 2 = 0) : m u 2 = 0 := by
  have hx : ∀ i, (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζp]
  have hm := h ![ζ, ζ, 1] hx (by simp)
  have hne : ((ζ : (Qext K)ˣ) : Qext K) - 1 ≠ 0 := by
    intro h0
    apply hζ
    apply Units.ext
    simpa [sub_eq_zero] using h0
  set w : QV K (Fin 3) := (((ζ : (Qext K)ˣ) : Qext K) - 1)⁻¹ • u with hw
  have hw2 : w 2 = 0 := by simp [hw, hu]
  have huw : u = torusEquiv (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) w - w := by
    funext i
    fin_cases i
    · simp [hw, torusEquiv_apply]
      field_simp
    · simp [hw, torusEquiv_apply]
      field_simp
    · simp [hw2, torusEquiv_apply, hu]
  have h1 : m (torusEquiv (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) w) =
      torusEquiv (![ζ, ζ, 1] : Fin 3 → (Qext K)ˣ) (m w) := by
    have := congrArg (fun f : AutV K => f w) hm
    simpa using this
  rw [huw, map_sub, h1]
  simp [torusEquiv_apply]

theorem CommTorD.smul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {m : AutV K} (h : CommTorD p m) {ζ : (Qext K)ˣ} (hζp : ζ ^ p = 1) (hζ : ζ ≠ 1)
    (c : Qext K) {u : QV K (Fin 3)} (hu : u 2 = 0) : m (c • u) = c • m u := by
  have hmu := h.U hζp hζ hu
  have hroot : ∀ x : Qext K, x ^ p = 1 → m (x • u) = x • m u := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hx
      exact zero_ne_one hx
    set xu : (Qext K)ˣ := Units.mk0 x hx0 with hxu
    have hxp : xu ^ p = 1 := Units.ext (by simpa [hxu] using hx)
    have hxs : ∀ i, (![xu, xu, 1] : Fin 3 → (Qext K)ˣ) i ^ p = 1 := by
      intro i
      fin_cases i <;> simp [hxp]
    have hm := h ![xu, xu, 1] hxs (by simp)
    have h1 : torusEquiv (![xu, xu, 1] : Fin 3 → (Qext K)ˣ) u = x • u := by
      rw [torusEquiv_U (by simp) hu]
      simp [hxu]
    have h2 : torusEquiv (![xu, xu, 1] : Fin 3 → (Qext K)ˣ) (m u) = x • m u := by
      rw [torusEquiv_U (by simp) hmu]
      simp [hxu]
    have := congrArg (fun f : AutV K => f u) hm
    simp only [LinearEquiv.mul_apply] at this
    rw [h1, h2] at this
    exact this
  have hspan := span_roots_eq_top (K := K) hp hp2 hpq
  have hc : c ∈ Submodule.span K {x : Qext K | x ^ p = 1} := by rw [hspan]; trivial
  induction hc using Submodule.span_induction with
  | mem x hx => exact hroot x hx
  | zero => simp
  | add c₁ c₂ _ _ h₁ h₂ =>
    rw [add_smul, map_add, h₁, h₂, add_smul]
  | smul a c₁ _ h₁ =>
    rw [smul_assoc, map_smul, h₁, ← smul_assoc]

theorem CommTorD.uPres {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {m : AutV K} (h : CommTorD p m) {ζ : (Qext K)ˣ} (hζp : ζ ^ p = 1) (hζ : ζ ≠ 1) : UPres m :=
  ⟨fun _ hu => h.U hζp hζ hu, fun c _ hu => h.smul hp hp2 hpq hζp hζ c hu⟩

theorem dBlk_normalized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {m : ↥(M10 K)} (hm : CommTorD p m.1) {ζ : (Qext K)ˣ} (hζp : ζ ^ p = 1) (hζ : ζ ≠ 1)
    {g : ↥(M10 K)} (hg : g ∈ dBlk K) : m * g * m⁻¹ ∈ dBlk K := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hu : UPres m.1 := hm.uPres hp hp2 hpq hζp hζ
  have hs : UPres m.1.symm := hm.symm.uPres hp hp2 hpq hζp hζ
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have h1 := hm.symm.sg_two hζp hζ a
    change m.1 (g.1 (m.1.symm (sg 2 a))) = sg 2 a
    rw [h1, hg1]
    have := m.1.apply_symm_apply (sg 2 a)
    rw [h1] at this
    exact this
  · exact UPres_mul (UPres_mul hu hg2) hs
  · have hmm : m.1 * m.1.symm = 1 := by
      refine LinearEquiv.ext fun v => ?_
      simp
    have h1 : dMat (m.1 * g.1 * m.1.symm) = dMat m.1 * dMat g.1 * dMat m.1.symm := by
      rw [dMat_mul (UPres_mul hu hg2) hs, dMat_mul hu hg2]
    have h2 : dMat m.1 * dMat m.1.symm = 1 := by
      rw [← dMat_mul hu hs, hmm, dMat_one]
    change (dMat (m.1 * g.1 * m.1.symm)).det = 1
    rw [h1, Matrix.det_mul, Matrix.det_mul, hg3, mul_one]
    have := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact this

end CFSG.RankThree.PartOne.S13K
