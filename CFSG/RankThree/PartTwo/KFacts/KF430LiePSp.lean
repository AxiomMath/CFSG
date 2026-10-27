module

public import CFSG.RankThree.PartTwo.KFacts.KF430LiePCommon
public import CFSG.RankThree.PartTwo.KFacts.KF430LiePSL2
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamSyl
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankTwo
public import CFSG.RankThree.PartTwo.Sec4.E27.Vac
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open Matrix
open CFSG.Open (StatedSp StatedProj)

section Plane

variable {F : Type} [Field F]

@[expose] def planeMat (M N : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (diagonal ![M 0 0, N 0 0]) (diagonal ![M 0 1, N 0 1]) (diagonal ![M 1 0, N 1 0])
    (diagonal ![M 1 1, N 1 1])

theorem planeMat_mul (M N M' N' : Matrix (Fin 2) (Fin 2) F) :
    planeMat M N * planeMat M' N' = planeMat (M * M') (N * N') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem planeMat_one : planeMat (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat]

theorem planeMat_pow (M N : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    planeMat M N ^ n = planeMat (M ^ n) (N ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, planeMat_one]
  | succ n ih => rw [pow_succ, ih, planeMat_mul, ← pow_succ, ← pow_succ]

theorem planeMat_symp {M N : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1) (hN : N.det = 1) :
    (planeMat M N)ᵀ * fromBlocks 0 1 (-1) 0 * planeMat M N = fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hM hN
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hM | linear_combination hN | linear_combination -hM |
      linear_combination -hN

@[expose] def swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]

theorem swapMat_mul_planeMat (M N : Matrix (Fin 2) (Fin 2) F) :
    swapMat * planeMat M N = planeMat N M * swapMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat, swapMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem swapMat_mul_self : swapMat (F := F) * swapMat = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem swapMat_symp :
    (swapMat (F := F))ᵀ * fromBlocks 0 1 (-1) 0 * swapMat = fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

@[expose] def planeGL (M N M' N' : Matrix (Fin 2) (Fin 2) F) (hM : M * M' = 1)
    (hM' : M' * M = 1) (hN : N * N' = 1) (hN' : N' * N = 1) : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨planeMat M N, planeMat M' N', by rw [planeMat_mul, hM, hN, planeMat_one],
    by rw [planeMat_mul, hM', hN', planeMat_one]⟩

@[expose] def swapGL : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

end Plane

section E9

variable {F : Type} [Field F]

theorem eq_zero_of_planeMat_pow_eq_scalar (i j : ZMod 3) (c : F)
    (h : planeMat (uMat ^ i.val) (uMat ^ j.val) = diagonal (fun _ => c)) : i = 0 ∧ j = 0 := by
  have hval : ∀ k : ZMod 3, (uMat (F := F) ^ k.val) 1 0 = 0 → k = 0 := by
    intro k hk
    by_contra hk0
    have hk3 : k.val % 3 ≠ 0 := by
      have : k.val < 3 := ZMod.val_lt k
      have : k.val ≠ 0 := fun h0 => hk0 ((ZMod.val_eq_zero k).1 h0)
      omega
    rcases uMat_pow_apply_one_zero (F := F) k.val hk3 with h1 | h1 <;> rw [h1] at hk <;>
      simp at hk
  have h0 := congrFun (congrFun h (Sum.inr 0)) (Sum.inl 0)
  have h1 := congrFun (congrFun h (Sum.inr 1)) (Sum.inl 1)
  simp [planeMat] at h0 h1
  exact ⟨hval i h0, hval j h1⟩

theorem exists_std_gen (u X X' : Matrix (Fin 2) (Fin 2) F) (hu3 : u ^ 3 = 1) (hXX' : X * X' = 1)
    (hX'X : X' * X = 1) (hXu : X * u = u ^ 2 * X)
    (hind : ∀ (i j : ZMod 3) (c : F),
      planeMat (u ^ i.val) (u ^ j.val) = diagonal (fun _ => c) → i = 0 ∧ j = 0) :
    ∃ a b w : GL (Fin 2 ⊕ Fin 2) F,
      ((a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeMat u 1 ∧
        (b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeMat 1 u ∧
        (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeMat X 1) ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
      (∀ i j : ZMod 3, ∀ c : Fˣ, a ^ i.val * b ^ j.val =
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c → i = 0 ∧ j = 0) ∧
      swapGL * a * swapGL⁻¹ = b ∧ swapGL * b * swapGL⁻¹ = a ∧ w * a * w⁻¹ = a ^ 2 ∧
      w * b * w⁻¹ = b := by
  have huu : u * u ^ 2 = 1 := by rw [← pow_succ', hu3]
  have huu' : u ^ 2 * u = 1 := by rw [← pow_succ, hu3]
  refine ⟨planeGL u 1 (u ^ 2) 1 huu huu' (mul_one 1) (mul_one 1),
    planeGL 1 u 1 (u ^ 2) (mul_one 1) (mul_one 1) huu huu',
    planeGL X 1 X' 1 hXX' hX'X (mul_one 1) (mul_one 1), ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change planeMat u 1 ^ 3 = 1
    rw [planeMat_pow, hu3, one_pow, planeMat_one]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change planeMat 1 u ^ 3 = 1
    rw [planeMat_pow, hu3, one_pow, planeMat_one]
  · apply Units.ext
    change planeMat u 1 * planeMat 1 u = planeMat 1 u * planeMat u 1
    simp only [planeMat_mul, mul_one, one_mul]
  · intro i j c hc
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hc'
    change planeMat u 1 ^ i.val * planeMat 1 u ^ j.val = _ at hc'
    rw [planeMat_pow, planeMat_pow, planeMat_mul, one_pow, one_pow, mul_one, one_mul] at hc'
    exact hind i j _ hc'
  · apply Units.ext
    change swapMat * planeMat u 1 * swapMat = planeMat 1 u
    rw [swapMat_mul_planeMat, mul_assoc, swapMat_mul_self, mul_one]
  · apply Units.ext
    change swapMat * planeMat 1 u * swapMat = planeMat u 1
    rw [swapMat_mul_planeMat, mul_assoc, swapMat_mul_self, mul_one]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change planeMat X 1 * planeMat u 1 * planeMat X' 1 = planeMat u 1 ^ 2
    rw [planeMat_pow, planeMat_mul, planeMat_mul, hXu, mul_assoc, hXX', mul_one, one_pow,
      mul_one, mul_one]
  · apply Units.ext
    change planeMat X 1 * planeMat 1 u * planeMat X' 1 = planeMat 1 u
    rw [planeMat_mul, planeMat_mul, mul_one, hXX', one_mul, mul_one]

theorem exists_std [Finite F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ a b w : GL (Fin 2 ⊕ Fin 2) F,
      (∀ g ∈ [a, b, w], ∃ M N : Matrix (Fin 2) (Fin 2) F, M.det = 1 ∧ N.det = 1 ∧
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeMat M N) ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
      (∀ i j : ZMod 3, ∀ c : Fˣ, a ^ i.val * b ^ j.val =
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c → i = 0 ∧ j = 0) ∧
      swapGL * a * swapGL⁻¹ = b ∧ swapGL * b * swapGL⁻¹ = a ∧ w * a * w⁻¹ = a ^ 2 ∧
      w * b * w⁻¹ = b := by
  obtain ⟨x, z, hxz⟩ := exists_sq_sub_mul_add_sq_eq_neg_one h2 h3
  have hdetX : (xMat x z).det = 1 := by rw [det_xMat, hxz, neg_neg]
  have hXA : xMat x z * xMatAdj x z = 1 := by rw [xMat_mul_xMatAdj, hdetX, one_smul]
  have hAX : xMatAdj x z * xMat x z = 1 := by rw [xMatAdj_mul_xMat, hdetX, one_smul]
  obtain ⟨a, b, w, ⟨ha, hb, hw⟩, hrest⟩ := exists_std_gen uMat (xMat x z) (xMatAdj x z) uMat_cube
    hXA hAX (xMat_mul_uMat x z) eq_zero_of_planeMat_pow_eq_scalar
  refine ⟨a, b, w, ?_, hrest⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨_, _, det_uMat, det_one, ha⟩
  · exact ⟨_, _, det_one, det_uMat, hb⟩
  · exact ⟨_, _, hdetX, det_one, hw⟩

variable [Finite F]

theorem e9Move_projSp (hF3 : ¬ 3 ∣ Nat.card F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    E9Move (CFSG.PGLModel.projSp 2 F) := by
  have hsyl := CFSG.RankThree.PartTwo.Sec12.Hering129C.sylow_comm_projSp_two hF3
  have hno := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.noE27_projSp_two hF3
  have e := CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2 F
  have hne : ∀ E : Subgroup (CFSG.PGLModel.projSp 2 F), CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E ≠ 27 := fun E hE h27 => hno ⟨E.map e.toMonoidHom,
    isElemAbelian_map e.toMonoidHom hE, by rw [Subgroup.card_map_of_injective e.injective, h27]⟩
  haveI : Finite (CFSG.PGLModel.projSp 2 F) := Finite.of_equiv _ e.symm.toEquiv
  have hle := card_le_nine_of_forall_ne hne
  rw [← CFSG.PGLModel.projImage_statedSp] at hsyl hle ⊢
  obtain ⟨a, b, w, hmat, ha3, hb3, hab, hind, hsa, hsb, hwa, hwb⟩ := exists_std h2 h3
  have hsympl : ∀ g ∈ [a, b, w], g ∈ StatedSp 2 F := by
    intro g hg
    obtain ⟨M, N, hM, hN, hgMN⟩ := hmat g hg
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hgMN]
    exact planeMat_symp hM hN
  exact e9Move_projImage_of_mats hsyl hle (hsympl a (by simp)) (hsympl b (by simp))
    (by rw [CFSG.Open.StatedAPI.mem_statedSp_iff]; exact swapMat_symp) (hsympl w (by simp))
    ha3 hb3 hab hind hsa hsb hwa hwb

end E9

theorem two_three_ne_zero {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hF : Nat.card F = p) : (2 : F) ≠ 0 ∧ (3 : F) ≠ 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hp : p.Prime := Fact.out
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega

theorem concl_projSp {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hF : Nat.card F = p) : Concl (CFSG.PGLModel.projSp 2 F) := by
  have e := CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2 F
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp3 hF
  have hF3 : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1 h
    omega
  refine ⟨inner_of_mulEquiv e fun σ hσ =>
      CFSG.RankThree.PartTwo.Sec4.E27.psp4_prime_order_three_inner hp3 hF σ
        (by rw [← hσ]; exact pow_orderOf_eq_one σ),
    center_eq_bot_of_mulEquiv e
      (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by norm_num)),
    e9Move_projSp hF3 h2 h3⟩

theorem kf430LiePSp_holds : KF430LiePSp := by
  intro p _ hp L _ _ ⟨e⟩
  have hF : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  exact Concl.of_mulEquiv e (concl_projSp hp hF)

end CFSG.RankThree.PartTwo.KFacts.KF430
