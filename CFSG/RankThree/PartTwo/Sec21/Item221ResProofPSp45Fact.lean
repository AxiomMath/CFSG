module

public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofPSp45
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.ClassicalInvolution.Orders.Symplectic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221ResProof.PSp45

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut)

variable {K : Type} [Field K]

@[expose] def pairMat (M N : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diagonal ![M 0 0, N 0 0]) (diagonal ![M 0 1, N 0 1])
    (diagonal ![M 1 0, N 1 0]) (diagonal ![M 1 1, N 1 1])

theorem pairMat_mul (M N M' N' : Matrix (Fin 2) (Fin 2) K) :
    pairMat (M * M') (N * N') = pairMat M N * pairMat M' N' := by
  simp only [pairMat, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pairMat_one : pairMat (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [← fromBlocks_one]
  simp only [pairMat]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem pairMat_transpose (M N : Matrix (Fin 2) (Fin 2) K) :
    (pairMat M N)ᵀ = pairMat Mᵀ Nᵀ := by
  simp only [pairMat, fromBlocks_transpose, diagonal_transpose, transpose_apply]

@[expose] def j2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem fromBlocks_eq_pairMat :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = pairMat j2 j2 := by
  simp only [pairMat, j2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem transpose_mul_j2_mul (M : Matrix (Fin 2) (Fin 2) K) : Mᵀ * j2 * M = M.det • j2 := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [j2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem pairMat_symplectic (M N : SpecialLinearGroup (Fin 2) K) :
    (pairMat (M : Matrix (Fin 2) (Fin 2) K) N)ᵀ * fromBlocks 0 1 (-1) 0 *
        pairMat (M : Matrix (Fin 2) (Fin 2) K) N = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_eq_pairMat, pairMat_transpose, ← pairMat_mul, ← pairMat_mul,
    transpose_mul_j2_mul, transpose_mul_j2_mul, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe, one_smul]

@[expose] def pairUnit (M N : SpecialLinearGroup (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K where
  val := pairMat (M : Matrix (Fin 2) (Fin 2) K) N
  inv := pairMat ((M⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    (N⁻¹ : SpecialLinearGroup (Fin 2) K)
  val_inv := by
    rw [← pairMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, pairMat_one]
  inv_val := by
    rw [← pairMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, pairMat_one]

@[expose] def pairSp :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun g := ⟨pairUnit g.1 g.2,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
      (pairMat_symplectic g.1 g.2)⟩
  map_one' := Subtype.ext (Units.ext (by
    change pairMat ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, pairMat_one]))
  map_mul' g h := Subtype.ext (Units.ext (by
    change pairMat (((g * h).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((g * h).2 : SpecialLinearGroup (Fin 2) K) =
        pairMat (g.1 : Matrix (Fin 2) (Fin 2) K) g.2 * pairMat (h.1 : Matrix (Fin 2) (Fin 2) K) h.2
    rw [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, pairMat_mul]))

theorem coe_pairSp (g : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    (((pairSp g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      pairMat (g.1 : Matrix (Fin 2) (Fin 2) K) g.2 :=
  rfl

theorem entries_of_proj_eq_one {g : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (h : proj 2 K (pairSp g) = 1) :
    (g.1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (g.2 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (g.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = (g.2 : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  have hmem := (QuotientGroup.eq_one_iff _).mp h
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' := congrArg (fun z : GL (Fin 2 ⊕ Fin 2) K => (z : Matrix (Fin 2 ⊕ Fin 2)
    (Fin 2 ⊕ Fin 2) K)) hc
  simp only [GeneralLinearGroup.coe_scalar] at hc'
  rw [coe_pairSp] at hc'
  have e1 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inr 0)
  have e2 := congrFun (congrFun hc' (Sum.inl 1)) (Sum.inr 1)
  have e3 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inl 0)
  have e4 := congrFun (congrFun hc' (Sum.inl 1)) (Sum.inl 1)
  simp [pairMat, Matrix.scalar_apply] at e1 e2 e3 e4
  exact ⟨e1.symm, e2.symm, e3.symm.trans e4⟩

@[expose] def x3 : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem coe_x3_sq :
    ((x3 ^ 2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![-1, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
  simp [x3]

theorem x3_pow_three : (x3 : SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, ← Matrix.SpecialLinearGroup.coe_pow, coe_x3_sq]
  simp [x3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_zero_of_entry {n : ℕ} (hn : n < 3)
    (h : ((x3 ^ n : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    n = 0 := by
  interval_cases n
  · rfl
  · rw [pow_one] at h
    simp [x3] at h
  · rw [coe_x3_sq] at h
    simp at h

@[expose] def m1 : SpecialLinearGroup (Fin 2) K :=
  ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

theorem m1_mul_self : (m1 : SpecialLinearGroup (Fin 2) K) * m1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [m1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem m1_comm_x3 : Commute (m1 : SpecialLinearGroup (Fin 2) K) x3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [m1, x3]

@[expose] def xHom : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K where
  toFun k := x3 ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_add, ← pow_eq_pow_mod _ x3_pow_three]

@[expose] def torusHom :
    Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →* StatedProj (StatedSp 2 K) :=
  (proj 2 K).comp (pairSp.comp (xHom.prodMap xHom))

theorem torusHom_injective : Function.Injective (torusHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨k, l⟩ h
  obtain ⟨hk, hl, -⟩ := entries_of_proj_eq_one h
  have hk0 := eq_zero_of_entry (ZMod.val_lt (Multiplicative.toAdd k)) hk
  have hl0 := eq_zero_of_entry (ZMod.val_lt (Multiplicative.toAdd l)) hl
  rw [ZMod.val_eq_zero] at hk0 hl0
  exact Prod.ext hk0 hl0

@[expose] def inv0 : StatedProj (StatedSp 2 K) := proj 2 K (pairSp (m1, 1))

theorem inv0_mul_self : (inv0 : StatedProj (StatedSp 2 K)) * inv0 = 1 := by
  rw [inv0, ← map_mul, ← map_mul, Prod.mk_mul_mk, m1_mul_self, one_mul, Prod.mk_one_one,
    map_one, map_one]

theorem inv0_ne_one (h2 : (2 : K) ≠ 0) : (inv0 : StatedProj (StatedSp 2 K)) ≠ 1 := by
  intro h
  obtain ⟨-, -, h00⟩ := entries_of_proj_eq_one h
  simp [m1] at h00
  apply h2
  linear_combination -h00

theorem inv0_comm (g : Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :
    torusHom g * (inv0 : StatedProj (StatedSp 2 K)) = inv0 * torusHom g := by
  have hc : Commute ((xHom.prodMap xHom) g) ((m1, 1) : SpecialLinearGroup (Fin 2) K ×
      SpecialLinearGroup (Fin 2) K) :=
    Prod.ext (m1_comm_x3.pow_right _).symm (Commute.one_right _)
  exact (hc.map ((proj 2 K).comp pairSp)).eq

variable [Finite K]

theorem five_eq_zero (hK : Nat.card K = 5) : (5 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [Fintype.card_eq_nat_card, hK] at h
  exact_mod_cast h

theorem two_ne_zero_of_card (hK : Nat.card K = 5) : (2 : K) ≠ 0 := by
  intro h
  have h5 := five_eq_zero hK
  have : (1 : K) = 0 := by linear_combination h5 - 2 * h
  exact one_ne_zero this

theorem ringChar_ne_two (hK : Nat.card K = 5) : ringChar K ≠ 2 := by
  intro h
  apply two_ne_zero_of_card hK
  have := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at this
  exact_mod_cast this

theorem card_psp (hK : Nat.card K = 5) : Nat.card (StatedProj (StatedSp 2 K)) = 4680000 := by
  have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := K) (n := 2)
    (two_ne_zero_of_card hK) (by norm_num)
  rw [hK, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at h
  norm_num at h
  omega

theorem exists_involution_of_isPGroup (hK : Nat.card K = 5)
    {F : Subgroup (StatedProj (StatedSp 2 K))} (hF : IsPGroup 3 F) :
    ∃ i : StatedProj (StatedSp 2 K), orderOf i = 2 ∧ ∀ f ∈ F, f * i = i * f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ := (torusHom (K := K)).range with hS₀
  have hS₀card : Nat.card S₀ = 9 := by
    rw [hS₀, ← Nat.card_congr (MonoidHom.ofInjective torusHom_injective).toEquiv, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3), Nat.card_zmod]
  have hS₀p : IsPGroup 3 S₀ := IsPGroup.of_card (n := 2) (by rw [hS₀card]; norm_num)
  obtain ⟨S, hFS⟩ := hF.exists_le_sylow
  obtain ⟨S₁, hS₀S₁⟩ := hS₀p.exists_le_sylow
  have hS₁card : Nat.card (S₁ : Subgroup (StatedProj (StatedSp 2 K))) ≤ 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S₁.isPGroup'
    have hdvd := Subgroup.card_subgroup_dvd_card (S₁ : Subgroup (StatedProj (StatedSp 2 K)))
    rw [hk, card_psp hK] at hdvd
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have h27 : 3 ^ 3 ∣ 4680000 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h27
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hS₀eq : S₀ = S₁ := Subgroup.eq_of_le_of_card_ge hS₀S₁ (by rw [hS₀card]; exact hS₁card)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) S₁ S
  refine ⟨g * inv0 * g⁻¹, ?_, fun f hf => ?_⟩
  · apply orderOf_eq_prime
    · rw [conj_pow, pow_two, inv0_mul_self, mul_one, mul_inv_cancel]
    · intro h
      apply inv0_ne_one (two_ne_zero_of_card hK)
      calc inv0 = g⁻¹ * (g * inv0 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
  · have hfS : f ∈ (S : Subgroup (StatedProj (StatedSp 2 K))) := hFS hf
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← hS₀eq] at hfS
    obtain ⟨t, ht⟩ := hfS
    have hf' : f = g * torusHom t * g⁻¹ := by
      rw [ht, MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      group
    rw [hf']
    have hc := inv0_comm (K := K) t
    calc g * torusHom t * g⁻¹ * (g * inv0 * g⁻¹) = g * (torusHom t * inv0) * g⁻¹ := by group
      _ = g * (inv0 * torusHom t) * g⁻¹ := by rw [hc]
      _ = g * inv0 * g⁻¹ * (g * torusHom t * g⁻¹) := by group

theorem exists_conj_eq_of_pow_three (hK : Nat.card K = 5)
    {β : MulAut (StatedProj (StatedSp 2 K))} (h3 : β ^ 3 = 1) :
    ∃ f : StatedProj (StatedSp 2 K), MulAut.conj f = β := by
  obtain ⟨A, σ, rfl⟩ := KFacts.psp4_odd_automorphism_normal_form (ringChar_ne_two hK) β
  have : Subsingleton (K ≃+* K) :=
    (Nat.card_eq_one_iff_unique.mp (Sec4.card_ringAut_eq (p := 5) (f := 1) (by norm_num) le_rfl
      (by rw [hK, pow_one]))).1
  rw [Subsingleton.elim σ 1, map_one, mul_one] at h3 ⊢
  exact Sec4.psp_inndiag_cube _ ⟨A, rfl⟩ h3

theorem exists_fixed_involution (hK : Nat.card K = 5)
    (B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))) (hB : ∀ β ∈ B, β ^ 3 = 1) :
    ∃ i : StatedProj (StatedSp 2 K), orderOf i = 2 ∧ ∀ β ∈ B, β i = i := by
  obtain ⟨-, -, hinj⟩ := CFSG.RankThree.PartOne.spProj_facts (r := 2) (K := K) (ℓ := 5) (f := 1)
    (by norm_num) le_rfl (by rw [hK, pow_one]) le_rfl (by norm_num)
  set F := B.comap (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _) with hFdef
  have hF : IsPGroup 3 F := by
    intro f
    refine ⟨1, Subtype.ext (hinj ?_)⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    exact hB _ f.2
  obtain ⟨i, hi2, hiF⟩ := exists_involution_of_isPGroup hK hF
  refine ⟨i, hi2, fun β hβ => ?_⟩
  obtain ⟨f, rfl⟩ := exists_conj_eq_of_pow_three hK (hB β hβ)
  have hf : f ∈ F := hβ
  rw [MulAut.conj_apply, hiF f hf, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec21.Item221ResProof.PSp45

namespace CFSG.RankThree.PartTwo.Sec21

theorem psp45AutThreeInv : PSp45AutThreeInv := by
  intro P _ _ hP B hB
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hP
  have hK5 : Nat.card K = 5 := by rw [hK, pow_one]
  set B' := B.map (MulAut.congr e).toMonoidHom with hB'def
  have hB' : ∀ β ∈ B', β ^ 3 = 1 := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hB.2 β hβ, map_one]
  obtain ⟨i, hi2, hfix⟩ := Item221ResProof.PSp45.exists_fixed_involution hK5 B' hB'
  refine ⟨e.symm i, by rw [MulEquiv.orderOf_eq]; exact hi2, fun β hβ => ?_⟩
  have h := hfix _ ⟨β, hβ, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply] at h
  have h' : e (β (e.symm i)) = i := h
  calc β (e.symm i) = e.symm (e (β (e.symm i))) := (e.symm_apply_apply _).symm
    _ = e.symm i := by rw [h']

end CFSG.RankThree.PartTwo.Sec21
