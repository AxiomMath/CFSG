module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open Matrix CFSG.Open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

section Transvection

variable {k : Type} [Field k] [CharP k 2]

abbrev burnsideF429_spE1 (k : Type) [Field k] : Fin 2 ⊕ Fin 2 → k := Pi.single (Sum.inl 0) 1

abbrev burnsideF429_spJ (k : Type) [Field k] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k :=
  fromBlocks 0 1 (-1) 0

theorem burnsideF429_sp_exists_mulVec_eq {v : Fin 2 ⊕ Fin 2 → k} (hv : v ≠ 0) :
    ∃ P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k,
      Pᵀ * burnsideF429_spJ k * P = burnsideF429_spJ k ∧ P *ᵥ burnsideF429_spE1 k = v := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  set B : LinearMap.BilinForm k (Fin 2 ⊕ Fin 2 → k) := Matrix.toBilin' (burnsideF429_spJ k)
    with hBdef
  have hBapp : ∀ x y, B x y = ∑ i, ∑ j, x i * burnsideF429_spJ k i j * y j := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply']
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hB : B.IsAlt := by
    intro x
    rw [hBapp]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, one_apply, Matrix.neg_apply]
    simp
    ring
  have hnd : B.Nondegenerate := by
    rw [hBdef, Matrix.nondegenerate_toBilin'_iff]
    rw [Matrix.nondegenerate_iff_det_ne_zero]
    rw [show burnsideF429_spJ k = -(Matrix.J (Fin 2) k) by
      ext a b; rcases a with i | i <;> rcases b with j | j <;> simp [Matrix.J, fromBlocks]]
    rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_J (Fin 2) k).ne_zero
  obtain ⟨m, b, hb, hb0⟩ := hB.exists_basis_apply_eq_J_inl_zero_eq hnd hv
  have hm : m = 1 := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin] at h
    omega
  subst hm
  refine ⟨Matrix.of fun i j => b j i, ?_, ?_⟩
  · ext x y
    have := hb x y
    rw [hBapp] at this
    simp only [mul_apply, transpose_apply, Matrix.of_apply]
    have e : ∑ j, (∑ i, b x i * burnsideF429_spJ k i j) * b y j =
        ∑ i, ∑ j, b x i * burnsideF429_spJ k i j * b y j := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e, this]
    rcases x with i | i <;> rcases y with j | j <;>
      simp [Matrix.J, fromBlocks, one_apply, CharTwo.neg_eq]
  · ext i
    simp only [mulVec, dotProduct, burnsideF429_spE1, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]
    rw [hb0]

theorem burnsideF429_rank_conj {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k)
    (M : Matrix ι ι k) :
    Matrix.rank ((g : Matrix ι ι k) * M * ((g⁻¹ : GL ι k) : Matrix ι ι k)) = Matrix.rank M := by
  have hg : IsUnit (g : Matrix ι ι k).det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hgi : IsUnit ((g⁻¹ : GL ι k) : Matrix ι ι k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hgi, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hg]

theorem burnsideF429_conj_sub_one {ι : Type} [Fintype ι] [DecidableEq ι] (g A : GL ι k) :
    (((g * A * g⁻¹ : GL ι k) : Matrix ι ι k) - 1) =
      (g : Matrix ι ι k) * ((A : Matrix ι ι k) - 1) * ((g⁻¹ : GL ι k) : Matrix ι ι k) := by
  have hgg : (g : Matrix ι ι k) * ((g⁻¹ : GL ι k) : Matrix ι ι k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgg]

theorem burnsideF429_rank_longRoot {c : k} (hc : c ≠ 0) :
    Matrix.rank ((1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) = 1 := by
  have e : ((1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) =
      Matrix.vecMulVec (Pi.single (Sum.inl 0) c) (Pi.single (Sum.inr 0) 1) := by
    ext a b
    simp only [add_sub_cancel_left, matrixUnit, vecMulVec_apply, Pi.single_apply]
    by_cases ha : a = Sum.inl 0 <;> by_cases hb : b = Sum.inr 0 <;> simp [ha, hb]
  rw [e]
  refine le_antisymm (Matrix.rank_vecMulVec_le _ _) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := congrFun (congrArg (fun f => f (Pi.single (Sum.inr 0) 1)) h0) (Sum.inl 0)
  simp [Matrix.mulVecLin_apply, mulVec_single_one, vecMulVec_apply] at this
  exact hc this

theorem burnsideF429_sp4_transvection_conj {A : GL (Fin 2 ⊕ Fin 2) k} (hA : A ∈ StatedSp 2 k)
    (hr : Matrix.rank ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) = 1) :
    ∃ g : GL (Fin 2 ⊕ Fin 2) k, g ∈ StatedSp 2 k ∧ ∃ c : k, c ≠ 0 ∧
      ((g * A * g⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
        1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c := by
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k := (A : Matrix _ _ k) - 1 with hN
  obtain ⟨⟨v, hvR⟩, hv0, hvspan⟩ := (finrank_eq_one_iff' (K := k)
    (V := LinearMap.range N.mulVecLin)).mp hr
  have hv : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hNx : ∀ x, ∃ c : k, N *ᵥ x = c • v := by
    intro x
    obtain ⟨c, hc⟩ := hvspan ⟨N *ᵥ x, x, rfl⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨P, hPs, hPe⟩ := burnsideF429_sp_exists_mulVec_eq hv
  have hdetJ : (burnsideF429_spJ k).det ≠ 0 := by
    rw [show burnsideF429_spJ k = -(Matrix.J (Fin 2) k) by
      ext a b; rcases a with i | i <;> rcases b with j | j <;> simp [Matrix.J, fromBlocks]]
    rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_J (Fin 2) k).ne_zero
  have hdetP : IsUnit P.det := by
    have h := congrArg Matrix.det hPs
    rw [det_mul, det_mul, det_transpose] at h
    have : P.det * P.det = 1 := by
      have h' : P.det * (burnsideF429_spJ k).det * P.det = 1 * (burnsideF429_spJ k).det := by
        rw [h, one_mul]
      exact mul_right_cancel₀ hdetJ (by linear_combination h' :
        P.det * P.det * (burnsideF429_spJ k).det = 1 * (burnsideF429_spJ k).det)
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one this)
  set Pg : GL (Fin 2 ⊕ Fin 2) k := Matrix.GeneralLinearGroup.mk'' P hdetP with hPg
  have hPgval : (Pg : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = P := rfl
  have hPgS : Pg ∈ StatedSp 2 k := CFSG.Open.StatedAPI.mem_statedSp_iff.mpr (by rw [hPgval]; exact hPs)
  refine ⟨Pg⁻¹, (StatedSp 2 k).inv_mem hPgS, ?_⟩
  set M : GL (Fin 2 ⊕ Fin 2) k := Pg⁻¹ * A * Pg⁻¹⁻¹ with hMdef
  have hMS : M ∈ StatedSp 2 k :=
    (StatedSp 2 k).mul_mem ((StatedSp 2 k).mul_mem ((StatedSp 2 k).inv_mem hPgS) hA)
      ((StatedSp 2 k).inv_mem ((StatedSp 2 k).inv_mem hPgS))
  have hMsub : ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) =
      ((Pg⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * N *
        ((Pg⁻¹⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) :=
    burnsideF429_conj_sub_one Pg⁻¹ A
  have hPinvP : ((Pg⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix _ _ k) * P = 1 := by
    rw [← hPgval, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPinv_v : ((Pg⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix _ _ k) *ᵥ v = burnsideF429_spE1 k := by
    rw [← hPe, mulVec_mulVec, hPinvP, one_mulVec]
  have hrow : ∀ a j : Fin 2 ⊕ Fin 2, a ≠ Sum.inl 0 →
      ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) a j = 0 := by
    intro a j ha
    obtain ⟨c, hc⟩ := hNx (((Pg⁻¹⁻¹ : GL (Fin 2 ⊕ Fin 2) k) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *ᵥ Pi.single j 1)
    have hcol : ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) *ᵥ Pi.single j 1 =
        c • burnsideF429_spE1 k := by
      rw [hMsub, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_smul, hPinv_v]
    have := congrFun hcol a
    rw [mulVec_single_one] at this
    simpa [Pi.single_apply, ha] using this
  have hsymp := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hMS
  set Mm := (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) with hMm
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 ⊕ Fin 2 → k, ∀ b, (Mm - 1) (Sum.inl 0) b = w b :=
    ⟨_, fun _ => rfl⟩
  have hMe : ∀ a b, Mm a b = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) a b +
      (if a = Sum.inl 0 then w b else 0) := by
    intro a b
    by_cases ha : a = Sum.inl 0
    · subst ha
      rw [if_pos rfl, ← hw, Matrix.sub_apply]
      ring
    · rw [if_neg ha, add_zero, ← sub_eq_zero, ← Matrix.sub_apply, hrow a b ha]
  have hwa : ∀ a, a ≠ Sum.inr 0 → w a = 0 := by
    intro a ha
    have h1 := congrFun (congrFun hsymp a) (Sum.inr 0)
    simp only [mul_apply, transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hMe] at h1
    rcases a with i | i <;> fin_cases i
    · simp [one_apply, fromBlocks] at h1 ⊢
      first | exact h1 | linear_combination h1 | linear_combination -h1
    · simp [one_apply, fromBlocks] at h1 ⊢
      first | exact h1 | linear_combination h1 | linear_combination -h1
    · exact absurd rfl ha
    · simp [one_apply, fromBlocks] at h1 ⊢
      first | exact h1 | linear_combination h1 | linear_combination -h1
  refine ⟨w (Sum.inr 0), ?_, ?_⟩
  · intro hc0
    have hzero : Mm - 1 = 0 := by
      ext a b
      rw [Matrix.zero_apply]
      by_cases ha : a = Sum.inl 0
      · subst ha
        rw [hw]
        by_cases hb : b = Sum.inr 0
        · subst hb; exact hc0
        · exact hwa b hb
      · exact hrow a b ha
    have h0 : N.rank = 0 := by
      rw [← burnsideF429_rank_conj Pg⁻¹ N, ← hMsub, hzero, Matrix.rank_zero]
    omega
  · ext a b
    rw [hMe a b, Matrix.add_apply]
    congr 1
    by_cases ha : a = Sum.inl 0
    · subst ha
      rw [if_pos rfl]
      by_cases hb : b = Sum.inr 0
      · subst hb; simp [matrixUnit]
      · rw [hwa b hb]; simp [matrixUnit, hb]
    · rw [if_neg ha]; simp [matrixUnit, ha]

end Transvection

section Marking

variable {k : Type} [Field k] [CharP k 2]

theorem burnsideF429_matrixUnit_zero {ι : Type} [DecidableEq ι] (a b : ι) :
    (matrixUnit a b (0 : k) : Matrix ι ι k) = 0 := by
  ext i j
  simp [matrixUnit]

theorem burnsideF429_longRoot_mul (c c' : k) :
    ((1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *
      (1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c')) =
      1 + matrixUnit (Sum.inl 0) (Sum.inr 0) (c + c') := by
  have hEE : (matrixUnit (Sum.inl 0) (Sum.inr 0) c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *
      matrixUnit (Sum.inl 0) (Sum.inr 0) c' = 0 := by
    ext a b
    rw [mul_apply, Matrix.zero_apply, Finset.sum_eq_zero]
    intro j _
    by_cases hj : j = Sum.inr 0
    · subst hj; simp [matrixUnit]
    · simp [matrixUnit, hj]
  have hadd : (matrixUnit (Sum.inl 0) (Sum.inr 0) c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) +
      matrixUnit (Sum.inl 0) (Sum.inr 0) c' = matrixUnit (Sum.inl 0) (Sum.inr 0) (c + c') := by
    ext a b
    simp only [Matrix.add_apply, matrixUnit]
    split_ifs <;> simp
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hEE, add_zero, add_assoc,
    add_comm (matrixUnit (Sum.inl 0) (Sum.inr 0) c'), hadd]

theorem burnsideF429_mem_nativeRoot_longOne {q : ℕ}
    (x : ClassicalRoots.nativeGroup .Sp4 q k) :
    x ∈ ClassicalRoots.nativeRoot .Sp4 q (1 : GL (ClassicalRoots.Coord .Sp4) k) .longOne false ↔
      ∃ c : k, ((x : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
        1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨-, c, c', -, hc⟩ := hy
      refine ⟨c, ?_⟩
      rw [hc]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
    | one => exact ⟨0, by rw [burnsideF429_matrixUnit_zero, add_zero]; rfl⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      refine ⟨a + b, ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, ha, hb, burnsideF429_longRoot_mul]
    | inv y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨-a, ?_⟩
      rw [Subgroup.coe_inv, Matrix.coe_units_inv, ha]
      exact Matrix.inv_eq_right_inv (by
        rw [burnsideF429_longRoot_mul, add_neg_cancel, burnsideF429_matrixUnit_zero, add_zero])
  · rintro ⟨c, hc⟩
    refine Subgroup.subset_closure ⟨Or.inr (Or.inr (Or.inl rfl)), c, 0, trivial, ?_⟩
    rw [hc]
    simp [markedMatrix, positiveMatrix, symplecticRoot]

variable [Finite k] {H : Type} [Group H] {d : ℕ}

noncomputable def burnsideF429_sp4Marking (hd : 1 ≤ d) (hk : Nat.card k = 2 ^ d)
    (ι : StatedSp 2 k ≃* H) : ClassicalRoots.Marking .Sp4 2 d H where
  field := k
  fieldStructure := inferInstance
  finiteField := inferInstance
  prime := Nat.prime_two
  exponent_pos := hd
  field_card := by simpa using hk
  basis := 1
  basis_compatible := rfl
  identification := (CFSG.QuasithinUnique.Lin2.Five.projEquiv k).symm.trans ι

theorem burnsideF429_sp4Marking_mem_root (hd : 1 ≤ d) (hk : Nat.card k = 2 ^ d)
    (ι : StatedSp 2 k ≃* H) (y : H) :
    y ∈ (burnsideF429_sp4Marking hd hk ι).root .longOne false ↔
      ∃ c : k, (((ι.symm y : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = 1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c := by
  have ht : ∀ x : StatedSp 2 k, (burnsideF429_sp4Marking hd hk ι).transport x = ι x := by
    intro x
    change ι ((CFSG.QuasithinUnique.Lin2.Five.projEquiv k).symm
      (CFSG.QuasithinUnique.Lin2.Five.projEquiv k x)) = ι x
    rw [MulEquiv.symm_apply_apply]
  unfold Marking.root
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : ι.symm ((burnsideF429_sp4Marking hd hk ι).transport x) = x := by
      rw [ht x]
      exact ι.symm_apply_apply x
    rw [e]
    have hx' : (x : ClassicalRoots.nativeGroup .Sp4 (2 ^ d) k) ∈
        ClassicalRoots.nativeRoot .Sp4 (2 ^ d) (1 : GL (ClassicalRoots.Coord .Sp4) k)
          .longOne false := hx
    obtain ⟨c, hc⟩ := (burnsideF429_mem_nativeRoot_longOne _).mp hx'
    exact ⟨c, hc⟩
  · intro h
    refine ⟨ι.symm y, (burnsideF429_mem_nativeRoot_longOne (k := k) (q := 2 ^ d) _).mpr h, ?_⟩
    rw [ht, MulEquiv.apply_symm_apply]

theorem burnsideF429_sp4Marking_longRoot_iff (hd : 1 ≤ d) (hk : Nat.card k = 2 ^ d)
    (ι : StatedSp 2 k ≃* H) (y : H) :
    (y ≠ 1 ∧ y * y = 1 ∧
      ∃ g : H, g * y * g⁻¹ ∈ (burnsideF429_sp4Marking hd hk ι).root .longOne false) ↔
      (y ≠ 1 ∧ y * y = 1 ∧ Matrix.rank ((((ι.symm y : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) = 1) := by
  refine and_congr_right fun hy1 => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨c, hc⟩ := (burnsideF429_sp4Marking_mem_root hd hk ι _).mp hg
    rw [map_mul, map_mul, map_inv] at hc
    set G : GL (Fin 2 ⊕ Fin 2) k := ((ι.symm g : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) with hG
    have hc' : ((G * ((ι.symm y : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) * G⁻¹ :
        GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
        1 + matrixUnit (Sum.inl 0) (Sum.inr 0) c := hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hy1
      have h1 : ι.symm g * ι.symm y * (ι.symm g)⁻¹ = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hc, burnsideF429_matrixUnit_zero, add_zero]
        rfl
      have h2 : ι.symm y = 1 := by
        have e : ι.symm y = (ι.symm g)⁻¹ * (ι.symm g * ι.symm y * (ι.symm g)⁻¹) * ι.symm g := by
          group
        rw [e, h1]
        group
      rw [← ι.apply_symm_apply y, h2, map_one]
    rw [← burnsideF429_rank_conj G, ← burnsideF429_conj_sub_one, hc']
    exact burnsideF429_rank_longRoot hc0
  · intro hr
    obtain ⟨G, hG, c, -, hc⟩ := burnsideF429_sp4_transvection_conj (ι.symm y).2 hr
    refine ⟨ι ⟨G, hG⟩, (burnsideF429_sp4Marking_mem_root hd hk ι _).mpr ⟨c, ?_⟩⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hc

theorem burnsideF429_sp4_marking_exists {E : Type} [Group E] {C : Subgroup E}
    (hd : 1 ≤ d) (hk : Nat.card k = 2 ^ d) (ι : StatedSp 2 k ≃* C) (P : E → Prop)
    (hP1 : ∀ e, P e → e ≠ 1 ∧ e * e = 1)
    (hP2 : ∀ x : StatedSp 2 k, ((ι x : C) : E) ≠ 1 → ((ι x : C) : E) * ((ι x : C) : E) = 1 →
      (P ((ι x : C) : E) ↔ Matrix.rank (((x : GL (Fin 2 ⊕ Fin 2) k) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) - 1) = 1)) :
    ∃ marking : ClassicalRoots.Marking .Sp4 2 d C, ∀ (e : E) (he : e ∈ C),
      (P e ↔ e ≠ 1 ∧ e * e = 1 ∧
        ∃ conjugator : C, conjugator * ⟨e, he⟩ * conjugator⁻¹ ∈ marking.root .longOne false) := by
  refine ⟨burnsideF429_sp4Marking hd hk ι, fun e he => ?_⟩
  have key := burnsideF429_sp4Marking_longRoot_iff hd hk ι ⟨e, he⟩
  have hx : ((ι (ι.symm ⟨e, he⟩) : C) : E) = e := by rw [MulEquiv.apply_symm_apply]
  have hP := hP2 (ι.symm ⟨e, he⟩)
  rw [hx] at hP
  have hne : e ≠ 1 → (⟨e, he⟩ : C) ≠ 1 := fun h1 h => h1 (congrArg Subtype.val h)
  have hsq : e * e = 1 → (⟨e, he⟩ : C) * ⟨e, he⟩ = 1 := fun h2 => Subtype.ext h2
  constructor
  · intro hPe
    obtain ⟨h1, h2⟩ := hP1 e hPe
    obtain ⟨-, -, hg⟩ := key.mpr ⟨hne h1, hsq h2, (hP h1 h2).mp hPe⟩
    exact ⟨h1, h2, hg⟩
  · rintro ⟨h1, h2, hg⟩
    exact (hP h1 h2).mpr (key.mp ⟨hne h1, hsq h2, hg⟩).2.2

end Marking

end CFSG.ASVolI
