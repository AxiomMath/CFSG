module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

@[expose] noncomputable def sp4J : StatedSp 2 K :=
  ⟨⟨fromBlocks 0 1 (-1) 0, fromBlocks 0 (-1) 1 0, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩,
    mem_statedSp_iff.2 (by simp [fromBlocks_multiply, fromBlocks_transpose])⟩

theorem coe_sp4J : (((sp4J : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 0 1 (-1) 0 := rfl

theorem ut_congr {C D : Matrix (Fin 2) (Fin 2) K} (h : C = D) (hC : Cᵀ = C) (hD : Dᵀ = D) :
    upperUnipotentSp 2 K hC = upperUnipotentSp 2 K hD := by
  subst h
  rfl

theorem ut_mul {C D : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hD : Dᵀ = D) :
    upperUnipotentSp 2 K hC * upperUnipotentSp 2 K hD =
      upperUnipotentSp 2 K (C := C + D) (by rw [transpose_add, hC, hD]) := by
  refine statedSp_ext ?_
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, coe_upperUnipotentSp,
    coe_upperUnipotentSp, fromBlocks_multiply]
  simp [add_comm]

@[expose] noncomputable def lowerSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    StatedSp 2 K :=
  sp4J * upperUnipotentSp 2 K hC * sp4J

theorem lowerSp_congr {C D : Matrix (Fin 2) (Fin 2) K} (h : C = D) (hC : Cᵀ = C) (hD : Dᵀ = D) :
    lowerSp hC = lowerSp hD := by
  subst h
  rfl

@[expose] noncomputable def nElt {D E : Matrix (Fin 2) (Fin 2) K} (hD : Dᵀ = D) (hE : Eᵀ = E) :
    StatedSp 2 K :=
  upperUnipotentSp 2 K hD * lowerSp hE * upperUnipotentSp 2 K hD

theorem inv_transpose_mul_transpose (A : GL (Fin 2) K) :
    ((A : Matrix (Fin 2) (Fin 2) K)⁻¹)ᵀ * (A : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
  rw [← transpose_mul, ← Matrix.coe_units_inv, Units.mul_inv, transpose_one]

theorem leviSp_mul_ut_mul_inv (A : GL (Fin 2) K) {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    leviSp A * upperUnipotentSp 2 K hC * (leviSp A)⁻¹ =
      upperUnipotentSp 2 K (C := (A : Matrix (Fin 2) (Fin 2) K) * C *
        (A : Matrix (Fin 2) (Fin 2) K)ᵀ) (by
          rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  refine statedSp_ext ?_
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp,
    coe_upperUnipotentSp, coe_leviSp, coe_upperUnipotentSp, inv_inv, fromBlocks_multiply,
    fromBlocks_multiply]
  simp [Matrix.mul_assoc]
  exact inv_transpose_mul_transpose A

theorem ut_comm {C D : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hD : Dᵀ = D) :
    upperUnipotentSp 2 K hC * upperUnipotentSp 2 K hD =
      upperUnipotentSp 2 K hD * upperUnipotentSp 2 K hC := by
  refine statedSp_ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_upperUnipotentSp,
    coe_upperUnipotentSp, fromBlocks_multiply, fromBlocks_multiply]
  simp [add_comm]

@[expose] def uGL (x : K) : GL (Fin 2) K :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

@[expose] def dGL (a d : Kˣ) : GL (Fin 2) K :=
  ⟨!![(a : K), 0; 0, d], !![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem coe_uGL (x : K) : ((uGL x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] :=
  rfl

theorem coe_uGL_inv (x : K) :
    (((uGL x)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, -x; 0, 1] := rfl

theorem coe_dGL (a d : Kˣ) :
    ((dGL a d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, d] := rfl

theorem coe_dGL_inv (a d : Kˣ) :
    (((dGL a d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)] := rfl

section Char2

variable [CharP K 2]

theorem sp4J_mul_self : (sp4J : StatedSp 2 K) * sp4J = 1 := by
  refine statedSp_ext ?_
  rw [Subgroup.coe_mul, Units.val_mul, coe_sp4J, fromBlocks_multiply]
  simp [CharTwo.neg_eq, fromBlocks_one]

theorem inv_sp4J : (sp4J : StatedSp 2 K)⁻¹ = sp4J := inv_eq_of_mul_eq_one_right sp4J_mul_self

theorem coe_lowerSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((lowerSp hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 0 C 1 := by
  rw [lowerSp, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_sp4J,
    coe_upperUnipotentSp, fromBlocks_multiply, fromBlocks_multiply]
  simp [CharTwo.neg_eq]

theorem coe_nElt {D E : Matrix (Fin 2) (Fin 2) K} (hD : Dᵀ = D) (hE : Eᵀ = E) (hDE : D * E = 1)
    (hED : E * D = 1) :
    (((nElt hD hE : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 0 D E 0 := by
  rw [nElt, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_upperUnipotentSp, coe_lowerSp, fromBlocks_multiply, fromBlocks_multiply]
  simp [hDE, hED, CharTwo.add_self_eq_zero]

theorem leviSp_mul_lowerSp_mul_inv (A : GL (Fin 2) K) {C : Matrix (Fin 2) (Fin 2) K}
    (hC : Cᵀ = C) :
    leviSp A * lowerSp hC * (leviSp A)⁻¹ =
      lowerSp (C := ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ * C *
        ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (by
          rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  refine statedSp_ext ?_
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp,
    coe_lowerSp, coe_leviSp, coe_lowerSp, inv_inv, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc]
  exact inv_transpose_mul_transpose A

section Mem

variable {H : Subgroup (StatedSp 2 K)}
  (hτ : ∀ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C), upperUnipotentSp 2 K hC ∈ H)
  (hJ : sp4J ∈ H)

include hτ hJ

omit [CharP K 2] in
theorem lowerSp_mem {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : lowerSp hC ∈ H :=
  mul_mem (mul_mem hJ (hτ C hC)) hJ

omit [CharP K 2] in
theorem nElt_mem {D E : Matrix (Fin 2) (Fin 2) K} (hD : Dᵀ = D) (hE : Eᵀ = E) :
    nElt hD hE ∈ H :=
  mul_mem (mul_mem (hτ D hD) (lowerSp_mem hτ hJ hE)) (hτ D hD)

theorem leviSp_dGL_mem (a d : Kˣ) : leviSp (dGL a d) ∈ H := by
  have hD : (!![(a : K), 0; 0, d])ᵀ = !![(a : K), 0; 0, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hE : (!![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)])ᵀ =
      !![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hDE : (!![(a : K), 0; 0, d]) * !![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)] = 1 := by
    simp [Matrix.one_fin_two]
  have hED : (!![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)]) * !![(a : K), 0; 0, d] = 1 := by
    simp [Matrix.one_fin_two]
  have h : leviSp (dGL a d) = nElt hD hE * sp4J := by
    refine statedSp_ext ?_
    rw [Subgroup.coe_mul, Units.val_mul, coe_nElt hD hE hDE hED, coe_sp4J, coe_leviSp, coe_dGL,
      coe_dGL_inv, fromBlocks_multiply, hE]
    simp [CharTwo.neg_eq]
  rw [h]
  exact mul_mem (nElt_mem hτ hJ hD hE) hJ

theorem leviSp_uGL_mem (x : K) : leviSp (uGL x) ∈ H := by
  have hD : (!![x, 1; 1, 0])ᵀ = !![x, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hE : (!![0, 1; 1, x])ᵀ = !![0, 1; 1, x] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hP : (!![0, 1; 1, 0])ᵀ = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hDE : (!![x, 1; 1, 0]) * !![0, 1; 1, x] = (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hED : (!![0, 1; 1, x]) * !![x, 1; 1, 0] = (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hPP : (!![0, 1; 1, 0]) * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    simp [Matrix.one_fin_two]
  have h : leviSp (uGL x) = nElt hD hE * nElt hP hP := by
    refine statedSp_ext ?_
    rw [coe_leviSp, coe_uGL, coe_uGL_inv, Subgroup.coe_mul, Units.val_mul, coe_nElt hD hE hDE hED,
      coe_nElt hP hP hPP hPP, fromBlocks_multiply]
    simp [CharTwo.neg_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  exact mul_mem (nElt_mem hτ hJ hD hE) (nElt_mem hτ hJ hP hP)

theorem borelSubgroup_le_of_tau_mem : borelSubgroup 2 K ≤ H := by
  intro g hg
  obtain ⟨A, C, hAu, hAdet, hC, hgA⟩ := mem_borelSubgroup_iff.mp hg
  have hg' : g = blockElt hAdet hC := statedSp_ext (by rw [hgA, coe_blockElt])
  rw [hg', blockElt]
  refine mul_mem ?_ (hτ C hC)
  have hA10 : A 1 0 = 0 := hAu (show (0 : Fin 2) < 1 by decide)
  have hdet : A.det = A 0 0 * A 1 1 := by rw [det_fin_two, hA10, mul_zero, sub_zero]
  have ha : A 0 0 ≠ 0 := left_ne_zero_of_mul (hdet ▸ hAdet.ne_zero)
  have hd : A 1 1 ≠ 0 := right_ne_zero_of_mul (hdet ▸ hAdet.ne_zero)
  have hfac : nonsingInvUnit A hAdet =
      dGL (Units.mk0 _ ha) (Units.mk0 _ hd) * uGL (A 0 1 / A 0 0) := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_dGL, coe_uGL]
    change A = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA10]
    all_goals field_simp
  rw [hfac, map_mul]
  exact mul_mem (leviSp_dGL_mem hτ hJ _ _) (leviSp_uGL_mem hτ hJ _)

theorem eq_top_of_tau_mem_of_sp4J_mem : H = ⊤ := by
  have hB := borelSubgroup_le_of_tau_mem hτ hJ
  obtain ⟨h1, -⟩ := borel_overgroups H hB
  have hcut : borelCuts K H = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := borelCuts_le H i hi
    have hJ' : sp4J ∈ flagStabilizer 2 K (borelCuts K H) := by rw [← h1]; exact hJ
    have hst := mem_flagStabilizer.mp hJ' i hi
    have he : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K i := by
      rw [mem_flag_of_le hi2, mem_isoFlag]
      refine ⟨fun j => by simp, fun j hj => ?_⟩
      have hj0 : j ≠ 0 := fun h => by subst h; simp at hj; omega
      simp [hj0]
    have hmem : ((sp4J : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K i := by
      rw [← mem_stabilizer.mp hst]
      exact ⟨_, he, rfl⟩
    have h0 := (mem_isoFlag.mp ((mem_flag_of_le hi2).mp hmem)).1 0
    rw [coe_sp4J, mulVec_single_one, col_apply, fromBlocks_apply₂₁] at h0
    simp at h0
  calc H = flagStabilizer 2 K (borelCuts K H) := h1
    _ = flagStabilizer 2 K ∅ := by rw [hcut]
    _ = ⊤ := flagStabilizer_empty

end Mem

theorem ut_mul_self {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    upperUnipotentSp 2 K hC * upperUnipotentSp 2 K hC = 1 := by
  refine statedSp_ext ?_
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, fromBlocks_multiply]
  simp [CharTwo.add_self_eq_zero, fromBlocks_one]

theorem pow_two_pow_ne_one_of_isUnit_sub_one {y : StatedSp 2 K}
    (hy : IsUnit (((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1))
    (n : ℕ) : y ^ 2 ^ n ≠ 1 := by
  intro h
  set Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ((y : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hY
  have h1 : Y ^ 2 ^ n = 1 := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simpa [hY] using this
  have h2 : (Y - 1) ^ 2 ^ n = 0 := by
    rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right Y), h1, one_pow, sub_self]
  exact not_isUnit_zero (h2 ▸ hy.pow (2 ^ n))

end Char2

theorem pow_two_pow_ne_one_of_pow_three {G : Type*} [Group G] {y : G} (h3 : y ^ 3 = 1)
    (h1 : y ≠ 1) (n : ℕ) : y ^ 2 ^ n ≠ 1 := by
  have h2 : y ^ 2 ≠ 1 := fun h => h1 (by
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul])
  have key : ∀ n : ℕ, y ^ 2 ^ n = y ∨ y ^ 2 ^ n = y ^ 2 := by
    intro n
    induction n with
    | zero => exact Or.inl (pow_one y)
    | succ n ih =>
      rw [pow_succ, pow_mul]
      rcases ih with h | h
      · exact Or.inr (by rw [h])
      · refine Or.inl ?_
        rw [h, ← pow_mul]
        calc y ^ (2 * 2) = y ^ 3 * y := by rw [← pow_succ]
          _ = y := by rw [h3, one_mul]
  rcases key n with h | h
  · rwa [h]
  · rwa [h]

theorem invAutGen_of_mem_invXiAut {L : Type*} [Group L] {φ : MulAut L} {x : L}
    (hx : x ∈ invXiAut φ) (hgen : ∀ H : Subgroup L, fixSubgroup φ ≤ H → x ∈ H → H = ⊤) :
    InvAutGen L φ :=
  hgen _ (fixSubgroup_le_closure_invXiAut ⟨x, hx⟩) (Subgroup.subset_closure hx)

end CFSG.Quasithin.F7Two
