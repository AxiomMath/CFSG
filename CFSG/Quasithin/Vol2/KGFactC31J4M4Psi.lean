module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4Pi
public import CFSG.Quasithin.Background.F918T2
public import CFSG.Quasithin.Background.F918T7
public import CFSG.Quasithin.Background.F918U5
public import CFSG.Quasithin.Vol2.KGFactC31J4M4F

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B5.Ln (mat dmat ofGL)
open scoped Matrix

theorem cast_bit (c p : ℕ) : ((D35Chk.bit c p : ℕ) : ZMod 2) = if c.testBit p then 1 else 0 := by
  have h : D35Chk.bit c p = if c.testBit p then 1 else 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [D35Chk.bit, Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ p) with h | h <;> simp [h]
  rw [h]
  split_ifs <;> simp

@[expose] def altV (v : Fin 10 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ∑ p : Fin 10, v p • D35Chk.bm (D35Chk.altE p)

theorem altV_codeVec (c : ℕ) : altV (codeVec c) = D35Chk.bm (D35Chk.altSum c) := by
  rw [D35Chk.altSum, D35Chk.bm_colSum, altV, ← Fin.sum_univ_eq_sum_range
    (fun p => ((D35Chk.bit c p : ℕ) : ZMod 2) • D35Chk.bm (D35Chk.altE p))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cast_bit]
  rfl

theorem altV_upper (v : Fin 10 → ZMod 2) (p : Fin 10) :
    altV v (D35Chk.upI p) (D35Chk.upJ p) = v p := by
  obtain ⟨c, -, rfl⟩ := exists_codeVec v
  rw [altV_codeVec, D35Chk.bm_altSum_upper c p.2, cast_bit]
  rfl

theorem altV_injective : Function.Injective altV := fun v w h => funext fun p => by
  rw [← altV_upper v p, ← altV_upper w p, h]

theorem altE_mem : ∀ p : Fin 10, D35Chk.bm (D35Chk.altE p) ∈ altMat 5 := by
  intro p
  rw [mem_altMat]
  revert p
  decide +kernel

theorem altV_mem (v : Fin 10 → ZMod 2) : altV v ∈ altMat 5 :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (altE_mem p)

theorem altV_coords {A : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : A ∈ altMat 5) :
    altV (fun p : Fin 10 => A (D35Chk.upI p) (D35Chk.upJ p)) = A := by
  have h := bm_altSum_codeOfMat hA
  rw [← altV_codeVec] at h
  have hc : codeVec (D35Chk.codeOfMat A) = fun p : Fin 10 => A (D35Chk.upI p) (D35Chk.upJ p) := by
    funext p
    rw [codeVec, testBit_codeOfMat A p.2]
    generalize A (D35Chk.upI p) (D35Chk.upJ p) = x
    revert x
    decide
  rw [hc] at h
  exact h

@[expose] noncomputable def psiMat (γ : ↥(StatedSL 5 (ZMod 2))) :
    Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  Matrix.of fun r j =>
    (dmat γ * D35Chk.bm (D35Chk.altE j) * (dmat γ)ᵀ) (D35Chk.upI r) (D35Chk.upJ r)

theorem altV_psiMat (γ : ↥(StatedSL 5 (ZMod 2))) (v : Fin 10 → ZMod 2) :
    altV (psiMat γ *ᵥ v) = dmat γ * altV v * (dmat γ)ᵀ := by
  have hA := congr_mem_altMat (dmat γ) (altV_mem v)
  rw [← altV_coords hA]
  refine congrArg altV (funext fun r => ?_)
  simp only [psiMat, Matrix.mulVec, dotProduct, Matrix.of_apply, altV, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem psiMat_mul (γ δ : ↥(StatedSL 5 (ZMod 2))) : psiMat (γ * δ) = psiMat γ * psiMat δ := by
  refine matrix_ext_mulVec fun v => altV_injective ?_
  rw [← Matrix.mulVec_mulVec, altV_psiMat, altV_psiMat, altV_psiMat, B5.Ln.dmat_mul,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem psiMat_one : psiMat 1 = 1 := by
  refine matrix_ext_mulVec fun v => altV_injective ?_
  rw [altV_psiMat, B5.Ln.dmat_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mulVec]

@[expose] noncomputable def psi : ↥(StatedSL 5 (ZMod 2)) →* GL (Fin 10) (ZMod 2) where
  toFun γ := ⟨psiMat γ, psiMat γ⁻¹, by rw [← psiMat_mul, mul_inv_cancel, psiMat_one],
    by rw [← psiMat_mul, inv_mul_cancel, psiMat_one]⟩
  map_one' := Units.ext psiMat_one
  map_mul' γ δ := Units.ext (psiMat_mul γ δ)

theorem psi_coe (γ : ↥(StatedSL 5 (ZMod 2))) :
    ((psi γ : GL (Fin 10) (ZMod 2)) : Matrix (Fin 10) (Fin 10) (ZMod 2)) = psiMat γ := rfl

theorem psiMat_eq_one {γ : ↥(StatedSL 5 (ZMod 2))} (h : psiMat γ = 1) : γ = 1 := by
  have h1 : ∀ B, altMulAct (B5.Ln.dualHom γ) B = B := by
    intro B
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [coe_toAdd_altMulAct, B5.Ln.mat_dualHom]
    have hB := (Multiplicative.toAdd B).2
    rw [← altV_coords hB, ← altV_psiMat, h, Matrix.one_mulVec]
  have h2 := altMulAct_faithful h1
  have h3 : dmat γ = 1 := by rw [← B5.Ln.mat_dualHom, h2, B5.Ln.mat_one]
  have h4 : mat γ⁻¹ = 1 := by
    have := congrArg Matrix.transpose h3
    rwa [B5.Ln.dmat, Matrix.transpose_transpose, Matrix.transpose_one] at this
  apply B5.Ln.mat_injective
  rw [B5.Ln.mat_one]
  calc mat γ = mat γ * mat γ⁻¹ := by rw [h4, Matrix.mul_one]
    _ = 1 := B5.Ln.mat_mul_inv γ

theorem psi_injective : Function.Injective psi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  exact psiMat_eq_one (congrArg Units.val (MonoidHom.mem_ker.mp hγ))

theorem altV_psiMat_codeVec {γ : ↥(StatedSL 5 (ZMod 2))} {gi : ℕ} (hgi : mat γ⁻¹ = D35Chk.bm gi)
    (c : ℕ) : altV (psiMat γ *ᵥ codeVec c) =
      D35Chk.bm (D35Chk.bmul (D35Chk.bmul (D35Chk.bT gi) (D35Chk.altSum c)) gi) := by
  rw [altV_psiMat, altV_codeVec, D35Chk.bm_bmul, D35Chk.bm_bmul, D35Chk.bm_bT, B5.Ln.dmat, hgi,
    Matrix.transpose_transpose]

theorem psiMat_codeVec {γ : ↥(StatedSL 5 (ZMod 2))} {gi c c' : ℕ} (hgi : mat γ⁻¹ = D35Chk.bm gi)
    (h : D35Chk.bmul (D35Chk.bmul (D35Chk.bT gi) (D35Chk.altSum c)) gi = D35Chk.altSum c') :
    psiMat γ *ᵥ codeVec c = codeVec c' :=
  altV_injective (by rw [altV_psiMat_codeVec hgi, h, altV_codeVec])

theorem ctab_chk : ∀ w < 2, ∀ j < 10,
    D35Chk.bmul (D35Chk.bmul (D35Chk.bT (gInvCode w)) (D35Chk.altSum (2 ^ j))) (gInvCode w) =
      D35Chk.altSum ((cTab.getD w []).getD j 0) := by
  decide +kernel

theorem codeVec_two_pow (j : Fin 10) : codeVec (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext i
  rw [codeVec, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem psiMat_gam_col {w : ℕ} (hw : w < 2) (j : Fin 10) :
    (fun r => psiMat (gam w) r j) = codeVec ((cTab.getD w []).getD j 0) := by
  have h := psiMat_codeVec (mat_gam_inv w) (ctab_chk w hw j j.2)
  rw [codeVec_two_pow] at h
  rw [← h]
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

@[expose] def tvU (p : ℕ) : ℕ := Nat.xor D35Chk.idm (2 ^ (D35Chk.upos.getD p 0))

theorem tvU_spec : ∀ p : Fin 10, D35Chk.bmul (tvU p) (tvU p) = D35Chk.idm ∧
    D35Chk.bmul (tvU p) (tvU p) = D35Chk.idm := by decide +kernel

@[expose] def tvEl (p : Fin 10) : ↥(StatedSL 5 (ZMod 2)) := ofGL (glOf (tvU p) (tvU p) (tvU_spec p))

theorem tvU_lower : ∀ p < 10, ∀ i < 5, ∀ j < i, (tvU p).testBit (5 * i + j) = false := by
  decide +kernel

theorem tvEl_mem (p : Fin 10) : tvEl p ∈ unitri5 := fun i j hji => by
  show (if (tvU p).testBit (5 * (i : ℕ) + j) then 1 else 0) = 0
  rw [tvU_lower p p.2 i i.2 j hji]
  rfl

theorem fixU_chk : ∀ c < 1024, (∀ p : Fin 10,
    D35Chk.bmul (D35Chk.bmul (D35Chk.bT (tvU p)) (D35Chk.altSum c)) (tvU p) = D35Chk.altSum c) →
    c = 0 ∨ c = 512 := by
  decide +kernel

@[expose] def permList : List ℕ :=
  [16910376, 4720680, 16910593, 4276264, 4720897, 16916545, 4261384, 4276481, 4726849, 17043521]

@[expose] def permInvList : List ℕ :=
  [16818306, 8437890, 16851073, 4243714, 8470657, 16916545, 2146564, 4276481, 8536129, 17043521]

theorem perm_spec : ∀ p : Fin 10,
    D35Chk.bmul (permList.getD p 0) (permInvList.getD p 0) = D35Chk.idm ∧
      D35Chk.bmul (permInvList.getD p 0) (permList.getD p 0) = D35Chk.idm := by decide +kernel

@[expose] def permEl (p : Fin 10) : ↥(StatedSL 5 (ZMod 2)) :=
  ofGL (glOf (permList.getD p 0) (permInvList.getD p 0) (perm_spec p))

theorem perm_chk : ∀ p : Fin 10, D35Chk.bmul (D35Chk.bmul (D35Chk.bT (permInvList.getD p 0))
    (D35Chk.altSum 512)) (permInvList.getD p 0) = D35Chk.altSum (2 ^ (p : ℕ)) := by
  decide +kernel

theorem psi_irred (W : AddSubgroup (Fin 10 → ZMod 2))
    (hW : ∀ γ : ↥(StatedSL 5 (ZMod 2)), ∀ v ∈ W, psiMat γ *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 ↥unitri5 := IsPGroup.of_card card_unitri5
  let act : MulAction ↥unitri5 ↥W :=
    { smul := fun u w => ⟨psiMat (u : ↥(StatedSL 5 (ZMod 2))) *ᵥ (w : Fin 10 → ZMod 2),
        hW u w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show psiMat ((1 : ↥unitri5) : ↥(StatedSL 5 (ZMod 2))) *ᵥ (w : Fin 10 → ZMod 2) = w
        rw [OneMemClass.coe_one, psiMat_one, Matrix.one_mulVec])
      mul_smul := fun u u' w => Subtype.ext (by
        show psiMat ((u * u' : ↥unitri5) : ↥(StatedSL 5 (ZMod 2))) *ᵥ (w : Fin 10 → ZMod 2) =
          psiMat u *ᵥ (psiMat u' *ᵥ (w : Fin 10 → ZMod 2))
        rw [Subgroup.coe_mul, psiMat_mul, Matrix.mulVec_mulVec]) }
  have hdvd : 2 ∣ Nat.card ↥W := by
    have h1 : Nat.card ↥W ∣ 2 ^ 10 := by
      have := AddSubgroup.card_addSubgroup_dvd_card W
      rwa [Nat.card_eq_fintype_card (α := Fin 10 → ZMod 2), Fintype.card_fun, ZMod.card,
        Fintype.card_fin] at this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hbot (AddSubgroup.eq_bot_of_card_eq W (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 2 hk0
  have h0 : (0 : ↥W) ∈ MulAction.fixedPoints ↥unitri5 ↥W := fun u => Subtype.ext (by
    show psiMat (u : ↥(StatedSL 5 (ZMod 2))) *ᵥ (0 : Fin 10 → ZMod 2) = 0
    exact Matrix.mulVec_zero _)
  obtain ⟨b, hb, hb0⟩ := hU.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥W) hdvd h0
  obtain ⟨c, hc, hcb⟩ := exists_codeVec (b : Fin 10 → ZMod 2)
  have hfix : ∀ u ∈ unitri5, psiMat u *ᵥ codeVec c = codeVec c := fun u hu => by
    rw [hcb]
    exact congrArg Subtype.val (hb ⟨u, hu⟩)
  have h512 : c = 512 := by
    refine (fixU_chk c hc fun p => ?_).resolve_left fun h => hb0 (Subtype.ext ?_)
    · have e := hfix (tvEl p) (tvEl_mem p)
      have e2 := congrArg altV e
      rw [altV_psiMat_codeVec (rfl : mat (tvEl p)⁻¹ = D35Chk.bm (tvU p)), altV_codeVec] at e2
      exact D35Chk.bm_inj (D35Chk.bmul_lt _ _) (D35Chk.colSum_lt D35Chk.altE_lt c) e2
    · rw [← hcb, h]
      funext i
      simp [codeVec]
  subst h512
  have hcW : codeVec 512 ∈ W := by rw [hcb]; exact b.2
  have hbasis : ∀ p : Fin 10, (Pi.single p 1 : Fin 10 → ZMod 2) ∈ W := fun p => by
    have e := psiMat_codeVec (rfl : mat (permEl p)⁻¹ = D35Chk.bm (permInvList.getD p 0))
      (perm_chk p)
    rw [codeVec_two_pow] at e
    rw [← e]
    exact hW _ _ hcW
  rw [eq_top_iff]
  intro v _
  rw [pi_eq_sum_univ' v]
  refine W.sum_mem fun p _ => ?_
  rcases zmod2_cases (v p) with h | h <;> rw [h]
  · rw [zero_smul]
    exact W.zero_mem
  · rw [one_smul]
    exact hbasis p

end CFSG.Quasithin.KGC31.J4M4

end
