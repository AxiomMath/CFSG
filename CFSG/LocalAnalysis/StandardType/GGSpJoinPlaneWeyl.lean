module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBSp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBLevi

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin Matrix

variable {F : Type} [Field F] {p : ℕ}

private def sl2TransUp (c : F) : SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c

private def sl2TransLow (c : F) : SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c

private theorem coe_sl2TransUp (c : F) :
    ((sl2TransUp c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (0 : Fin 2) 1 c := by
  rw [sl2TransUp, Matrix.SpecialLinearGroup.transvection_coe]

private theorem coe_sl2TransLow (c : F) :
    ((sl2TransLow c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (1 : Fin 2) 0 c := by
  rw [sl2TransLow, Matrix.SpecialLinearGroup.transvection_coe]

private theorem coe_sl2TransUp_inv (c : F) :
    (((sl2TransUp c)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (0 : Fin 2) 1 (-c) := by
  rw [sl2TransUp, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem sl2TransUp_mul_low_mul_self :
    sl2TransUp 1 * sl2TransLow (-1) * sl2TransUp 1 =
      (sl2W : SpecialLinearGroup (Fin 2) F)⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2TransUp, coe_sl2TransLow, coe_sl2W_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

private theorem sl2W_inv_self_of_two (h2 : (2 : F) = 0) :
    (sl2W : SpecialLinearGroup (Fin 2) F)⁻¹ = sl2W := by
  apply inv_eq_of_mul_eq_one_right
  rw [sl2W_mul_sl2W, sp_units_neg_one_eq_one_of_two h2, map_one]

private theorem pairMat_add_single_inl_inr {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (c : F) : pairMat a b (1 + Matrix.single (0 : Fin 2) 1 c) = 1 + Matrix.single a b c := by
  ext x y
  simp only [pairMat, Matrix.of_apply]
  split_ifs <;> simp_all [Matrix.single_apply, eq_comm]

private theorem pairMat_add_single_inr_inl {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (c : F) : pairMat a b (1 + Matrix.single (1 : Fin 2) 0 c) = 1 + Matrix.single b a c := by
  ext x y
  simp only [pairMat, Matrix.of_apply]
  split_ifs <;> simp_all [Matrix.single_apply, eq_comm]

private theorem elt_positiveLong_eq_lam {n : ℕ} (i : Fin n) (c : F) :
    elt (RootSubgroupIndex.positiveLong i) c = lam i (sl2TransUp c) := by
  apply mat_injective
  rw [mat_elt_positiveLong, Matrix.transvection, mat_apply, coe_lam, coe_sl2TransUp]
  exact (pairMat_add_single_inl_inr Sum.inl_ne_inr c).symm

private theorem elt_negativeLong_eq_lam {n : ℕ} (i : Fin n) (c : F) :
    elt (RootSubgroupIndex.negativeLong i) c = lam i (sl2TransLow c) := by
  apply mat_injective
  rw [mat_elt_negativeLong, Matrix.transvection, mat_apply, coe_lam, coe_sl2TransLow]
  exact (pairMat_add_single_inr_inl Sum.inl_ne_inr c).symm

private theorem coe_sl2TransLow_inv (c : F) :
    (((sl2TransLow c)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (1 : Fin 2) 0 (-c) := by
  rw [sl2TransLow, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem elt_difference_eq_rho_up {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F) :
    elt (RootSubgroupIndex.difference i j hij) c = rho i j hij (sl2TransUp c) := by
  apply mat_injective
  rw [mat_elt, mat_apply, coe_rho, coe_sl2TransUp, coe_sl2TransUp_inv,
    pairMat_add_single_inl_inr hij c, pairMat_add_single_inl_inr hij (-c),
    Matrix.transpose_add, Matrix.transpose_one, transpose_single,
    show E F (RootSubgroupIndex.difference i j hij) =
      Matrix.single (Sum.inl i) (Sum.inl j) 1 -
        Matrix.single (Sum.inr j) (Sum.inr i) 1 from rfl]
  ext (x | x) (y | y) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.single_apply, Matrix.one_apply, neg_ite, neg_zero]

private theorem elt_difference_symm_eq_rho_low {n : ℕ} {i j : Fin n} (hij : i ≠ j) {hji : j ≠ i}
    (c : F) : elt (RootSubgroupIndex.difference j i hji) c = rho i j hij (sl2TransLow c) := by
  apply mat_injective
  rw [mat_elt, mat_apply, coe_rho, coe_sl2TransLow, coe_sl2TransLow_inv,
    pairMat_add_single_inr_inl hij c, pairMat_add_single_inr_inl hij (-c),
    Matrix.transpose_add, Matrix.transpose_one, transpose_single,
    show E F (RootSubgroupIndex.difference j i hji) =
      Matrix.single (Sum.inl j) (Sum.inl i) 1 -
        Matrix.single (Sum.inr i) (Sum.inr j) 1 from rfl]
  ext (x | x) (y | y) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.single_apply, Matrix.one_apply, neg_ite, neg_zero]

private theorem weylRep_eq_rho_sl2W_inv {n : ℕ} (k : Fin n) (hk : k.val + 1 < n) :
    weylRep n F k = rho k ⟨k.val + 1, hk⟩ (Fin.ne_of_val_ne (by simp)) (sl2W⁻¹) := by
  rw [weylRep_eq_elt_of_lt hk]
  rw [elt_difference_symm_eq_rho_low (hij := ne_succ' hk)]
  rw [elt_difference_eq_rho_up, ← map_mul, ← map_mul, sl2TransUp_mul_low_mul_self]

private theorem weylRep_eq_lam_sl2W_inv {n : ℕ} (k : Fin n) (hk : ¬ k.val + 1 < n) :
    weylRep n F k = lam k (sl2W⁻¹) := by
  rw [weylRep_eq_elt_of_not_lt hk, elt_positiveLong_eq_lam, elt_negativeLong_eq_lam,
    ← map_mul, ← map_mul, sl2TransUp_mul_low_mul_self]

theorem weylRep_conj_lam_swap (h2 : (2 : F) = 0) {n : ℕ} (k : Fin n) (hk : k.val + 1 < n)
    (g : SpecialLinearGroup (Fin 2) F) :
    weylRep n F k * lam k g * (weylRep n F k)⁻¹ = lam ⟨k.val + 1, hk⟩ g := by
  have hkk' : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  have h := congrArg (fun φ => φ g) (conj_rho_sl2W_comp_lam_fst (k := F) hkk')
  rw [weylRep_eq_rho_sl2W_inv k hk, sl2W_inv_self_of_two h2]
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem weylRep_conj_lam_of_ne (h2 : (2 : F) = 0) {n : ℕ} (k : Fin n) (hk : k.val + 1 < n)
    {i : Fin n} (hik : i ≠ k) (hik' : i ≠ ⟨k.val + 1, hk⟩) (g : SpecialLinearGroup (Fin 2) F) :
    weylRep n F k * lam i g * (weylRep n F k)⁻¹ = lam i g := by
  have hkk' : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  rw [weylRep_eq_rho_sl2W_inv k hk, sl2W_inv_self_of_two h2]
  have hcomm := commute_rho_lam (k := F) hkk' hik hik'
    (sl2W : SpecialLinearGroup (Fin 2) F) g
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem weylRep_conj_lam_long (h2 : (2 : F) = 0) {n : ℕ} (k : Fin n) (hk : ¬ k.val + 1 < n)
    (g : SpecialLinearGroup (Fin 2) F) :
    weylRep n F k * lam k g * (weylRep n F k)⁻¹ = lam k (sl2W * g * sl2W⁻¹) := by
  rw [weylRep_eq_lam_sl2W_inv k hk, ← map_inv, ← map_mul, ← map_mul, inv_inv,
    sl2W_inv_self_of_two h2]

theorem weylRep_conj_lam_long_of_ne (h2 : (2 : F) = 0) {n : ℕ} (k : Fin n) (hk : ¬ k.val + 1 < n)
    {i : Fin n} (hik : i ≠ k) (g : SpecialLinearGroup (Fin 2) F) :
    weylRep n F k * lam i g * (weylRep n F k)⁻¹ = lam i g := by
  rw [weylRep_eq_lam_sl2W_inv k hk]
  have hcomm := commute_lam_lam (k := F) hik.symm (sl2W⁻¹) g
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem involution_conj_mul_inv {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    x * (x * y * x⁻¹) * x⁻¹ = y := by
  calc x * (x * y * x⁻¹) * x⁻¹
      = (x * x) * y * (x⁻¹ * x⁻¹) := by group
    _ = y := by
        rw [hx, one_mul]
        have h : x⁻¹ * x⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hx, inv_one]
        rw [h, mul_one]

private def reindexHom {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) where
  toFun f := f ∘ e
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def invertCoordHom {n : ℕ} (k : Fin n) :
    (Fin n → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) where
  toFun f := Function.update f k (f k)⁻¹
  map_one' := by
    funext i
    rw [Function.update_apply]
    by_cases hik : i = k <;> simp [hik]
  map_mul' f g := by
    funext i
    simp only [Pi.mul_apply]
    rw [Function.update_apply, Function.update_apply, Function.update_apply]
    by_cases hik : i = k
    · rw [hik, if_pos rfl, if_pos rfl, if_pos rfl]
      simp only [Pi.mul_apply, _root_.mul_inv_rev]
      rw [mul_comm]
    · rw [if_neg hik, if_neg hik, if_neg hik]
      rfl

@[simp] private theorem reindexHom_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) : reindexHom e f = f ∘ e := rfl

@[simp] private theorem invertCoordHom_apply {n : ℕ} (k : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) :
    invertCoordHom k f = Function.update f k (f k)⁻¹ := rfl

private theorem mulSingle_comp_swap {n : ℕ} (k l i : Fin n) (a : Multiplicative (ZMod p)) :
    (Pi.mulSingle i a) ∘ (Equiv.swap k l) = Pi.mulSingle (Equiv.swap k l i) a := by
  funext j
  simp only [Function.comp_apply, Pi.mulSingle, Function.update_apply, Pi.one_apply]
  simp only [Equiv.swap_apply_eq_iff]

private theorem update_mulSingle_inv {n : ℕ} (i k : Fin n) (a : Multiplicative (ZMod p)) :
    Function.update (Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a) k
        ((Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a) k)⁻¹ =
      if i = k then Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) k a⁻¹
      else Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a := by
  by_cases hik : i = k
  · rw [hik, if_pos rfl, Pi.mulSingle_eq_same]
    funext j
    rw [Function.update_apply]
    by_cases hjk : j = k
    · subst hjk; rw [if_pos rfl, Pi.mulSingle_eq_same]
    · rw [if_neg hjk, Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) hjk a,
          Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) hjk a⁻¹]
  · rw [if_neg hik]
    have hk : (Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a) k = 1 :=
      Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) (Ne.symm hik) a
    rw [hk, inv_one, ← hk, Function.update_eq_self]

theorem weylRep_conj_spPlaneTorus (h2 : (2 : F) = 0) {n : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    (hζ : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (k : Fin n) (f : Fin n → Multiplicative (ZMod p)) :
    weylRep n F k * spPlaneTorus n ζ f * (weylRep n F k)⁻¹ =
      spPlaneTorus n ζ (spRefl n p k f) := by
  by_cases hk : k.val + 1 < n
  · let k' : Fin n := ⟨k.val + 1, hk⟩
    let A : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F :=
      (MulAut.conj (weylRep n F k)).toMonoidHom.comp (spPlaneTorus n ζ)
    let B : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F :=
      (spPlaneTorus n ζ).comp (reindexHom (Equiv.swap k k'))
    have hAB : A = B := MonoidHom.pi_ext (fun i a => by
      simp only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        reindexHom_apply]
      rw [mulSingle_comp_swap, spPlaneTorus_mulSingle, spPlaneTorus_mulSingle]
      by_cases hik : i = k
      · rw [hik, Equiv.swap_apply_left]
        exact weylRep_conj_lam_swap h2 k hk (ζ a)
      · by_cases hik' : i = k'
        · rw [hik', Equiv.swap_apply_right, ← weylRep_conj_lam_swap h2 k hk (ζ a)]
          exact involution_conj_mul_inv (spWeylRep_mul_self n h2 k)
        · rw [Equiv.swap_apply_of_ne_of_ne hik hik']
          exact weylRep_conj_lam_of_ne h2 k hk hik hik' (ζ a))
    have h := congrArg (fun φ => φ f) hAB
    rw [show spRefl n p k f = f ∘ Equiv.swap k k' from by rw [spRefl, dif_pos hk]; rfl]
    simpa only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      reindexHom_apply] using h
  · let A : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F :=
      (MulAut.conj (weylRep n F k)).toMonoidHom.comp (spPlaneTorus n ζ)
    let B : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F :=
      (spPlaneTorus n ζ).comp (invertCoordHom k)
    have hAB : A = B := MonoidHom.pi_ext (fun i a => by
      simp only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        invertCoordHom_apply]
      rw [spPlaneTorus_mulSingle, update_mulSingle_inv]
      by_cases hik : i = k
      · rw [hik, if_pos rfl, spPlaneTorus_mulSingle, weylRep_conj_lam_long h2 k hk (ζ a), hζ a]
      · rw [if_neg hik, spPlaneTorus_mulSingle]
        exact weylRep_conj_lam_long_of_ne h2 k hk hik (ζ a))
    have h := congrArg (fun φ => φ f) hAB
    simpa [A, B, spRefl, dif_neg hk, invertCoordHom_apply] using h

theorem weylRep_mem_normalizer_spPlaneTorus (h2 : (2 : F) = 0) {n : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    (hζ : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (k : Fin n) :
    weylRep n F k ∈ Subgroup.normalizer ((spPlaneTorus n ζ).range : Set (StatedSp n F)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨spRefl n p k f, (weylRep_conj_spPlaneTorus h2 ζ hζ k f).symm⟩
  · rintro ⟨f', hf'⟩
    refine ⟨spRefl n p k f', ?_⟩
    calc spPlaneTorus n ζ (spRefl n p k f')
        = weylRep n F k * spPlaneTorus n ζ f' * (weylRep n F k)⁻¹ :=
          (weylRep_conj_spPlaneTorus h2 ζ hζ k f').symm
      _ = h := by
          rw [hf']
          exact involution_conj_mul_inv (spWeylRep_mul_self n h2 k)

end CFSG.StandardType.SpJoin

