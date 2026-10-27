module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphCent
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveConjFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private lemma ggHalfGraphI1_f2_eq_one_of_ne_zero {z : F2} (hz : z ≠ 0) : z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
  exact (huniq z hz).trans (huniq 1 one_ne_zero).symm

private lemma ggHalfGraphI1_transvection_irrel {N : ℕ} {i j : Fin N} (h h' : i ≠ j) (c : F2) :
    SpecialLinearGroup.transvection h c = SpecialLinearGroup.transvection h' c :=
  Subtype.ext rfl

private lemma ggHalfGraphI1_update_eq_single (i : Fin 6) (x : F2) :
    Function.update (0 : Fin 6 → F2) i x = Pi.single (M := fun _ => F2) i x := by
  funext j
  rw [Function.update_apply, Pi.single_apply]
  rfl

private noncomputable abbrev ggHalfGraphI1_v (i : Fin 6) : Fin 6 → F2 :=
  Pi.single (M := fun _ => F2) i 1

private lemma ggHalfGraphI1_v_same (i : Fin 6) : ggHalfGraphI1_v i i = 1 :=
  Pi.single_eq_same i 1

private lemma ggHalfGraphI1_v_ne {i j : Fin 6} (h : j ≠ i) : ggHalfGraphI1_v i j = 0 :=
  Pi.single_eq_of_ne h 1

private def ggHalfGraphI1_sigma : Equiv.Perm (Fin 6) where
  toFun := ggHalfSLoc
  invFun := ggHalfSLoc
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private noncomputable abbrev ggHalfGraphI1_tvUp (k : Fin 5) : SpecialLinearGroup (Fin 6) F2 :=
  SpecialLinearGroup.transvection
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1

private noncomputable abbrev ggHalfGraphI1_tvDn (k : Fin 5) : SpecialLinearGroup (Fin 6) F2 :=
  SpecialLinearGroup.transvection
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' 1

private lemma ggHalfGraphI1_slLower2Hom_transvection {m : ℕ} {i j : Fin (m + 1)}
    (hij : i ≠ j) (c : F2) :
    slLower2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

private lemma ggHalfGraphI1_slUpper2Hom_transvection {m : ℕ} {i j : Fin (m + 1)}
    (hij : i ≠ j) (c : F2) :
    slUpper2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c := by
  rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_transvection,
    slUpperBlockHom_transvection]

private lemma ggHalfGraphI1_graphAut_transvection {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut N F2
      (SpecialLinearGroup.transvection hab 1) =
      SpecialLinearGroup.transvection hab.symm 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    Matrix.SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, hneg]

private lemma ggHalfGraphI1_graphAut_tvUp (k : Fin 5) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2
      (ggHalfGraphI1_tvUp k) = ggHalfGraphI1_tvDn k :=
  ggHalfGraphI1_graphAut_transvection _

private lemma ggHalfGraphI1_graphAut_tvDn (k : Fin 5) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2
      (ggHalfGraphI1_tvDn k) = ggHalfGraphI1_tvUp k :=
  ggHalfGraphI1_graphAut_transvection _

private lemma ggHalfGraphI1_weylRep_eq_transvections (n : ℕ) (k : Fin n) :
    weylRep n F2 k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' 1 *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
  rw [← slPerm_swap_castSucc_succ (F := F2) gf2_two k]
  exact slPerm_swap_eq_transvections gf2_two
    (show k.castSucc ≠ k.succ from (Fin.castSucc_lt_succ).ne)

private lemma ggHalfGraphI1_weylRep_eq_slPerm (n : ℕ) (k : Fin n) :
    weylRep n F2 k = slPerm gf2_two (Equiv.swap k.castSucc k.succ) :=
  (slPerm_swap_castSucc_succ (F := F2) gf2_two k).symm

private lemma ggHalfGraphI1_omegaBlock_eq_weyl_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k = weylRep n F2 k *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 :=
  rfl

private lemma ggHalfGraphI1_transvection_one_mul_self {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, show (1 : F2) + 1 = 0 from by
    rw [one_add_one_eq_two, gf2_two]]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private lemma ggHalfGraphI1_mul_self_mul_self {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) : (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private lemma ggHalfGraphI1_omegaBlock_mul_aux {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) : x * (x * y) = y := by
  rw [show x * (x * y) = (x * x) * y by group, hx, one_mul]

private lemma ggHalfGraphI1_omegaBlock_eq_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' 1 := by
  rw [ggHalfGraphI1_omegaBlock_eq_weyl_mul, ggHalfGraphI1_weylRep_eq_transvections]
  exact ggHalfGraphI1_mul_self_mul_self (ggHalfGraphI1_transvection_one_mul_self _)

private lemma ggHalfGraphI1_transvection_mul_omegaBlock (n : ℕ) (k : Fin n) :
    SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
        omegaBlock n k =
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' 1 := by
  rw [ggHalfGraphI1_omegaBlock_eq_mul]
  exact ggHalfGraphI1_omegaBlock_mul_aux (ggHalfGraphI1_transvection_one_mul_self _)

private lemma ggHalfGraphI1_conj_single {c : SpecialLinearGroup (Fin 6) F2}
    {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (h : c * SpecialLinearGroup.transvection hij 1 * c⁻¹ =
      SpecialLinearGroup.transvection hkl 1) :
    (c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1 *
      ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) =
      Matrix.single k l 1 := by
  have key : (c : Matrix (Fin 6) (Fin 6) F2) * (1 + Matrix.single i j 1) *
      ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) =
      1 + Matrix.single k l 1 := by
    have hh := congrArg (fun x : SpecialLinearGroup (Fin 6) F2 =>
      (x : Matrix (Fin 6) (Fin 6) F2)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_inv] using hh
  have hC : (c : Matrix (Fin 6) (Fin 6) F2) *
      ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [mul_add, add_mul, mul_one, hC] at key
  exact add_left_cancel key

private lemma ggHalfGraphI1_column {c : SpecialLinearGroup (Fin 6) F2}
    {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (h : (c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1 *
      ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) =
      Matrix.single k l 1) :
    (c : Matrix (Fin 6) (Fin 6) F2).mulVec (ggHalfGraphI1_v i) = ggHalfGraphI1_v k := by
  have hsingle : Matrix.single i j (1 : F2) *ᵥ ggHalfGraphI1_v j = ggHalfGraphI1_v i := by
    rw [Matrix.single_mulVec, ggHalfGraphI1_v_same j, mul_one]
    exact ggHalfGraphI1_update_eq_single i (1 : F2)
  have h2 : (c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1 =
      Matrix.single k l 1 * (c : Matrix (Fin 6) (Fin 6) F2) := by
    have hc : (((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)) *
        (c : Matrix (Fin 6) (Fin 6) F2) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc (c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1
        = (c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1 *
            ((((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)) *
              (c : Matrix (Fin 6) (Fin 6) F2)) := by rw [hc, mul_one]
      _ = ((c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1 *
            ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)) *
            (c : Matrix (Fin 6) (Fin 6) F2) :=
          (mul_assoc ((c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1)
            (((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2))
            (c : Matrix (Fin 6) (Fin 6) F2)).symm
      _ = Matrix.single k l 1 * (c : Matrix (Fin 6) (Fin 6) F2) := by rw [h]
  have hv : (c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v i =
      Matrix.single k l 1 *ᵥ ((c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v j) := by
    calc (c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v i
        = (c : Matrix (Fin 6) (Fin 6) F2) *ᵥ
            (Matrix.single i j 1 *ᵥ ggHalfGraphI1_v j) := by rw [hsingle]
      _ = ((c : Matrix (Fin 6) (Fin 6) F2) * Matrix.single i j 1) *ᵥ
            ggHalfGraphI1_v j := by rw [Matrix.mulVec_mulVec]
      _ = (Matrix.single k l 1 * (c : Matrix (Fin 6) (Fin 6) F2)) *ᵥ
            ggHalfGraphI1_v j := by rw [h2]
      _ = Matrix.single k l 1 *ᵥ
            ((c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v j) := by
            rw [Matrix.mulVec_mulVec]
  have hne : ((c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v j) l ≠ 0 := by
    intro h0
    have hci : (((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)) *
        (c : Matrix (Fin 6) (Fin 6) F2) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hzero : (c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v i = 0 := by
      rw [hv, Matrix.single_mulVec, h0]
      simp
    have hviz : ggHalfGraphI1_v i = 0 := by
      calc ggHalfGraphI1_v i
          = (1 : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v i := by
              rw [Matrix.one_mulVec]
        _ = ((((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)) *
              (c : Matrix (Fin 6) (Fin 6) F2)) *ᵥ ggHalfGraphI1_v i := by rw [hci]
        _ = ((c⁻¹ : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2) *ᵥ
              ((c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v i) := by
              rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hzero, Matrix.mulVec_zero]
    have h1 : (ggHalfGraphI1_v i) i = (0 : Fin 6 → F2) i := congrFun hviz i
    rw [ggHalfGraphI1_v_same] at h1
    exact one_ne_zero h1
  rw [hv, Matrix.single_mulVec]
  rw [ggHalfGraphI1_f2_eq_one_of_ne_zero hne, mul_one]
  exact ggHalfGraphI1_update_eq_single k (1 : F2)

private lemma ggHalfGraphI1_column_of_conj_transvection {c : SpecialLinearGroup (Fin 6) F2}
    {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (h : c * SpecialLinearGroup.transvection hij 1 * c⁻¹ =
      SpecialLinearGroup.transvection hkl 1) :
    (c : Matrix (Fin 6) (Fin 6) F2).mulVec (ggHalfGraphI1_v i) = ggHalfGraphI1_v k :=
  ggHalfGraphI1_column hij hkl (ggHalfGraphI1_conj_single hij hkl h)

private lemma ggHalfGraphI1_eq_signedPerm {c : SpecialLinearGroup (Fin 6) F2}
    (hcol : ∀ i : Fin 6, (c : Matrix (Fin 6) (Fin 6) F2).mulVec (ggHalfGraphI1_v i) =
      ggHalfGraphI1_v (ggHalfGraphI1_sigma i)) :
    (c : Matrix (Fin 6) (Fin 6) F2) = signedPerm ggHalfGraphI1_sigma 1 := by
  ext a b
  calc (c : Matrix (Fin 6) (Fin 6) F2) a b
      = ((c : Matrix (Fin 6) (Fin 6) F2) *ᵥ ggHalfGraphI1_v b) a := by
          rw [Matrix.mulVec_single]; simp [Matrix.col_apply]
    _ = (ggHalfGraphI1_v (ggHalfGraphI1_sigma b)) a := by rw [hcol b]
    _ = signedPerm ggHalfGraphI1_sigma 1 a b := by
          rw [signedPerm_apply]
          by_cases h : a = ggHalfGraphI1_sigma b
          · rw [h, ggHalfGraphI1_v_same, if_pos rfl]; rfl
          · rw [ggHalfGraphI1_v_ne (show a ≠ ggHalfGraphI1_sigma b from h), if_neg h]

private lemma ggHalfGraphI1_sigmaPerm_conj_swap23 :
    (sigmaPerm 3 : Equiv.Perm (Fin 6)) *
        Equiv.swap ((2 : Fin 5).castSucc) ((2 : Fin 5).succ) *
        (sigmaPerm 3)⁻¹ =
      Equiv.swap ((0 : Fin 5).castSucc) ((0 : Fin 5).succ) := by
  decide

private lemma ggHalfGraphI1_tau_conj_swap01 :
    (tauPerm 3 : Equiv.Perm (Fin 6)) *
        Equiv.swap ((0 : Fin 5).castSucc) ((0 : Fin 5).succ) *
        (tauPerm 3)⁻¹ =
      Equiv.swap ((4 : Fin 5).castSucc) ((4 : Fin 5).succ) := by
  decide

namespace GGHalfCtx

theorem graph_I1 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂) :
    ∀ c d : Fin 6, c ≠ d →
      gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹ =
        hElt φ₂ * φ₁ (slE (ggHalfSLoc d) (ggHalfSLoc c)) * (hElt φ₂)⁻¹ := by
  obtain ⟨α, hα⟩ := h.exists_alpha_five
  obtain ⟨c, ε, hε, hαc⟩ := aut_sl_gf2 (d := 6) (by norm_num) α
  have hc1 : ε = 1 := by
    interval_cases ε
    · exfalso
      refine hg ⟨c, fun s => ?_⟩
      have hconj : ∀ t, α t = c * t * c⁻¹ := by
        intro t
        have hα0 : α = MulAut.conj c := by rw [hαc, pow_zero, mul_one]
        rw [hα0, MulAut.conj_apply]
      rw [← hconj s]
      exact (hα s).symm
    · rfl
  subst hc1
  have hαc' : α = MulAut.conj c * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2 := by
    rw [hαc, pow_one]
  have key : ∀ {s t : SpecialLinearGroup (Fin 6) F2},
      gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ = hElt φ₂ * φ₁ t * (hElt φ₂)⁻¹ → α s = t := by
    intro s t hst
    have h1 : hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = hElt φ₂ * φ₁ t * (hElt φ₂)⁻¹ := by
      rw [hα s, hst]
    exact h.coords.inj₁ (mul_left_cancel (mul_right_cancel h1))
  have hAv : α (omegaBlock 5 (0 : Fin 5)) = omegaBlock 5 (0 : Fin 5) :=
    key (alpha_v h)
  have hAw : α (omegaBlock 5 (4 : Fin 5)) = omegaBlock 5 (2 : Fin 5) :=
    key (alpha_w h)
  have hAv' : α (omegaBlock 5 (0 : Fin 5)) = omegaBlock 5 (0 : Fin 5) := by
    simpa using hAv
  have hAw' : α (omegaBlock 5 (4 : Fin 5)) = omegaBlock 5 (2 : Fin 5) := by
    simpa using hAw
  have hAW0 : α (weylRep 5 F2 (0 : Fin 5)) = weylRep 5 F2 (0 : Fin 5) := by
    have hK : hElt φ₂ ∈ K := by
      rw [← h.coords.range₂]
      exact ⟨slPerm gf2_two (tauPerm 3), rfl⟩
    have hagree : φ₂ (weylRep 5 F2 (0 : Fin 5)) = φ₁ (weylRep 5 F2 (2 : Fin 5)) := by
      have hh := congrArg (fun f : SpecialLinearGroup (Fin 4) F2 →* G =>
        f (weylRep 3 F2 (0 : Fin 3))) h.coords.agree
      simp only [MonoidHom.comp_apply] at hh
      rw [slLower2Hom_weylRep, slUpper2Hom_weylRep] at hh
      simpa using hh.symm
    have hperm : slPerm gf2_two (sigmaPerm 3) * weylRep 5 F2 (2 : Fin 5) *
        (slPerm gf2_two (sigmaPerm 3))⁻¹ = weylRep 5 F2 (0 : Fin 5) := by
      rw [ggHalfGraphI1_weylRep_eq_slPerm 5 (2 : Fin 5),
          ggHalfGraphI1_weylRep_eq_slPerm 5 (0 : Fin 5),
          ← map_inv, ← map_mul, ← map_mul, ggHalfGraphI1_sigmaPerm_conj_swap23]
    have hL : gElt φ₁ * φ₂ (weylRep 5 F2 (0 : Fin 5)) * (gElt φ₁)⁻¹ =
        φ₁ (weylRep 5 F2 (0 : Fin 5)) := by
      rw [hagree, show gElt φ₁ = φ₁ (slPerm gf2_two (sigmaPerm 3)) from rfl]
      rw [← map_inv, ← map_mul, ← map_mul, hperm]
    have hR : hElt φ₂ * φ₁ (weylRep 5 F2 (0 : Fin 5)) * (hElt φ₂)⁻¹ =
        φ₁ (weylRep 5 F2 (0 : Fin 5)) := by
      have hcomm : φ₁ (weylRep 5 F2 (0 : Fin 5)) * hElt φ₂ =
          hElt φ₂ * φ₁ (weylRep 5 F2 (0 : Fin 5)) := by
        show sZero φ₁ * hElt φ₂ = hElt φ₂ * sZero φ₁
        exact sZero_central h (hElt φ₂) hK
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact key (hL.trans hR.symm)
  have hAW2 : α (weylRep 5 F2 (4 : Fin 5)) = weylRep 5 F2 (2 : Fin 5) := by
    have hgL : gElt φ₁ ∈ L := by
      rw [← h.coords.range₁]
      exact ⟨slPerm gf2_two (sigmaPerm 3), rfl⟩
    have hagree : φ₁ (weylRep 5 F2 (2 : Fin 5)) = φ₂ (weylRep 5 F2 (0 : Fin 5)) := by
      have hh := congrArg (fun f : SpecialLinearGroup (Fin 4) F2 →* G =>
        f (weylRep 3 F2 (0 : Fin 3))) h.coords.agree
      simp only [MonoidHom.comp_apply] at hh
      rw [slLower2Hom_weylRep, slUpper2Hom_weylRep] at hh
      exact hh
    have hL : gElt φ₁ * φ₂ (weylRep 5 F2 (4 : Fin 5)) * (gElt φ₁)⁻¹ =
        endT₂ φ₂ := by
      have hcomm : endT₂ φ₂ * gElt φ₁ = gElt φ₁ * endT₂ φ₂ :=
        endT₂_central h (gElt φ₁) hgL
      rw [show φ₂ (weylRep 5 F2 (4 : Fin 5)) = endT₂ φ₂ from rfl,
        ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hperm2 : slPerm gf2_two (tauPerm 3) * weylRep 5 F2 (0 : Fin 5) *
        (slPerm gf2_two (tauPerm 3))⁻¹ = weylRep 5 F2 (4 : Fin 5) := by
      rw [ggHalfGraphI1_weylRep_eq_slPerm 5 (0 : Fin 5),
          ggHalfGraphI1_weylRep_eq_slPerm 5 (4 : Fin 5),
          ← map_inv, ← map_mul, ← map_mul, ggHalfGraphI1_tau_conj_swap01]
    have hR : hElt φ₂ * φ₁ (weylRep 5 F2 (2 : Fin 5)) * (hElt φ₂)⁻¹ =
        endT₂ φ₂ := by
      rw [hagree, show hElt φ₂ = φ₂ (slPerm gf2_two (tauPerm 3)) from rfl]
      rw [← map_inv, ← map_mul, ← map_mul, hperm2]
      rw [show φ₂ (weylRep 5 F2 (4 : Fin 5)) = endT₂ φ₂ from rfl]
    exact key (hL.trans hR.symm)
  have hx01 : α (ggHalfGraphI1_tvUp (0 : Fin 5)) = ggHalfGraphI1_tvUp (0 : Fin 5) := by
    have h := hAv'
    rw [ggHalfGraphI1_omegaBlock_eq_weyl_mul, map_mul, hAW0] at h
    exact mul_left_cancel h
  have hx10 : α (ggHalfGraphI1_tvDn (0 : Fin 5)) = ggHalfGraphI1_tvDn (0 : Fin 5) := by
    have h := hAv'
    rw [ggHalfGraphI1_omegaBlock_eq_mul, map_mul, hx01] at h
    exact mul_left_cancel h
  have hx45 : α (ggHalfGraphI1_tvUp (4 : Fin 5)) = ggHalfGraphI1_tvUp (2 : Fin 5) := by
    have h := hAw'
    rw [ggHalfGraphI1_omegaBlock_eq_weyl_mul, map_mul, hAW2] at h
    exact mul_left_cancel h
  have hx54 : α (ggHalfGraphI1_tvDn (4 : Fin 5)) = ggHalfGraphI1_tvDn (2 : Fin 5) := by
    have h := hAw'
    rw [ggHalfGraphI1_omegaBlock_eq_mul, map_mul, hx45] at h
    have h' : α (ggHalfGraphI1_tvDn (4 : Fin 5)) =
        (ggHalfGraphI1_tvUp (2 : Fin 5))⁻¹ * omegaBlock 5 (2 : Fin 5) := by
      rw [← h]; group
    rw [h', inv_eq_of_mul_eq_one_right (ggHalfGraphI1_transvection_one_mul_self _)]
    exact ggHalfGraphI1_transvection_mul_omegaBlock 5 (2 : Fin 5)
  have hx23 : α (ggHalfGraphI1_tvUp (2 : Fin 5)) = ggHalfGraphI1_tvUp (4 : Fin 5) := by
    have hmem : SpecialLinearGroup.transvection
        (show (2 : Fin 4) ≠ 3 by decide) 1 ∈ slOn 4 {j : Fin 4 | 2 ≤ j.val} :=
      transvection_mem_slOn _ 1 (by decide) (by decide)
    have h := key (alpha_lower h _ hmem)
    simpa [ggHalfGraphI1_slUpper2Hom_transvection, ggHalfGraphI1_slLower2Hom_transvection] using h
  have hx32 : α (ggHalfGraphI1_tvDn (2 : Fin 5)) = ggHalfGraphI1_tvDn (4 : Fin 5) := by
    have hmem : SpecialLinearGroup.transvection
        (show (3 : Fin 4) ≠ 2 by decide) 1 ∈ slOn 4 {j : Fin 4 | 2 ≤ j.val} :=
      transvection_mem_slOn _ 1 (by decide) (by decide)
    have h := key (alpha_lower h _ hmem)
    simpa [ggHalfGraphI1_slUpper2Hom_transvection, ggHalfGraphI1_slLower2Hom_transvection] using h
  have hE10 : c * ggHalfGraphI1_tvDn (0 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvUp (0 : Fin 5) := by
    have h := hx01
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvUp] at h
    exact h
  have hE01 : c * ggHalfGraphI1_tvUp (0 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvDn (0 : Fin 5) := by
    have h := hx10
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvDn] at h
    exact h
  have hE54 : c * ggHalfGraphI1_tvDn (4 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvUp (2 : Fin 5) := by
    have h := hx45
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvUp] at h
    exact h
  have hE45 : c * ggHalfGraphI1_tvUp (4 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvDn (2 : Fin 5) := by
    have h := hx54
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvDn] at h
    exact h
  have hE32 : c * ggHalfGraphI1_tvDn (2 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvUp (4 : Fin 5) := by
    have h := hx23
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvUp] at h
    exact h
  have hE23 : c * ggHalfGraphI1_tvUp (2 : Fin 5) * c⁻¹ = ggHalfGraphI1_tvDn (4 : Fin 5) := by
    have h := hx32
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_tvDn] at h
    exact h
  have hcol : ∀ i : Fin 6, (c : Matrix (Fin 6) (Fin 6) F2).mulVec (ggHalfGraphI1_v i) =
      ggHalfGraphI1_v (ggHalfGraphI1_sigma i) := by
    intro i
    fin_cases i
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 0) (j := 1) (k := 1) (l := 0)
        (by decide) (by decide) hE01
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 1) (j := 0) (k := 0) (l := 1)
        (by decide) (by decide) hE10
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 2) (j := 3) (k := 5) (l := 4)
        (by decide) (by decide) hE23
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 3) (j := 2) (k := 4) (l := 5)
        (by decide) (by decide) hE32
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 4) (j := 5) (k := 3) (l := 2)
        (by decide) (by decide) hE45
    · exact ggHalfGraphI1_column_of_conj_transvection (i := 5) (j := 4) (k := 2) (l := 3)
        (by decide) (by decide) hE54
  have hc_eq : (c : Matrix (Fin 6) (Fin 6) F2) = signedPerm ggHalfGraphI1_sigma 1 :=
    ggHalfGraphI1_eq_signedPerm hcol
  have hc : c = slPerm gf2_two ggHalfGraphI1_sigma := by
    apply Subtype.ext
    rw [coe_slPerm]
    exact hc_eq
  intro a b hab
  have hS : ggHalfSLoc b ≠ ggHalfSLoc a := by
    intro hh
    exact hab (ggHalfGraphI1_sigma.injective (by
      change ggHalfSLoc a = ggHalfSLoc b
      exact hh.symm))
  have hmain : α (slE a b) = slE (ggHalfSLoc b) (ggHalfSLoc a) := by
    rw [slE, dif_neg hab, slE, dif_neg hS]
    rw [hαc', MulAut.mul_apply, MulAut.conj_apply, ggHalfGraphI1_graphAut_transvection hab, hc]
    rw [conj_transvection_of_coe_eq_signedPerm (g := slPerm gf2_two ggHalfGraphI1_sigma)
      (π := ggHalfGraphI1_sigma) (ε := 1) (coe_slPerm gf2_two ggHalfGraphI1_sigma)
      (fun s => by simp) hab.symm 1]
    simp only [Pi.one_apply, one_mul]
    exact ggHalfGraphI1_transvection_irrel _ _ 1
  rw [← hα (slE a b), hmain]

end GGHalfCtx

end CFSG.StandardType

end
