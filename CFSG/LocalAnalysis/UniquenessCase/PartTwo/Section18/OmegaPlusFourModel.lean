module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Refl2
public import CFSG.Quasithin.Background.HPairGen
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped MatrixGroups Matrix

@[expose] def polQ {K : Type} [Field K] (v w : Fin 2 ⊕ Fin 2 → K) : K :=
  StatedQuadPlus 2 K (v + w) - StatedQuadPlus 2 K v - StatedQuadPlus 2 K w

abbrev stdOmegaModel {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) : OmegaModel (StdMod (Fin 2 ⊕ Fin 2) K) :=
  { K := K, four_le := h4, e := MulEquiv.refl _ }

namespace stdOmegaModel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {h4 : 4 ≤ Nat.card K}

theorem vec (v : Fin 2 ⊕ Fin 2 → K) :
    (stdOmegaModel h4).vec (Multiplicative.ofAdd v) = v := rfl

theorem Q (v : Fin 2 ⊕ Fin 2 → K) :
    (stdOmegaModel h4).Q (Multiplicative.ofAdd v) = StatedQuadPlus 2 K v := rfl

theorem pol (v w : Fin 2 ⊕ Fin 2 → K) :
    (stdOmegaModel h4).pol (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) = polQ v w := by
  simp only [OmegaModel.pol, Q, vec, polQ, ← ofAdd_add]

theorem smul (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (stdOmegaModel h4).smul c (Multiplicative.ofAdd v) = Multiplicative.ofAdd (c • v) := rfl

theorem actHom (γ : GL (Fin 2 ⊕ Fin 2) K) :
    (stdOmegaModel h4).actHom γ = matAut γ := by
  ext x
  rfl

theorem omega (h4 : 4 ≤ Nat.card K) :
    (stdOmegaModel h4).omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := by
  have hfun : (stdOmegaModel h4).actHom = (matHom : GL (Fin 2 ⊕ Fin 2) K →*
      MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) := MonoidHom.ext (fun γ => actHom γ)
  change (StatedOmega (StatedQuadPlus 2 K)).map (stdOmegaModel h4).actHom = _
  rw [hfun, ← natImage_eq_map]

end stdOmegaModel

theorem hasScalarCommutant_statedOmegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    HasScalarCommutant (StatedOmega (StatedQuadPlus 2 K)) := by
  classical
  intro f hf
  let S := stdOmegaModel h4
  have hSω : S.omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := stdOmegaModel.omega h4
  let F : StdMod (Fin 2 ⊕ Fin 2) K →* StdMod (Fin 2 ⊕ Fin 2) K :=
    { toFun := fun w => Multiplicative.ofAdd (f (Multiplicative.toAdd w))
      map_one' := by
        show Multiplicative.ofAdd (f (Multiplicative.toAdd 1)) = 1
        rw [toAdd_one, map_zero, ofAdd_zero]
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (Multiplicative.toAdd (a * b))) =
          Multiplicative.ofAdd (f (Multiplicative.toAdd a)) *
            Multiplicative.ofAdd (f (Multiplicative.toAdd b))
        rw [toAdd_mul, map_add, ofAdd_add] }
  have hF : ∀ h ∈ S.omega0, ∀ w : StdMod (Fin 2 ⊕ Fin 2) K, F (h w) = h (F w) := by
    intro h hh w
    have hmem : h ∈ S.omega := S.omega0_le_omega hh
    rw [hSω, natImage, MonoidHom.mem_range] at hmem
    obtain ⟨γ, hγ⟩ := hmem
    have hγ' : S.actHom (γ : GL (Fin 2 ⊕ Fin 2) K) = h := hγ
    have hw : h w = Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix
        (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd w) := by
      rw [← hγ', stdOmegaModel.actHom]
      rfl
    have hFw : F w = Multiplicative.ofAdd (f (Multiplicative.toAdd w)) := rfl
    rw [hw, hFw, ← hγ', stdOmegaModel.actHom]
    change Multiplicative.ofAdd (f (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix
        (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd w)) =
      Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix
        (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f (Multiplicative.toAdd w))
    rw [hf (γ : GL (Fin 2 ⊕ Fin 2) K) γ.2 (Multiplicative.toAdd w)]
  obtain ⟨c, hc⟩ := S.exists_smul_of_commute_omega0 F hF
  refine ⟨c, fun v => ?_⟩
  have h := hc (Multiplicative.ofAdd v)
  change Multiplicative.ofAdd (f v) = S.smul c (Multiplicative.ofAdd v) at h
  rw [stdOmegaModel.smul] at h
  exact Multiplicative.ofAdd.injective h

private theorem ofMat_add {K : Type} [Add K] (X Y : Matrix (Fin 2) (Fin 2) K) :
    OmegaModel.ofMat (X + Y) = OmegaModel.ofMat X + OmegaModel.ofMat Y := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [OmegaModel.ofMat]

private theorem ofMat_neg {K : Type} [Neg K] (X : Matrix (Fin 2) (Fin 2) K) :
    OmegaModel.ofMat (-X) = -OmegaModel.ofMat X := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [OmegaModel.ofMat]

private theorem ofMat_zero {K : Type} [Zero K] :
    OmegaModel.ofMat (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [OmegaModel.ofMat]

private theorem sl2_transitive {K : Type} [Field K] {x : Fin 2 → K} (hx : x ≠ 0) :
    ∃ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) *ᵥ x = Pi.single 0 1 := by
  classical
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h
      exact hx (funext fun i => by fin_cases i <;> simp [h0, h])
    refine ⟨⟨!![0, (x 1)⁻¹; -(x 1), 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      ring
    · funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1] <;> field_simp
  · refine ⟨⟨!![(x 0)⁻¹, 0; -(x 1), x 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      ring
    · funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] <;> field_simp <;> ring

private theorem exists_sl2_mul_transpose_single {K : Type} [Field K]
    {R : Matrix (Fin 2) (Fin 2) K} (hR : R ≠ 0) (h10 : R 1 0 = 0) (h11 : R 1 1 = 0) :
    ∃ b : SL(2, K), R * (b : Matrix (Fin 2) (Fin 2) K)ᵀ = Matrix.single 0 0 1 := by
  classical
  have hrow : (fun j => R 0 j) ≠ 0 := by
    intro h
    apply hR
    ext i j
    fin_cases i
    · exact congrFun h j
    · fin_cases j
      · exact h10
      · exact h11
  have hb : ∀ b : SL(2, K), (b : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun j => R 0 j) =
      Pi.single 0 1 → R * (b : Matrix (Fin 2) (Fin 2) K)ᵀ = Matrix.single 0 0 1 := by
    intro b hbm
    have hbj : ∀ j, Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) 0 j =
        (b : Matrix (Fin 2) (Fin 2) K) j 0 * R 0 0 +
          (b : Matrix (Fin 2) (Fin 2) K) j 1 * R 0 1 := by
      intro j
      have h := congrFun hbm j
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
      rw [h]
      simp [Matrix.single, Pi.single, Function.update, eq_comm]
    ext i j
    by_cases hi : i = 0
    · subst hi
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single, Fin.sum_univ_two,
        if_true, eq_self_iff_true, and_true]
      rw [mul_comm (R 0 0) ((b : Matrix (Fin 2) (Fin 2) K) j 0),
        mul_comm (R 0 1) ((b : Matrix (Fin 2) (Fin 2) K) j 1), ← hbj j]
      rfl
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
  exact Exists.elim (sl2_transitive hrow) fun b hbm => ⟨b, hb b hbm⟩

theorem isNatIrr_statedOmegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    PairG.IsNatIrr (StatedOmega (StatedQuadPlus 2 K)) := by
  classical
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  have hne : ∃ u ∈ U, u ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot (le_antisymm (fun u hu => by simpa using h u hu) bot_le)
  obtain ⟨u₀, hu₀U, hu₀⟩ := hne
  let S := stdOmegaModel h4
  have hSω : S.omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := stdOmegaModel.omega h4
  have hvec : ∀ v, S.vec (Multiplicative.ofAdd v) = v := fun v => stdOmegaModel.vec v
  let U' : AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {X | OmegaModel.ofMat X ∈ U}
      zero_mem' := by
        change OmegaModel.ofMat (0 : Matrix (Fin 2) (Fin 2) K) ∈ U
        rw [ofMat_zero]; exact U.zero_mem
      add_mem' := fun hX hY => by
        change OmegaModel.ofMat (_ + _) ∈ U
        rw [ofMat_add]; exact U.add_mem hX hY
      neg_mem' := fun hX => by
        change OmegaModel.ofMat (-_) ∈ U
        rw [ofMat_neg]; exact U.neg_mem hX }
  have hmemU' : ∀ X : Matrix (Fin 2) (Fin 2) K, X ∈ U' ↔ OmegaModel.ofMat X ∈ U :=
    fun _ => Iff.rfl
  have hinv : ∀ (p : SL(2, K) × SL(2, K)) {X : Matrix (Fin 2) (Fin 2) K}, X ∈ U' →
      (p.1 : Matrix (Fin 2) (Fin 2) K) * X * (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ U' := by
    intro p X hX
    have hXU : OmegaModel.ofMat X ∈ U := (hmemU' X).mp hX
    have hmem0 : S.jHom p ∈ S.omega0 := ⟨p, rfl⟩
    have hmem : S.jHom p ∈ S.omega := S.omega0_le_omega hmem0
    rw [hSω, natImage, MonoidHom.mem_range] at hmem
    obtain ⟨γ, hγ⟩ := hmem
    have h1 : S.jHom p (Multiplicative.ofAdd (OmegaModel.ofMat X)) =
        Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix
          (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ OmegaModel.ofMat X) := by
      rw [← hγ]
      rfl
    have h2 : S.vec (S.jHom p (Multiplicative.ofAdd (OmegaModel.ofMat X))) =
        OmegaModel.ofMat ((p.1 : Matrix (Fin 2) (Fin 2) K) * X *
          (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
      rw [OmegaModel.vec_jHom]
      simp only [hvec, OmegaModel.toMat_ofMat]
    have h3 : (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        OmegaModel.ofMat X) = OmegaModel.ofMat ((p.1 : Matrix (Fin 2) (Fin 2) K) * X *
          (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
      rw [← h2, h1, hvec]
    have h4 : OmegaModel.ofMat ((p.1 : Matrix (Fin 2) (Fin 2) K) * X *
        (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) ∈ U := by
      rw [← h3]
      exact hU (γ : GL (Fin 2 ⊕ Fin 2) K) γ.2 (OmegaModel.ofMat X) hXU
    exact (hmemU' _).mpr h4
  have hrow : ∃ R : Matrix (Fin 2) (Fin 2) K, R ≠ 0 ∧ R 1 0 = 0 ∧ R 1 1 = 0 ∧ R ∈ U' := by
    by_cases hsec : OmegaModel.toMat u₀ 1 0 = 0 ∧ OmegaModel.toMat u₀ 1 1 = 0
    · refine ⟨OmegaModel.toMat u₀, ?_, hsec.1, hsec.2, ?_⟩
      · intro h
        apply hu₀
        have h0 : OmegaModel.ofMat (OmegaModel.toMat u₀) = 0 := by rw [h, ofMat_zero]
        rwa [OmegaModel.ofMat_toMat] at h0
      · rw [hmemU', OmegaModel.ofMat_toMat]; exact hu₀U
    · push Not at hsec
      let L : SL(2, K) := ⟨!![(1 : K), 1; 0, 1], by
        rw [Matrix.det_fin_two_of]; norm_num⟩
      have hLval : (L : Matrix (Fin 2) (Fin 2) K) = !![(1 : K), 1; 0, 1] := rfl
      have hLX : OmegaModel.ofMat ((L : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat u₀ *
          (1 : SL(2, K))ᵀ) ∈ U := by
        have h := hinv (L, 1) (show OmegaModel.toMat u₀ ∈ U' from by
          rw [hmemU', OmegaModel.ofMat_toMat]; exact hu₀U)
        exact (hmemU' _).mp h
      have hXU : OmegaModel.ofMat (OmegaModel.toMat u₀) ∈ U := by
        rwa [OmegaModel.ofMat_toMat]
      have hsub : OmegaModel.ofMat ((L : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat u₀ *
          (1 : SL(2, K))ᵀ - OmegaModel.toMat u₀) ∈ U := by
        rw [sub_eq_add_neg, ofMat_add, ofMat_neg]
        exact U.add_mem hLX (U.neg_mem hXU)
      have hRmat : (L : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat u₀ *
          (1 : SL(2, K))ᵀ - OmegaModel.toMat u₀ =
          !![OmegaModel.toMat u₀ 1 0, OmegaModel.toMat u₀ 1 1; 0, 0] := by
        rw [hLval, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.sub_apply, Fin.sum_univ_two]
      refine ⟨(L : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat u₀ *
        (1 : SL(2, K))ᵀ - OmegaModel.toMat u₀, ?_, ?_, ?_, ?_⟩
      · rw [hRmat]
        intro hzero
        have h10 : OmegaModel.toMat u₀ 1 0 = 0 := by
          have := congrFun (congrFun hzero 0) 0
          simpa using this
        have h11 : OmegaModel.toMat u₀ 1 1 = 0 := by
          have := congrFun (congrFun hzero 0) 1
          simpa using this
        exact hsec h10 h11
      · rw [hRmat]; simp
      · rw [hRmat]; simp
      · rw [hmemU']; exact hsub
  obtain ⟨R, hRne, hR10, hR11, hRU'⟩ := hrow
  obtain ⟨b, hb⟩ := exists_sl2_mul_transpose_single hRne hR10 hR11
  have hE00 : (Matrix.single 0 0 (1 : K)) ∈ U' := by
    have h := hinv ((1 : SL(2, K)), b) hRU'
    have h' : OmegaModel.ofMat (Matrix.single 0 0 (1 : K)) ∈ U := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, hb] using (hmemU' _).mp h
    exact (hmemU' _).mpr h'
  have hunit : ∀ c : K, ∀ i j : Fin 2, Matrix.single i j c ∈ U' := by
    intro c
    have h00 : Matrix.single 0 0 c ∈ U' := by
      by_cases hc : c = 0
      · subst hc
        simpa using U'.zero_mem
      · let D : SL(2, K) := ⟨!![c, 0; 0, c⁻¹],
          by rw [Matrix.det_fin_two_of]; field_simp; ring⟩
        have hDval : (D : Matrix (Fin 2) (Fin 2) K) = !![c, 0; 0, c⁻¹] := rfl
        have hD : OmegaModel.ofMat ((D : Matrix (Fin 2) (Fin 2) K) *
            Matrix.single 0 0 (1 : K) * (1 : SL(2, K))ᵀ) ∈ U := by
          have h := hinv (D, 1) hE00
          exact (hmemU' _).mp h
        have hDm : (D : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 (1 : K) *
            (1 : SL(2, K))ᵀ = Matrix.single 0 0 c := by
          rw [hDval, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]
          all_goals field_simp
        rw [hDm] at hD
        exact (hmemU' _).mpr hD
    have h10 : Matrix.single 1 0 c ∈ U' := by
      let L : SL(2, K) := ⟨!![(1 : K), 0; 1, 1], by
        rw [Matrix.det_fin_two_of]; norm_num⟩
      have hLval : (L : Matrix (Fin 2) (Fin 2) K) = !![(1 : K), 0; 1, 1] := rfl
      have hL : OmegaModel.ofMat ((L : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 c *
          (1 : SL(2, K))ᵀ) ∈ U := by
        have h := hinv (L, 1) h00
        exact (hmemU' _).mp h
      have hLm : (L : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 c *
          (1 : SL(2, K))ᵀ = Matrix.single 0 0 c + Matrix.single 1 0 c := by
        rw [hLval, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, add_apply, Fin.sum_univ_two, Matrix.single]
      rw [hLm, ofMat_add] at hL
      exact (hmemU' _).mpr (by simpa using U.sub_mem hL ((hmemU' _).mp h00))
    have h01 : Matrix.single 0 1 c ∈ U' := by
      let L : SL(2, K) := ⟨!![(1 : K), 0; 1, 1], by
        rw [Matrix.det_fin_two_of]; norm_num⟩
      have hLval : (L : Matrix (Fin 2) (Fin 2) K) = !![(1 : K), 0; 1, 1] := rfl
      have hR' : OmegaModel.ofMat (Matrix.single 0 0 c *
          (L : Matrix (Fin 2) (Fin 2) K)ᵀ) ∈ U := by
        have h := hinv (1, L) h00
        simpa using (hmemU' _).mp h
      have hRm : Matrix.single 0 0 c * (L : Matrix (Fin 2) (Fin 2) K)ᵀ =
          Matrix.single 0 0 c + Matrix.single 0 1 c := by
        rw [hLval]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, add_apply, Fin.sum_univ_two, Matrix.single]
      rw [hRm, ofMat_add] at hR'
      exact (hmemU' _).mpr (by simpa using U.sub_mem hR' ((hmemU' _).mp h00))
    have h11 : Matrix.single 1 1 c ∈ U' := by
      let W : SL(2, K) := ⟨!![(0 : K), 1; 1, 0], by
        rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩
      have hWval : (W : Matrix (Fin 2) (Fin 2) K) = !![(0 : K), 1; 1, 0] := rfl
      have hW : OmegaModel.ofMat (Matrix.single 1 0 c *
          (W : Matrix (Fin 2) (Fin 2) K)ᵀ) ∈ U := by
        have h := hinv (1, W) h10
        simpa using (hmemU' _).mp h
      have hWm : Matrix.single 1 0 c * (W : Matrix (Fin 2) (Fin 2) K)ᵀ =
          Matrix.single 1 1 c := by
        rw [hWval]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]
      rw [hWm] at hW
      exact (hmemU' _).mpr hW
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hU'top : U' = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have hX : X = ∑ i, ∑ j, Matrix.single i j (X i j) := Matrix.matrix_eq_sum_single X
    rw [hX]
    exact U'.sum_mem fun i _ => U'.sum_mem fun j _ => hunit (X i j) i j
  rw [eq_top_iff]
  intro v _
  have hv : OmegaModel.toMat v ∈ U' := by rw [hU'top]; trivial
  rw [hmemU'] at hv
  rwa [OmegaModel.ofMat_toMat] at hv

theorem polQ_comm {K : Type} [Field K] [CharP K 2] (v w : Fin 2 ⊕ Fin 2 → K) :
    polQ v w = polQ w v := by
  simp only [polQ, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two,
    Pi.add_apply]
  ring

theorem polQ_self {K : Type} [Field K] [CharP K 2] (v : Fin 2 ⊕ Fin 2 → K) :
    polQ v v = 0 := by
  simp only [polQ, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two,
    Pi.add_apply]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (v (Sum.inl 0) * v (Sum.inr 0) +
    v (Sum.inl 1) * v (Sum.inr 1)) * h2

theorem polQ_add_right {K : Type} [Field K] [CharP K 2] (v w w' : Fin 2 ⊕ Fin 2 → K) :
    polQ v (w + w') = polQ v w + polQ v w' := by
  simp only [polQ, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two,
    Pi.add_apply]
  ring

theorem polQ_sub_right {K : Type} [Field K] [CharP K 2] (v w w' : Fin 2 ⊕ Fin 2 → K) :
    polQ v (w - w') = polQ v w - polQ v w' := by
  have h1 := polQ_add_right v (w - w') w'
  rw [sub_add_cancel] at h1
  linear_combination -h1

theorem polQ_add_left {K : Type} [Field K] [CharP K 2] (v v' w : Fin 2 ⊕ Fin 2 → K) :
    polQ (v + v') w = polQ v w + polQ v' w := by
  rw [polQ_comm, polQ_add_right, polQ_comm v w, polQ_comm v' w]

theorem polQ_sub_left {K : Type} [Field K] [CharP K 2] (v v' w : Fin 2 ⊕ Fin 2 → K) :
    polQ (v - v') w = polQ v w - polQ v' w := by
  have h1 := polQ_add_left (v - v') v' w
  rw [sub_add_cancel] at h1
  linear_combination -h1

theorem polQ_smul_right {K : Type} [Field K] [CharP K 2] (c : K) (v w : Fin 2 ⊕ Fin 2 → K) :
    polQ v (c • w) = c * polQ v w := by
  simp only [polQ, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  ring

theorem polQ_smul_left {K : Type} [Field K] [CharP K 2] (c : K) (v w : Fin 2 ⊕ Fin 2 → K) :
    polQ (c • v) w = c * polQ v w := by
  rw [polQ_comm, polQ_smul_right, polQ_comm w v]

theorem eq_zero_of_polQ_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {v : Fin 2 ⊕ Fin 2 → K} (h : ∀ w, polQ v w = 0) : v = 0 := by
  have h1 : (stdOmegaModel h4).ofVec v = 1 := by
    refine (stdOmegaModel h4).eq_one_of_pol_eq_zero fun w => ?_
    let x := (stdOmegaModel h4).vec w
    have hw : Multiplicative.ofAdd x = w := OmegaModel.ofVec_vec _ w
    have hofv : (stdOmegaModel h4).ofVec v = Multiplicative.ofAdd v := rfl
    rw [hofv, ← hw, stdOmegaModel.pol]
    exact h x
  have h2 : Multiplicative.ofAdd v = (1 : StdMod (Fin 2 ⊕ Fin 2) K) := h1
  simpa using congrArg Multiplicative.toAdd h2

theorem exists_polQ_ne_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {e : Fin 2 ⊕ Fin 2 → K} (he : e ≠ 0) : ∃ v, polQ v e ≠ 0 := by
  by_contra h
  push Not at h
  exact he (eq_zero_of_polQ_eq_zero h4 fun v => (polQ_comm e v).trans (h v))

private theorem card_fixV_of_rkIdx_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {a : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hrk : rkIdx (fixV (Subgroup.zpowers a)) = 2) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // a v = v} = 64 := by
  have hW : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = 2 ^ 8 := by
    rw [H.card_stdMod, hK]
    norm_num [Fintype.card_sum]
  have hW' : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = 256 := by
    rw [hW]; norm_num
  have hidx_dvd : (fixV (Subgroup.zpowers a)).index ∣ 2 ^ 8 := by
    rw [← hW]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx_dvd
  have hk2 : k = 2 := by
    have hp : padicValNat 2 (2 ^ k) = k := padicValNat.prime_pow (p := 2) k
    have hrk' : padicValNat 2 (fixV (Subgroup.zpowers a)).index = 2 := hrk
    rw [← hk, hrk'] at hp
    omega
  have hidx : (fixV (Subgroup.zpowers a)).index = 4 := by
    rw [hk, hk2]
    norm_num
  have hcardfix : Nat.card (fixV (Subgroup.zpowers a)) = 64 := by
    have hmul := (fixV (Subgroup.zpowers a)).card_mul_index
    rw [hidx, hW'] at hmul
    omega
  have hcard : Nat.card (fixV (Subgroup.zpowers a)) =
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // a v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => Quasithin.mem_fixV_zpowers_iff_apply)
  rw [← hcard, hcardfix]

theorem exists_reflection_of_rkIdx_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {a : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (ha : a ∈ natNorm (StatedOmega (StatedQuadPlus 2 K)))
    (hlin : IsSemilinear a (RingEquiv.refl K)) (ha2 : a ^ 2 = 1)
    (hrk : rkIdx (fixV (Subgroup.zpowers a)) = 2) :
    ∃ e : Fin 2 ⊕ Fin 2 → K, StatedQuadPlus 2 K e ≠ 0 ∧
      ∀ v, toAddMap a v = v + (polQ v e / StatedQuadPlus 2 K e) • e := by
  classical
  have h4 : 4 ≤ Nat.card K := by omega
  let S := stdOmegaModel h4
  have hSω : S.omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := stdOmegaModel.omega h4
  have hvecS : ∀ v, S.vec (Multiplicative.ofAdd v) = v := fun v => stdOmegaModel.vec v
  have hsmulS : ∀ (c : K) (v : Fin 2 ⊕ Fin 2 → K),
      S.smul c (Multiplicative.ofAdd v) = Multiplicative.ofAdd (c • v) :=
    fun c v => stdOmegaModel.smul c v
  have hQS : ∀ v, S.Q (Multiplicative.ofAdd v) = StatedQuadPlus 2 K v :=
    fun v => stdOmegaModel.Q v
  have hpolS : ∀ v w, S.pol (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) = polQ v w :=
    fun v w => stdOmegaModel.pol v w
  have haS : a ∈ Subgroup.normalizer (S.omega : Set (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) := by
    rwa [hSω]
  have hfixcard : Nat.card K ^ 2 < Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // a v = v} := by
    rw [card_fixV_of_rkIdx_two hK hrk, hK]
    norm_num
  have hane : a ≠ 1 := by
    intro h
    have htop : fixV (Subgroup.zpowers a) = ⊤ := by
      rw [h]
      ext v
      simp [fixV]
    rw [htop] at hrk
    have h0 : rkIdx (⊤ : Subgroup (StdMod (Fin 2 ⊕ Fin 2) K)) = 0 := by
      simp [rkIdx]
    rw [h0] at hrk
    exact absurd hrk (by norm_num)
  have ha2' : a * a = 1 := by rwa [pow_two] at ha2
  obtain ⟨-, hisoS⟩ := S.linear_isometry_of_card_fixed_gt haS ha2' hfixcard
  have hlinS : ∀ (c : K) (w : StdMod (Fin 2 ⊕ Fin 2) K), a (S.smul c w) = S.smul c (a w) := by
    intro c w
    have hsmulw : S.smul c w = Multiplicative.ofAdd (c • Multiplicative.toAdd w) := rfl
    rw [hsmulw]
    show Multiplicative.ofAdd (toAddMap a (c • Multiplicative.toAdd w)) =
      Multiplicative.ofAdd (c • Multiplicative.toAdd (a w))
    rw [hlin c (Multiplicative.toAdd w)]
    rfl
  obtain ⟨eW, hQe, -, hline⟩ := S.exists_line_of_card_fixed_gt hlinS hisoS hane hfixcard
  have hrefl := S.reflection_formula hlinS hisoS hane hQe hline
  set e : Fin 2 ⊕ Fin 2 → K := S.vec eW with he
  have heW : eW = Multiplicative.ofAdd e := (S.ofVec_vec eW).symm
  rw [heW] at hline hrefl
  have hQe' : S.Q (Multiplicative.ofAdd e) ≠ 0 := by rwa [hQS]
  refine ⟨e, ?_, ?_⟩
  · rw [← hQS e]
    exact hQe'
  · intro v
    obtain ⟨coef, hcoef⟩ := hline (Multiplicative.ofAdd v)
    have hspec := hrefl (Multiplicative.ofAdd v) coef hcoef
    have hcoefeq : coef = polQ v e / S.Q (Multiplicative.ofAdd e) := by
      rw [eq_div_iff hQe', hspec, hpolS]
    have haw : a (Multiplicative.ofAdd v) =
        S.smul coef (Multiplicative.ofAdd e) * Multiplicative.ofAdd v := by
      rw [← hcoef]
      group
    have hvec := congrArg S.vec haw
    rw [S.vec_mul, hsmulS, hvecS, hcoefeq, hQS e] at hvec
    have hgoal : toAddMap a v =
        v + (polQ v e / StatedQuadPlus 2 K e) • e := by
      have hvec' : S.vec (a (Multiplicative.ofAdd v)) =
          (polQ v e / StatedQuadPlus 2 K e) • e + S.vec (Multiplicative.ofAdd v) := hvec
      rw [show S.vec (Multiplicative.ofAdd v) = v from hvecS v] at hvec'
      rw [show S.vec (a (Multiplicative.ofAdd v)) = toAddMap a v from rfl] at hvec'
      rw [add_comm] at hvec'
      exact hvec'
    exact hgoal

theorem quadPlus_add {K : Type} [Field K] [CharP K 2] (v w : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (v + w) =
      StatedQuadPlus 2 K v + StatedQuadPlus 2 K w + polQ v w := by
  simp only [polQ, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two,
    Pi.add_apply]
  ring

theorem eq_one_or_reflection_of_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hg : g ∈ natNorm (StatedOmega (StatedQuadPlus 2 K))) {e : Fin 2 ⊕ Fin 2 → K}
    (he : StatedQuadPlus 2 K e ≠ 0) (hfix : ∀ v, polQ v e = 0 → toAddMap g v = v) :
    g = 1 ∨ ∀ v, toAddMap g v = v + (polQ v e / StatedQuadPlus 2 K e) • e := by
  classical
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  right
  let S := stdOmegaModel h4
  have hSω : S.omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := stdOmegaModel.omega h4
  have hvecS : ∀ v, S.vec (Multiplicative.ofAdd v) = v := fun v => stdOmegaModel.vec v
  have hQS : ∀ v, S.Q (Multiplicative.ofAdd v) = StatedQuadPlus 2 K v :=
    fun v => stdOmegaModel.Q v
  have hpolS : ∀ v w, S.pol (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) = polQ v w :=
    fun v w => stdOmegaModel.pol v w
  have hgS : g ∈ Subgroup.normalizer (S.omega : Set (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) := by
    rwa [hSω]
  have he0 : e ≠ 0 := by
    intro h
    exact he (by rw [h]; simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore])
  have hge : toAddMap g e = e := hfix e (polQ_self e)
  obtain ⟨σ, hσ⟩ := H.exists_semilinear (hasScalarCommutant_statedOmegaPlus h4) hg
  have hσ1 : σ = RingEquiv.refl K := by
    refine RingEquiv.ext fun c => ?_
    have h1 := hσ c e
    rw [hge] at h1
    have h2 : polQ (c • e) e = 0 := by rw [polQ_smul_left, polQ_self, mul_zero]
    have h3 : toAddMap g (c • e) = c • e := hfix (c • e) h2
    rw [h3] at h1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he0
    have hcoef := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at hcoef
    exact (mul_right_cancel₀ hi hcoef).symm
  have hlin_map : ∀ (c : K) (v : Fin 2 ⊕ Fin 2 → K),
      toAddMap g (c • v) = c • toAddMap g v := by
    intro c v
    have := hσ c v
    rwa [hσ1] at this
  have hlinS : ∀ (c : K) (w : StdMod (Fin 2 ⊕ Fin 2) K), g (S.smul c w) = S.smul c (g w) := by
    intro c w
    have hsmulw : S.smul c w = Multiplicative.ofAdd (c • Multiplicative.toAdd w) := rfl
    rw [hsmulw]
    show Multiplicative.ofAdd (toAddMap g (c • Multiplicative.toAdd w)) =
      Multiplicative.ofAdd (c • Multiplicative.toAdd (g w))
    rw [hlin_map c (Multiplicative.toAdd w)]
    rfl
  obtain ⟨c, hc0, hc⟩ := S.exists_similitude_of_linear hgS hlinS
  have hc1 : c = 1 := by
    have h := hc (Multiplicative.ofAdd e)
    change S.Q (Multiplicative.ofAdd (toAddMap g e)) =
      c * S.Q (Multiplicative.ofAdd e) at h
    rw [hge, hQS] at h
    have hQe : StatedQuadPlus 2 K e ≠ 0 := he
    have hzero : (c - 1) * StatedQuadPlus 2 K e = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hQe
  have hisoQ : ∀ v, StatedQuadPlus 2 K (toAddMap g v) = StatedQuadPlus 2 K v := by
    intro v
    have h := hc (Multiplicative.ofAdd v)
    change S.Q (Multiplicative.ofAdd (toAddMap g v)) =
      c * S.Q (Multiplicative.ofAdd v) at h
    rw [hQS, hc1, one_mul] at h
    exact h
  obtain ⟨e', he'⟩ : ∃ e', polQ e' e = 1 := by
    obtain ⟨v, hv⟩ := exists_polQ_ne_zero h4 he0
    exact ⟨(polQ v e)⁻¹ • v, by rw [polQ_smul_left, inv_mul_cancel₀ hv]⟩
  set t : Fin 2 ⊕ Fin 2 → K := toAddMap g e' - e' with ht
  have hgv : ∀ v, toAddMap g v = v + polQ v e • t := by
    intro v
    have hfixH : toAddMap g (v - polQ v e • e') = v - polQ v e • e' := by
      refine hfix _ ?_
      rw [polQ_sub_left, polQ_smul_left, he', mul_one, sub_self]
    have hdecomp : v = (v - polQ v e • e') + polQ v e • e' := by abel
    conv_lhs => rw [hdecomp]
    rw [H.toAddMap_add, hfixH, hlin_map]
    have h1 : toAddMap g e' = t + e' := by rw [ht]; abel
    rw [h1, smul_add]
    abel
  have hQe' : StatedQuadPlus 2 K t + polQ e' t = 0 := by
    have h := hisoQ e'
    rw [show toAddMap g e' = e' + t from by rw [ht]; abel, quadPlus_add] at h
    linear_combination h
  have hstep : ∀ h, polQ h e = 0 → polQ h t = 0 := by
    intro h hh
    have hc1' : polQ (e' + h) e = 1 := by
      rw [polQ_add_left, he', hh, add_zero]
    have hisoe'h := hisoQ (e' + h)
    have hge'h : toAddMap g (e' + h) = (e' + h) + t := by
      rw [hgv (e' + h), hc1', one_smul]
    rw [hge'h, quadPlus_add] at hisoe'h
    have h0 : StatedQuadPlus 2 K t + polQ (e' + h) t = 0 := by linear_combination hisoe'h
    rw [polQ_add_left] at h0
    linear_combination h0 - hQe'
  obtain ⟨ν, hν⟩ : ∃ ν : K, t = ν • e := by
    have hψ : ∀ v, polQ v t = polQ v e * polQ e' t := by
      intro v
      have hh : polQ (v - polQ v e • e') e = 0 := by
        rw [polQ_sub_left, polQ_smul_left, he', mul_one, sub_self]
      have h1 : polQ (v - polQ v e • e') t = 0 := hstep _ hh
      have h2 : v = (v - polQ v e • e') + polQ v e • e' := by abel
      conv_lhs => rw [h2]
      rw [polQ_add_left, h1, zero_add, polQ_smul_left]
    refine ⟨polQ e' t, ?_⟩
    apply sub_eq_zero.mp
    apply eq_zero_of_polQ_eq_zero h4
    intro v
    rw [polQ_comm, polQ_sub_right, polQ_smul_right, hψ v, mul_comm, sub_self]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hν
    have hgt : ∀ v, toAddMap g v = v := by
      intro v
      rw [hgv v, hν, smul_zero, add_zero]
    exact hg1 (H.toAddMap_injective hgt)
  have hνQ : ν * StatedQuadPlus 2 K e = 1 := by
    have h := hQe'
    rw [hν, CFSG.QuasithinUnique.Setup.Family.quadPlus_smul, polQ_smul_right, he', mul_one] at h
    have h' : ν * (ν * StatedQuadPlus 2 K e + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hν0
    · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination h0 - h2
  have hcoef : ∀ v, polQ v e * ν = polQ v e / StatedQuadPlus 2 K e := by
    intro v
    rw [div_eq_mul_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_left hνQ
  intro v
  have hstep2 : polQ v e • t = (polQ v e / StatedQuadPlus 2 K e) • e := by
    rw [hν, smul_smul, hcoef v]
  rw [hgv v, hstep2]

private theorem toMat_jHom {K : Type} [Field K] [Finite K] [CharP K 2]
    {h4 : 4 ≤ Nat.card K} (p : SL(2, K) × SL(2, K)) (v : Fin 2 ⊕ Fin 2 → K) :
    OmegaModel.toMat (toAddMap ((stdOmegaModel h4).jHom p) v) =
      (p.1 : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat v *
        (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have h := (stdOmegaModel h4).vec_jHom p (Multiplicative.ofAdd v)
  rw [stdOmegaModel.vec] at h
  have h2 := congrArg OmegaModel.toMat h
  rwa [OmegaModel.toMat_ofMat] at h2

theorem exists_orderOf_five_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {e : Fin 2 ⊕ Fin 2 → K} (he : StatedQuadPlus 2 K e ≠ 0) :
    ∃ γ ∈ StatedOmega (StatedQuadPlus 2 K), orderOf γ = 5 ∧
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e = e := by
  classical
  have h4 : 4 ≤ Nat.card K := by omega
  let S := stdOmegaModel h4
  have hSω : S.omega = natImage (StatedOmega (StatedQuadPlus 2 K)) := stdOmegaModel.omega h4
  have hQS : ∀ v, S.Q (Multiplicative.ofAdd v) = StatedQuadPlus 2 K v :=
    fun v => stdOmegaModel.Q v
  have hvecS : ∀ v, S.vec (Multiplicative.ofAdd v) = v := fun v => stdOmegaModel.vec v
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hex : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) := by
      intro x
      by_cases hx0 : x = 0
      · exact ⟨0, by simp [hx0]⟩
      · exact ⟨1, by simp [h x hx0]⟩
    have hle : Nat.card K ≤ 2 := by
      have := Nat.card_le_card_of_surjective _ hsurj
      simpa using this
    omega
  obtain ⟨ω, hω0, hω1⟩ := hex
  have hω3 : ω ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    have h := pow_card_eq_one' (x := (Units.mk0 ω hω0))
    rw [hcard] at h
    have h' : ((Units.mk0 ω hω0) : K) ^ 3 = (1 : K) := by
      have := congrArg (fun u : Kˣ => (u : K)) h
      simpa using this
    simpa using h'
  have hquad : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [h, hω3, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hω2 : ω ^ 2 = ω + 1 := by linear_combination hquad - (ω + 1) * h2
  have hωsq : ω * ω = ω + 1 := by rw [← pow_two]; exact hω2
  have hadd : ∀ x : K, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  have hbb : (!![(0 : K), 1; 1, ω] : Matrix (Fin 2) (Fin 2) K) *
      !![(0 : K), 1; 1, ω] = !![(1 : K), ω; ω, ω] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωsq, h2, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have hm2b : (!![(1 : K), ω; ω, ω] : Matrix (Fin 2) (Fin 2) K) *
      !![(0 : K), 1; 1, ω] = !![ω, ω; ω, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωsq, h2, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have ha2b : (!![ω, ω; ω, (1 : K)] : Matrix (Fin 2) (Fin 2) K) *
      !![(0 : K), 1; 1, ω] = !![ω, 1; 1, (0 : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωsq, h2, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have hhab : (!![ω, 1; 1, (0 : K)] : Matrix (Fin 2) (Fin 2) K) *
      !![(0 : K), 1; 1, ω] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have hhba : (!![(0 : K), 1; 1, ω] : Matrix (Fin 2) (Fin 2) K) *
      !![ω, 1; 1, (0 : K)] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have haa : (!![ω, 1; 1, (0 : K)] : Matrix (Fin 2) (Fin 2) K) *
      !![ω, 1; 1, (0 : K)] = !![ω, ω; ω, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωsq, h2, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have ha2a2 : (!![ω, ω; ω, (1 : K)] : Matrix (Fin 2) (Fin 2) K) *
      !![ω, ω; ω, 1] = !![(0 : K), 1; 1, ω] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωsq, h2, hadd]
    all_goals try linear_combination h2
    all_goals try linear_combination ω * h2
  have haT : (!![ω, 1; 1, (0 : K)] : Matrix (Fin 2) (Fin 2) K)ᵀ =
      !![ω, 1; 1, (0 : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have hbdet : (!![(0 : K), 1; 1, ω] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, zero_mul, sub_zero]
    linear_combination -h2
  have hadet : (!![ω, 1; 1, (0 : K)] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, zero_mul, sub_zero]
    linear_combination -h2
  let bMat : Matrix (Fin 2) (Fin 2) K := !![(0 : K), 1; 1, ω]
  let aMat : Matrix (Fin 2) (Fin 2) K := !![ω, 1; 1, (0 : K)]
  let m2Mat : Matrix (Fin 2) (Fin 2) K := !![(1 : K), ω; ω, ω]
  let a2Mat : Matrix (Fin 2) (Fin 2) K := !![ω, ω; ω, (1 : K)]
  have hb2m : bMat ^ 2 = m2Mat := by rw [pow_two, show bMat = _ from rfl]; exact hbb
  have hb3m : bMat ^ 3 = a2Mat := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hb2m]
    exact hm2b
  have hb4m : bMat ^ 4 = aMat := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hb3m]
    exact ha2b
  have hb5m : bMat ^ 5 = 1 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, hb4m]
    exact hhab
  have ha2m : aMat ^ 2 = a2Mat := by rw [pow_two, show aMat = _ from rfl]; exact haa
  have ha4m : aMat ^ 4 = bMat := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, ha2m]
    exact ha2a2
  have ha5m : aMat ^ 5 = 1 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, ha4m]
    exact hhba
  have hbaTm : bMat * aMatᵀ = 1 := by
    rw [show aMatᵀ = aMat from haT]
    exact hhba
  let b : SL(2, K) := ⟨bMat, by rw [show bMat = _ from rfl]; exact hbdet⟩
  let a : SL(2, K) := ⟨aMat, by rw [show aMat = _ from rfl]; exact hadet⟩
  have hb5 : b ^ 5 = 1 := by
    apply Subtype.ext
    show ((b : Matrix (Fin 2) (Fin 2) K) ^ 5) = 1
    rw [show (b : Matrix (Fin 2) (Fin 2) K) = bMat from rfl]
    exact hb5m
  have ha5 : a ^ 5 = 1 := by
    apply Subtype.ext
    show ((a : Matrix (Fin 2) (Fin 2) K) ^ 5) = 1
    rw [show (a : Matrix (Fin 2) (Fin 2) K) = aMat from rfl]
    exact ha5m
  have hbaT : (b : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    simpa [b, a] using hbaTm
  have hbne : b ≠ 1 := by
    intro h
    have hmat : (b : Matrix (Fin 2) (Fin 2) K) = 1 := congrArg Subtype.val h
    rw [show (b : Matrix (Fin 2) (Fin 2) K) = bMat from rfl] at hmat
    have h00 := congrFun (congrFun hmat 0) 0
    simp [bMat] at h00
  have hinj : Function.Injective (fun x : K => x ^ 2) := fun x y h => CharTwo.sq_inj.mp h
  obtain ⟨lam, hlam⟩ := Finite.injective_iff_surjective.mp hinj ((StatedQuadPlus 2 K e)⁻¹)
  have hlamQ : lam ^ 2 * StatedQuadPlus 2 K e = 1 := by
    have hlam' : lam ^ 2 = (StatedQuadPlus 2 K e)⁻¹ := hlam
    rw [hlam']
    field_simp
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num), zero_mul] at hlamQ
    exact zero_ne_one hlamQ
  have hPdet : (OmegaModel.toMat (lam • e)).det = 1 := by
    have h := (stdOmegaModel h4).Q_eq_det (Multiplicative.ofAdd (lam • e))
    rw [stdOmegaModel.vec, hQS, CFSG.QuasithinUnique.Setup.Family.quadPlus_smul, hlamQ] at h
    exact h.symm
  let P : SL(2, K) := ⟨OmegaModel.toMat (lam • e), hPdet⟩
  let t : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := S.jHom (b, a)
  let u : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := S.jHom (P, 1)
  let t' : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := u * t * u⁻¹
  let q : SL(2, K) × SL(2, K) := (P * b * P⁻¹, a)
  have ht' : t' = S.jHom q := by
    change u * t * u⁻¹ = S.jHom q
    have h1 : u * t * u⁻¹ = S.jHom ((P, 1) * (b, a) * (P, 1)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    congr 1
    apply Prod.ext <;> simp [q]
  have hq5 : q ^ 5 = 1 := by
    apply Prod.ext
    · show (P * b * P⁻¹) ^ 5 = 1
      rw [show (P * b * P⁻¹) ^ 5 = P * b ^ 5 * P⁻¹ from by
        rw [show P * b * P⁻¹ = (MulAut.conj P) b from rfl, ← map_pow]
        rfl, hb5, mul_one, mul_inv_cancel]
    · show a ^ 5 = 1
      exact ha5
  have ht'5 : t' ^ 5 = 1 := by
    rw [ht', ← map_pow, hq5, map_one]
  have ht'1 : t' ≠ 1 := by
    rw [ht']
    intro h
    have hq1 : q = 1 := S.jHom_injective (by rw [h, map_one])
    have hb1 : b = 1 := by
      have hq1' : (P * b * P⁻¹, a) = (1, 1) := hq1
      have h1 : P * b * P⁻¹ = 1 := congrArg Prod.fst hq1'
      have := congrArg (fun x => P⁻¹ * x * P) h1
      simpa [mul_assoc] using this
    exact hbne hb1
  have hPdet' : (P : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [show (P : Matrix (Fin 2) (Fin 2) K).det = 1 from hPdet]
    norm_num
  have hPinv : (P * b * P⁻¹) * P = P * b := by group
  have hfixP : toAddMap t' (lam • e) = lam • e := by
    have hmat : OmegaModel.toMat (toAddMap t' (lam • e)) = OmegaModel.toMat (lam • e) := by
      have h := toMat_jHom (h4 := h4) q (lam • e)
      rw [← ht'] at h
      rw [h]
      show ((P * b * P⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          OmegaModel.toMat (lam • e) * (a : Matrix (Fin 2) (Fin 2) K)ᵀ =
        OmegaModel.toMat (lam • e)
      rw [show OmegaModel.toMat (lam • e) = (P : Matrix (Fin 2) (Fin 2) K) from rfl]
      calc ((P * b * P⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
            (P : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K)ᵀ
          = (((P * b * P⁻¹) * P : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
              (a : Matrix (Fin 2) (Fin 2) K)ᵀ := by
            rw [← Matrix.SpecialLinearGroup.coe_mul]
        _ = ((P * b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
              (a : Matrix (Fin 2) (Fin 2) K)ᵀ := by rw [hPinv]
        _ = (P : Matrix (Fin 2) (Fin 2) K) * (b : Matrix (Fin 2) (Fin 2) K) *
              (a : Matrix (Fin 2) (Fin 2) K)ᵀ := by
            rw [Matrix.SpecialLinearGroup.coe_mul]
        _ = (P : Matrix (Fin 2) (Fin 2) K) * ((b : Matrix (Fin 2) (Fin 2) K) *
              (a : Matrix (Fin 2) (Fin 2) K)ᵀ) := by rw [Matrix.mul_assoc]
        _ = (P : Matrix (Fin 2) (Fin 2) K) * 1 := by rw [hbaT]
        _ = (P : Matrix (Fin 2) (Fin 2) K) := mul_one _
    have hinj : Function.Injective (OmegaModel.toMat (K := K)) := fun x y h => by
      have := congrArg OmegaModel.ofMat h
      rwa [OmegaModel.ofMat_toMat, OmegaModel.ofMat_toMat] at this
    exact hinj hmat
  have ht'ω0 : t' ∈ S.omega0 := by
    rw [ht']
    exact ⟨q, rfl⟩
  have ht'ω : t' ∈ S.omega := S.omega0_le_omega ht'ω0
  rw [hSω, natImage, MonoidHom.mem_range] at ht'ω
  obtain ⟨γ, hγ⟩ := ht'ω
  have hγ' : S.actHom (γ : GL (Fin 2 ⊕ Fin 2) K) = t' := by
    rw [stdOmegaModel.actHom]
    exact hγ
  refine ⟨(γ : GL (Fin 2 ⊕ Fin 2) K), γ.2, ?_, ?_⟩
  · have h5 : (γ : GL (Fin 2 ⊕ Fin 2) K) ^ 5 = 1 := by
      apply S.actHom_injective
      rw [map_pow, hγ', ht'5, map_one]
    have h1 : (γ : GL (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
      intro h
      exact ht'1 (by rw [← hγ', h, map_one])
    exact orderOf_eq_prime (p := 5) (hp := ⟨by norm_num⟩) h5 h1
  · have hfixγ : ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (lam • e) = lam • e := by
      have h1 : toAddMap (S.actHom (γ : GL (Fin 2 ⊕ Fin 2) K)) (lam • e) = lam • e := by
        rw [hγ']
        exact hfixP
      rwa [stdOmegaModel.actHom, H.toAddMap_matAut] at h1
    rw [Matrix.mulVec_smul] at hfixγ
    have hcongr := congrArg (fun w => (lam⁻¹) • w) hfixγ
    simpa [smul_smul, hlam0] using hcongr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
