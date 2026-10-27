module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

theorem eq_zero_of_mulVec_eq_of_planeStab (hKG : SL3ParabolicAutFact) {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (Y : Subgroup ↥(StatedSL 3 F)) (hY : Y ≠ ⊥) (hYperf : ⁅Y, Y⁆ = Y)
    (hstab : ∀ y ∈ Y, ∀ w ∈ W,
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) →
        g ∈ Subgroup.normalizer (Y : Set ↥(StatedSL 3 F)))
    (v : Fin 3 → F)
    (hv : ∀ y ∈ Y,
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v) :
    v = 0 := by
  classical
  set e := specialLinearGroupEquivStatedSL 3 F with he
  let mat : ↥(StatedSL 3 F) → Matrix (Fin 3) (Fin 3) F := fun g => ((g : GL (Fin 3) F) : _)
  have hmat_mul : ∀ g h : ↥(StatedSL 3 F), mat (g * h) = mat g * mat h := fun g h => rfl
  have hmat_e : ∀ γ : SpecialLinearGroup (Fin 3) F, mat (e γ) = γ :=
    fun γ => specialLinearGroupEquivStatedSL_coe 3 F γ
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow] at h
    exact pow_eq_zero_iff (by omega) |>.mp h
  have hWtop : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h3 := congrArg (fun S : Submodule F (Fin 3 → F) => Module.finrank F S) h
    simp only [finrank_top, Module.finrank_fin_fun, hW] at h3
    omega
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W hWtop
  have hrange : LinearMap.range f = ⊤ := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, f u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    refine LinearMap.range_eq_top.mpr fun a => ⟨(a / f u₀) • u₀, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ a hu₀]
  have hker : LinearMap.ker f = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hWf
    have h3 := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h3
    rw [hW]
    omega
  have hmemW : ∀ u, u ∈ W ↔ f u = 0 := fun u => by rw [← hker, LinearMap.mem_ker]
  set fv : Fin 3 → F := fun i => f (fun j => if i = j then 1 else 0) with hfvdef
  have hfv : ∀ u, fv ⬝ᵥ u = f u := by
    intro u
    conv_rhs => rw [pi_eq_sum_univ u]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hfvdef]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hfv0 : fv ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun u => ?_
    rw [← hfv, h, zero_dotProduct, LinearMap.zero_apply]
  have hfinv : ∀ y ∈ Y, ∀ u, f ((mat y).mulVec u) = f u := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, f u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    have hchi : ∀ g : ↥(StatedSL 3 F), (∀ w ∈ W, (mat g).mulVec w ∈ W) →
        ∀ u, f ((mat g).mulVec u) = (f ((mat g).mulVec u₀) / f u₀) * f u := by
      intro g hg u
      have hd : u - (f u / f u₀) • u₀ ∈ W := by
        rw [hmemW, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₀, sub_self]
      have h3 := (hmemW _).mp (hg _ hd)
      rw [mulVec_sub, mulVec_smul, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
      rw [h3]
      field_simp
    let S : Subgroup ↥(StatedSL 3 F) :=
      { carrier := {g | ∀ u, f ((mat g).mulVec u) = f u}
        one_mem' := fun u => by simp [mat]
        mul_mem' := fun {a b} ha hb u => by
          show f ((mat a * mat b).mulVec u) = f u
          rw [← mulVec_mulVec, ha, hb]
        inv_mem' := fun {a} ha u => by
          have h3 := ha ((mat a⁻¹).mulVec u)
          rw [mulVec_mulVec, ← hmat_mul, mul_inv_cancel] at h3
          simpa [mat] using h3.symm }
    have hYS : Y ≤ S := by
      rw [← hYperf, Subgroup.commutator_le]
      intro a ha b hb u
      have hYW : ∀ y ∈ Y, ∀ w ∈ W, (mat y).mulVec w ∈ W := hstab
      set χ : ↥(StatedSL 3 F) → F := fun g => f ((mat g).mulVec u₀) / f u₀ with hχ
      have hc : ∀ y ∈ Y, ∀ u, f ((mat y).mulVec u) = χ y * f u :=
        fun y hy => hchi y (hYW y hy)
      have hinv : ∀ y ∈ Y, χ y * χ y⁻¹ = 1 := by
        intro y hy
        have h3 := hc y hy ((mat y⁻¹).mulVec u₀)
        rw [mulVec_mulVec, ← hmat_mul, mul_inv_cancel, hc y⁻¹ (Y.inv_mem hy)] at h3
        have h4 : f ((mat 1).mulVec u₀) = f u₀ := by simp [mat]
        rw [h4] at h3
        have h5 : f u₀ * 1 = f u₀ * (χ y * χ y⁻¹) :=
          calc f u₀ * 1 = f u₀ := mul_one _
            _ = χ y * (χ y⁻¹ * f u₀) := h3
            _ = f u₀ * (χ y * χ y⁻¹) := by ring
        exact (mul_left_cancel₀ hu₀ h5).symm
      show f ((mat (a * b * a⁻¹ * b⁻¹)).mulVec u) = f u
      rw [hmat_mul, hmat_mul, hmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
        hc a ha, hc b hb, hc a⁻¹ (Y.inv_mem ha), hc b⁻¹ (Y.inv_mem hb)]
      have h3 := hinv a ha
      have h4 := hinv b hb
      calc χ a * (χ b * (χ a⁻¹ * (χ b⁻¹ * f u))) = (χ a * χ a⁻¹) * (χ b * χ b⁻¹) * f u := by
            ring
        _ = f u := by rw [h3, h4, one_mul, one_mul]
    exact fun y hy => hYS hy
  have hfvinv : ∀ y ∈ Y, fv ᵥ* mat y = fv := by
    intro y hy
    funext i
    have h3 := hfinv y hy (fun j => if i = j then 1 else 0)
    rw [← hfv, ← hfv, dotProduct_mulVec] at h3
    have h5 : ∀ w : Fin 3 → F, w ⬝ᵥ (fun j => if i = j then (1 : F) else 0) = w i := by
      intro w
      simp [dotProduct]
    rw [h5, h5] at h3
    exact h3
  have houter : ∀ (w u : Fin 3 → F) (a : F),
      (1 + vecMulVec w (a • fv)).mulVec u = u + (a * f u) • w := by
    intro w u a
    rw [add_mulVec, one_mulVec, vecMulVec_mulVec, smul_dotProduct, hfv, smul_eq_mul,
      op_smul_eq_smul]
  have hdet : ∀ (w : Fin 3 → F) (a : F), w ∈ W → (1 + vecMulVec w (a • fv)).det = 1 := by
    intro w a hw
    have h3 : vecMulVec w (a • fv) =
        replicateCol Unit w * replicateRow Unit (a • fv) := by
      ext i j
      simp [vecMulVec_apply, mul_apply]
    rw [h3, det_one_add_replicateCol_mul_replicateRow (ι := Unit), smul_dotProduct, hfv,
      (hmemW w).mp hw, smul_zero, add_zero]
  have hB : ∀ u ∈ W, (∀ y ∈ Y, (mat y).mulVec u = u) → u = 0 := by
    intro u huW hu
    by_contra hu0
    set τ : SpecialLinearGroup (Fin 3) F := ⟨1 + vecMulVec u ((1 : F) • fv), hdet u 1 huW⟩
      with hτ
    set t := e τ with ht
    have hτmat : mat t = 1 + vecMulVec u ((1 : F) • fv) := hmat_e τ
    have hτY : ∀ y ∈ Y, t * y * t⁻¹ = y := by
      intro y hy
      have hcomm : mat t * mat y = mat y * mat t := by
        rw [hτmat, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul, mul_vecMulVec, hu y hy,
          one_smul, hfvinv y hy]
      have h3 : t * y = y * t := by
        apply Subtype.ext
        apply Units.ext
        exact hcomm
      rw [h3, mul_inv_cancel_right]
    have hτ2 : t * t = 1 := by
      apply Subtype.ext
      apply Units.ext
      show mat t * mat t = 1
      have hNN : vecMulVec u ((1 : F) • fv) * vecMulVec u ((1 : F) • fv) = 0 := by
        rw [vecMulVec_mul_vecMulVec, one_smul, hfv, (hmemW u).mp huW, zero_smul]
        ext i j
        simp [vecMulVec_apply]
      have h2N : vecMulVec u ((1 : F) • fv) + vecMulVec u ((1 : F) • fv) = 0 := by
        rw [← two_smul F, h2, zero_smul]
      rw [hτmat]
      calc (1 + vecMulVec u ((1 : F) • fv)) * (1 + vecMulVec u ((1 : F) • fv)) =
            1 + (vecMulVec u ((1 : F) • fv) + vecMulVec u ((1 : F) • fv)) +
              vecMulVec u ((1 : F) • fv) * vecMulVec u ((1 : F) • fv) := by noncomm_ring
        _ = 1 := by rw [h2N, hNN, add_zero, add_zero]
    set σ : MulAut ↥(StatedSL 3 F) := MulAut.conj t with hσ
    have hσσ : σ * σ = 1 := by
      rw [hσ, ← map_mul, hτ2, map_one]
    have hσY : ∀ y ∈ Y, σ y = y := fun y hy => by
      rw [hσ, MulAut.conj_apply]
      exact hτY y hy
    have hσ1 := hKG F n hn hF W hW Y hY hYperf hstab hnorm σ hσσ hσY
    have hscalar : mat t ∈ Set.range (Matrix.scalar (Fin 3)) := by
      refine mem_range_scalar_of_commute_transvectionStruct fun ts => ?_
      have h3 : σ (e ts.toSpecialLinearGroup) = e ts.toSpecialLinearGroup := by
        rw [hσ1, MulAut.one_apply]
      rw [hσ, MulAut.conj_apply] at h3
      have h4 : t * e ts.toSpecialLinearGroup = e ts.toSpecialLinearGroup * t :=
        calc t * e ts.toSpecialLinearGroup =
              (t * e ts.toSpecialLinearGroup * t⁻¹) * t := by group
          _ = e ts.toSpecialLinearGroup * t := by rw [h3]
      have h5 := congrArg mat h4
      rw [hmat_mul, hmat_mul, hmat_e] at h5
      exact h5.symm
    obtain ⟨r, hr⟩ := hscalar
    have hN : vecMulVec u fv = (r - 1) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      have h3 : (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec u fv = r • 1 := by
        rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, hr, hτmat, one_smul]
      rw [sub_smul, one_smul, ← h3, add_sub_cancel_left]
    have hNsq : vecMulVec u fv * vecMulVec u fv = 0 := by
      rw [vecMulVec_mul_vecMulVec, hfv, (hmemW u).mp huW, zero_smul]
      ext i j
      simp [vecMulVec_apply]
    rw [hN, smul_mul_smul_comm, mul_one] at hNsq
    have hr1 : (r - 1) * (r - 1) = 0 := by
      have h3 := congrFun (congrFun hNsq 0) 0
      simpa using h3
    have hr1' : r - 1 = 0 := mul_self_eq_zero.mp hr1
    rw [hr1', zero_smul, vecMulVec_eq_zero] at hN
    rcases hN with h | h
    · exact hu0 h
    · exact hfv0 h
  by_cases hvW : v ∈ W
  · exact hB v hvW hv
  · exfalso
    have hfv1 : f v ≠ 0 := fun h => hvW ((hmemW v).mpr h)
    obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
      by_contra h
      push Not at h
      have hbot : W = ⊥ := (Submodule.eq_bot_iff W).mpr h
      rw [hbot, finrank_bot] at hW
      omega
    set ρ : SpecialLinearGroup (Fin 3) F := ⟨1 + vecMulVec w ((f v)⁻¹ • fv), hdet w _ hwW⟩
      with hρ
    set g := e ρ with hg
    have hgmat : mat g = 1 + vecMulVec w ((f v)⁻¹ • fv) := hmat_e ρ
    have hgW : ∀ u ∈ W, (mat g).mulVec u ∈ W := by
      intro u hu
      rw [hgmat, houter, (hmemW u).mp hu, mul_zero, zero_smul, add_zero]
      exact hu
    have hgN := hnorm g hgW
    have hgv : (mat g).mulVec v = v + w := by
      rw [hgmat, houter, inv_mul_cancel₀ hfv1, one_smul]
    have hfixgv : ∀ y ∈ Y, (mat y).mulVec (v + w) = v + w := by
      intro y hy
      have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) y).mp hy
      rw [inv_inv] at hy'
      have h3 := hv _ hy'
      have h4 : mat y * mat g = mat g * mat (g⁻¹ * y * g) := by
        rw [← hmat_mul, ← hmat_mul]
        congr 1
        group
      rw [← hgv, mulVec_mulVec, h4, ← mulVec_mulVec, h3]
    have hfixw : ∀ y ∈ Y, (mat y).mulVec w = w := by
      intro y hy
      have h3 := hfixgv y hy
      rw [mulVec_add, hv y hy] at h3
      exact add_left_cancel h3
    exact hw0 (hB w hwW hfixw)

end CFSG.Quasithin.H13.Ch4
