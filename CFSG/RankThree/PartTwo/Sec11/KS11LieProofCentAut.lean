module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSL2

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section Linear

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts

theorem mul_self_pow_eq {M : Type*} [Monoid M] {x : M} {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    (x * x) ^ ((3 ^ k + 1) / 2) = x := by
  have h2m : 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 := by
    obtain ⟨r, hr⟩ : Odd (3 ^ k) := Odd.pow ⟨1, rfl⟩
    omega
  rw [← sq, ← pow_mul, h2m, pow_succ, hx, one_mul]

theorem aut_semilinear_linear (hK : PiField true p f K)
    (β : MulAut (projImage (slPi true 3 (p ^ f) K))) {k : ℕ} (hβ : β ^ 3 ^ k = 1) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * frobGL σ s * A⁻¹) := by
  have := hK.finite
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set α' := MulAut.congr ψ β with hα'
  have hα'k : α' ^ 3 ^ k = 1 := by
    rw [hα', ← map_pow, hβ, map_one]
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hcoe : ∀ s : SpecialLinearGroup (Fin 3) K,
      β (slToPsl (p ^ f) K s) = ψ.symm (α' (proj 3 K s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj,
      MulEquiv.symm_apply_apply]
  have hslPi : ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = slToPsl (p ^ f) K (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩) := by
    intro s hs
    change projOf _ ⟨s, hs⟩ = projOf _ ((slPiTrueEquiv (p ^ f) K).symm
      (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩))
    rw [MulEquiv.symm_apply_apply]
  have hstd : α' ∈ standardAutGroup 3 K := by
    rw [(automorphism_generation (K := K) (n := 3) le_rfl).1]
    exact Subgroup.mem_top _
  have hE : α' ∈ semilinearAutGroup 3 K := by
    rcases mem_or_mul_dualAut_mem hstd with h | h
    · exact h
    · have hδδ : dualAut 3 K * dualAut 3 K = 1 :=
        (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
      have h2 : α' * α' ∈ semilinearAutGroup 3 K := by
        have e : α' * α' = (α' * dualAut 3 K) *
            (dualAut 3 K * (α' * dualAut 3 K) * dualAut 3 K) := by
          calc α' * α' = α' * 1 * α' * 1 := by group
            _ = α' * (dualAut 3 K * dualAut 3 K) * α' * (dualAut 3 K * dualAut 3 K) := by
                rw [hδδ]
            _ = _ := by group
        rw [e]
        exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
      rw [← mul_self_pow_eq hα'k]
      exact pow_mem h2 _
  obtain ⟨A, σ, hA⟩ := mem_semilinearAutGroup_iff.mp hE
  refine ⟨A, σ, fun s hs => ?_⟩
  rw [hslPi s hs, hcoe, hA, MulAut.mul_apply, fieldAut_proj, conjAut_proj, hproj, coe_slToPsl,
    toGL_slConjugation, toGL_map_eq_frobGL, toGL_slPiTrueEquiv]

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem aut_semilinear_unitary (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    (β : MulAut (projImage (slPi false 3 (p ^ f) K))) :
    ∃ A ∈ glPi false 3 (p ^ f) K, ∃ σ : K ≃+* K, ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * frobGL σ s * A⁻¹) := by
  have h := hK.unitary
  have := hK.finite
  set ψ := psuEquivUnitary h with hψ
  set α' := MulAut.congr ψ β with hα'
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hcoe : ∀ s : unitarySU p f K 3,
      β (suToPsu p f K s) = ψ.symm (α' (unitaryProj h 3 s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← psuEquivUnitary_suToPsu h, MulEquiv.symm_apply_apply]
  have hslPi : ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = suToPsu p f K ⟨s, hs⟩ := fun s hs => rfl
  obtain ⟨A, σ, hA⟩ := exists_psuConj_mul_psuField hq2 α'
  refine ⟨A, (mem_glPi_false h).mpr A.2, σ, fun s hs => ?_⟩
  rw [hslPi s hs, hcoe, hA, MulAut.mul_apply, psuField_unitaryProj, psuConj_unitaryProj, hproj,
    coe_suToPsu, coe_suConj, coe_suField, glAut_eq_frobGL]
  simp only [Subgroup.coe_inv]

end Unitary

theorem aut_semilinear (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) {k : ℕ} (hβ : β ^ 3 ^ k = 1) :
    ∃ A ∈ glPi π 3 (p ^ f) K, ∃ σ : K ≃+* K, ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * frobGL σ s * A⁻¹) := by
  cases π
  · exact aut_semilinear_unitary hK hq2 β
  · obtain ⟨A, σ, hA⟩ := aut_semilinear_linear hK β hβ
    exact ⟨A, mem_glPi_true _ _, σ, hA⟩


theorem eq_of_mk_eq_block (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {h₀ : GL (Fin 3) K} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) K) (Φ : GL (Fin 3) K →* GL (Fin 3) K)
    (hΦ : ∀ B : slPi π 2 (p ^ f) K,
      ProjGenLinGroup.mk (Φ (blockConj hK hh₀ B : slPi π 3 (p ^ f) K)) =
        ProjGenLinGroup.mk ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K))
    (B : slPi π 2 (p ^ f) K) :
    Φ (blockConj hK hh₀ B : slPi π 3 (p ^ f) K) =
      ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) := by
  set g : slPi π 2 (p ^ f) K →* GL (Fin 3) K :=
    (slPi π 3 (p ^ f) K).subtype.comp (blockConj hK hh₀) with hg
  have hQ := isQuasisimple_slPi_two hK hq hq2
  have hw : ∀ B, (g B)⁻¹ * Φ (g B) ∈ StatedScalars (Fin 3) K := fun B => by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv]
    change (ProjGenLinGroup.mk ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K))⁻¹ *
      ProjGenLinGroup.mk (Φ (blockConj hK hh₀ B : slPi π 3 (p ^ f) K)) = 1
    rw [hΦ B, inv_mul_cancel]
  exact eq_of_eq_mul_commute hQ.1 (Φ.comp g) g (fun B => (g B)⁻¹ * Φ (g B))
    (fun B => (mul_inv_cancel_left _ _).symm)
    (fun x y => (commute_of_mem_statedScalars (hw x) (g y)).symm)
    (fun x y => (commute_of_mem_statedScalars (hw x) ((g y)⁻¹ * Φ (g y))).symm) B

theorem trace_conj_gl (A M : GL (Fin 3) K) :
    ((A * M * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (M : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

theorem trace_frobGL (σ : K ≃+* K) (M : GL (Fin 3) K) :
    ((frobGL σ M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      σ (M : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [coe_frobGL, Matrix.trace_fin_three, Matrix.trace_fin_three]
  simp [Matrix.map_apply, map_add]

theorem trace_blockConj (hK : PiField π p f K) {h₀ : GL (Fin 3) K}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) K) (B : slPi π 2 (p ^ f) K) :
    (((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).trace =
        1 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [coe_blockConj, trace_conj_gl, coe_blockHom_of_det (det_eq_one_of_mem_slPi hK B.2),
    trace_blockMat]

theorem eq_one_of_trace (hK : PiField true p f K) {h₀ : GL (Fin 3) K}
    (hh₀ : h₀ ∈ glPi true 3 (p ^ f) K) {A : GL (Fin 3) K} {σ : K ≃+* K}
    (h : ∀ B : slPi true 2 (p ^ f) K,
      A * frobGL σ (blockConj hK hh₀ B : slPi true 3 (p ^ f) K) * A⁻¹ =
        ((blockConj hK hh₀ B : slPi true 3 (p ^ f) K) : GL (Fin 3) K)) : σ = 1 := by
  apply RingEquiv.ext
  intro x
  have h1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).trace)
    (h ⟨tTwo x, tTwo_mem_slPi_true x⟩)
  simp only [trace_conj_gl, trace_frobGL, trace_blockConj] at h1
  rw [coe_tTwo, Matrix.trace_fin_two_of] at h1
  simpa using h1

theorem exists_orderOf_eq_qSubPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ μ : Kˣ, orderOf μ = qSubPi π (p ^ f) := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (qSubPi π (p ^ f)) K)
  refine ⟨ζ, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hζ,
    card_rootsOfUnity_qSubPi hK hq]

theorem eq_of_dvd_pow_sub_add {p f i : ℕ} (hp : 2 ≤ p) (hf : 1 ≤ f) (hi : i < 2 * f) :
    (p ^ f + 1 ∣ p ^ i - 1 → i = 0) ∧ (p ^ f + 1 ∣ p ^ i + 1 → i = f) := by
  have hp1 : 1 < p := by omega
  have hpos : ∀ n : ℕ, 1 ≤ p ^ n := fun n => Nat.one_le_pow _ _ (by omega)
  have hlt : ∀ {a b : ℕ}, a < b → p ^ a < p ^ b := fun h => Nat.pow_lt_pow_right hp1 h
  have hpow1 : ∀ {n : ℕ}, p ^ n = 1 → n = 0 := fun h => by
    rcases Nat.pow_eq_one.mp h with h' | h'
    · omega
    · exact h'
  rcases lt_trichotomy i f with hif | rfl | hif
  · have h1 := hlt hif
    refine ⟨fun hd => hpow1 ?_, fun hd => ?_⟩
    · have := Nat.eq_zero_of_dvd_of_lt hd (by have := hpos i; omega)
      have := hpos i
      omega
    · have := Nat.le_of_dvd (by omega) hd
      omega
  · refine ⟨fun hd => ?_, fun _ => rfl⟩
    have h2 : 2 ≤ p ^ i := le_trans hp (Nat.le_self_pow (by omega) p)
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = f + j := ⟨i - f, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hjf : j < f := by omega
    have hpj := hlt hjf
    have hpj1 : 2 ≤ p ^ j := le_trans hp (Nat.le_self_pow (by omega) p)
    have hsplit : p ^ (f + j) = p ^ j * p ^ f := by rw [pow_add, mul_comm]
    have hmul : p ^ f + 1 ∣ p ^ j * (p ^ f + 1) := dvd_mul_left _ _
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · exfalso
      have h3 : p ^ j * (p ^ f + 1) - (p ^ (f + j) - 1) = p ^ j + 1 := by
        rw [hsplit, mul_add, mul_one]
        have := hpos f
        have : p ^ j ≤ p ^ j * p ^ f := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h4 := Nat.dvd_sub hmul hd
      rw [h3] at h4
      have := Nat.le_of_dvd (by omega) h4
      omega
    · exfalso
      have h3 : p ^ j * (p ^ f + 1) - (p ^ (f + j) + 1) = p ^ j - 1 := by
        rw [hsplit, mul_add, mul_one]
        omega
      have h4 := Nat.dvd_sub hmul hd
      rw [h3] at h4
      have := Nat.eq_zero_of_dvd_of_lt h4 (by omega)
      omega

theorem mul_self_eq_one_of_apply (hK : PiField false p f K) {μ : Kˣ}
    (hμ : orderOf μ = p ^ f + 1) {σ : K ≃+* K}
    (hσ : σ (μ : K) = μ ∨ σ (μ : K) = ((μ⁻¹ : Kˣ) : K)) : σ * σ = 1 := by
  have h := hK.unitary
  have hf1 := h.one_le
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (n := 2 * f) (by omega) h.card
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨i, hi, rfl⟩ : ∃ i < 2 * f, φ ^ i = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i % (2 * f), Nat.mod_lt _ (by omega), ?_⟩
    rw [← hi, ← hord, pow_mod_orderOf]
  have hpow : ∀ (n : ℕ) (a : K), (φ ^ n) a = a ^ p ^ n := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih => intro a; rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]
  have hp2 : 2 ≤ p := h.prime.two_le
  have hpi : 1 ≤ p ^ i := Nat.one_le_pow _ _ (by omega)
  obtain ⟨hsub, hadd⟩ := eq_of_dvd_pow_sub_add hp2 hf1 hi
  have hi0 : i = 0 ∨ i = f := by
    rcases hσ with h1 | h1
    · left
      apply hsub
      rw [← hμ, orderOf_dvd_iff_pow_eq_one]
      have h2 : μ ^ p ^ i = μ := Units.ext (by rw [Units.val_pow_eq_pow_val, ← hpow, h1])
      have h3 : μ ^ (p ^ i - 1) * μ = μ := by
        rw [← pow_succ, Nat.sub_add_cancel hpi, h2]
      exact mul_eq_right.mp h3
    · right
      apply hadd
      rw [← hμ, orderOf_dvd_iff_pow_eq_one]
      have h2 : μ ^ p ^ i = μ⁻¹ := Units.ext (by rw [Units.val_pow_eq_pow_val, ← hpow, h1])
      rw [pow_succ, h2, inv_mul_cancel]
  rw [← pow_add]
  rcases hi0 with rfl | rfl
  · simp
  · rw [← two_mul, ← hord, pow_orderOf_eq_one]

theorem mul_self_eq_one_of_trace (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {h₀ : GL (Fin 3) K} (hh₀ : h₀ ∈ glPi false 3 (p ^ f) K) {A : GL (Fin 3) K} {σ : K ≃+* K}
    (h : ∀ B : slPi false 2 (p ^ f) K,
      A * frobGL σ (blockConj hK hh₀ B : slPi false 3 (p ^ f) K) * A⁻¹ =
        ((blockConj hK hh₀ B : slPi false 3 (p ^ f) K) : GL (Fin 3) K)) : σ * σ = 1 := by
  obtain ⟨μ, hμ⟩ := exists_orderOf_eq_qSubPi hK hq
  have hμ' : orderOf μ = p ^ f + 1 := hμ
  have hμq : (μ : K) ^ (p ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hμ', pow_orderOf_eq_one, Units.val_one]
  have h1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).trace)
    (h ⟨diagTwo μ, diagTwo_mem_slPi hK (fun _ => hμq)⟩)
  simp only [trace_conj_gl, trace_frobGL, trace_blockConj] at h1
  rw [coe_diagTwo, Matrix.trace_diagonal, Fin.sum_univ_two] at h1
  simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one, map_add, map_one,
    add_right_inj] at h1
  set x := σ (μ : K) with hx
  set y := (μ : K) with hy
  have hy0 : y ≠ 0 := Units.ne_zero μ
  have hx0 : x ≠ 0 := by rw [hx]; exact (map_ne_zero σ).mpr hy0
  have hinv : σ ((μ⁻¹ : Kˣ) : K) = x⁻¹ := by rw [Units.val_inv_eq_inv_val, map_inv₀]
  rw [hinv, Units.val_inv_eq_inv_val] at h1
  have hkey : (x - y) * (x - y⁻¹) = 0 := by
    have hx' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    have hy' : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    have e : (x - y) * (x - y⁻¹) = x * ((x + x⁻¹) - (y + y⁻¹)) := by
      linear_combination hy' - hx'
    rw [e, h1, sub_self, mul_zero]
  refine mul_self_eq_one_of_apply hK hμ' ?_
  rcases mul_eq_zero.mp hkey with h2 | h2
  · exact Or.inl (sub_eq_zero.mp h2)
  · exact Or.inr (by rw [Units.val_inv_eq_inv_val]; exact sub_eq_zero.mp h2)


theorem frobGL_frobGL_of_mul_self {σ : K ≃+* K} (hσ : σ * σ = 1) (M : GL (Fin 3) K) :
    frobGL σ (frobGL σ M) = M := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL]
  ext i j
  simp only [Matrix.map_apply]
  have := congrArg (fun τ : K ≃+* K => τ ((M : Matrix (Fin 3) (Fin 3) K) i j)) hσ
  simpa only [RingAut.mul_apply, RingAut.one_apply] using this

theorem exists_inner_of_sq (hK : PiField π p f K)
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    {A : GL (Fin 3) K} (hA : A ∈ glPi π 3 (p ^ f) K) {σ : K ≃+* K} (hσ : σ * σ = 1)
    (hβA : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * frobGL σ s * A⁻¹)) :
    ∃ A' ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
      (β m : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk A' * m * (ProjGenLinGroup.mk A')⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h' => by subst h'; exact hK.unitary
  set A₂ := A * frobGL σ A with hA₂
  have hmem : ∀ s ∈ slPi π 3 (p ^ f) K, A * frobGL σ s * A⁻¹ ∈ slPi π 3 (p ^ f) K :=
    fun s hs => conj_mem_slPi hπ hA (frobGL_mem_slPi hK σ hs)
  have hβ' : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      β (projOf _ ⟨s, hs⟩) = projOf _ ⟨A * frobGL σ s * A⁻¹, hmem s hs⟩ := fun s hs =>
    Subtype.ext (by rw [hβA]; rfl)
  have hβ2 : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (((β * β) m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk A₂ * m * (ProjGenLinGroup.mk A₂)⁻¹ := by
    intro m
    obtain ⟨⟨s, hs⟩, rfl⟩ := projOf_surjective _ m
    rw [MulAut.mul_apply, hβ' s hs, hβA]
    have e : A * frobGL σ (A * frobGL σ s * A⁻¹) * A⁻¹ = A₂ * s * A₂⁻¹ := by
      rw [map_mul, map_mul, map_inv, frobGL_frobGL_of_mul_self hσ, hA₂]
      group
    rw [e, map_mul, map_mul, map_inv]
    rfl
  refine ⟨A₂ ^ ((3 ^ k + 1) / 2), pow_mem (mul_mem hA (frobGL_mem_glPi hK σ hA)) _,
    fun m => ?_⟩
  have h1 := mulAut_pow_coe hβ2 ((3 ^ k + 1) / 2) m
  rw [mul_self_pow_eq hβ] at h1
  rw [h1, map_pow]

theorem exists_diag_of_commute_block (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {M : GL (Fin 3) K}
    (hM : ∀ B : slPi π 2 (p ^ f) K,
      M * blockHom (B : GL (Fin 2) K) = blockHom (B : GL (Fin 2) K) * M) :
    ∃ a b : Kˣ, M = diagUnits a b b := by
  obtain ⟨μ, hμ⟩ := exists_orderOf_eq_qSubPi hK hq
  have h3 : 3 ≤ qSubPi π (p ^ f) := by
    cases π
    · change 3 ≤ p ^ f + 1
      omega
    · change 3 ≤ p ^ f - 1
      change p ^ f % 3 = 1 at hq
      omega
  have hμ1 : (μ : K) ≠ 1 := by
    intro h1
    have : μ = 1 := Units.ext (by rw [h1, Units.val_one])
    rw [this, orderOf_one] at hμ
    omega
  have hμ2 : (μ : K) ≠ ((μ⁻¹ : Kˣ) : K) := by
    intro h1
    have h2 : μ = μ⁻¹ := Units.ext h1
    have h3' : μ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h2]; exact mul_inv_cancel μ
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3')
    omega
  have hμ1' : ((μ⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h1
    apply hμ1
    have : μ⁻¹ = 1 := Units.ext (by rw [h1, Units.val_one])
    rw [inv_eq_one.mp this, Units.val_one]
  have hμq : π = false → (μ : K) ^ (p ^ f + 1) = 1 := by
    intro hπ
    subst hπ
    rw [← Units.val_pow_eq_pow_val, show p ^ f + 1 = qSubPi false (p ^ f) from rfl, ← hμ,
      pow_orderOf_eq_one, Units.val_one]
  set Mm := (M : Matrix (Fin 3) (Fin 3) K) with hMm
  have hD := hM ⟨diagTwo μ, diagTwo_mem_slPi hK hμq⟩
  have hD' := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hD
  have hdet1 : GeneralLinearGroup.det (diagTwo μ : GL (Fin 2) K) = 1 :=
    det_eq_one_of_mem_slPi hK (diagTwo_mem_slPi hK hμq)
  have hblock : blockMat (1 : K) ((diagTwo μ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![1, (μ : K), ((μ⁻¹ : Kˣ) : K)] := by
    rw [coe_diagTwo]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat]
  simp only [Units.val_mul, coe_blockHom_of_det hdet1, hblock] at hD'
  have z := fun i j (hij : (![1, (μ : K), ((μ⁻¹ : Kˣ) : K)] : Fin 3 → K) i ≠
      ![1, (μ : K), ((μ⁻¹ : Kˣ) : K)] j) => entry_eq_zero_of_commute_diagonal hD' hij
  have m01 := z 0 1 (by simpa using hμ1.symm)
  have m02 := z 0 2 (by simpa using hμ1'.symm)
  have m10 := z 1 0 (by simpa using hμ1)
  have m12 := z 1 2 (by simpa using hμ2)
  have m20 := z 2 0 (by simpa using hμ1')
  have m21 := z 2 1 (by simpa using hμ2.symm)
  have hW := hM ⟨wTwo, wTwo_mem_slPi hK⟩
  have hW' := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hW
  simp only [Units.val_mul, coe_blockHom_of_det (det_eq_one_of_mem_slPi hK (wTwo_mem_slPi hK)),
    coe_wTwo] at hW'
  have e12 := congrFun (congrFun hW' 1) 2
  simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, m10] at e12
  have hdetM : Mm.det ≠ 0 := by
    rw [hMm]
    exact (M.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have hdiag : Mm = diagonal ![Mm 0 0, Mm 1 1, Mm 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hMm, m01, m02, m10, m12, m20, m21, e12]
  have hdetM' : Mm 0 0 * (Mm 1 1 * Mm 1 1) ≠ 0 := by
    rw [hdiag, det_diagonal, Fin.prod_univ_three] at hdetM
    simpa using hdetM
  have ha : Mm 0 0 ≠ 0 := left_ne_zero_of_mul hdetM'
  have hb : Mm 1 1 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hdetM')
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, Units.ext ?_⟩
  rw [coe_diagUnits, ← hMm, Units.val_mk0, Units.val_mk0]
  exact hdiag


theorem diagUnits_eq_scalar_mul (a b : Kˣ) :
    diagUnits a b b = GeneralLinearGroup.scalar (Fin 3) b * diagE (a * b⁻¹) := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, coe_diagE, Matrix.scalar_apply,
    diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp
  field_simp

theorem aut_fix_block (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {h₀ : GL (Fin 3) K} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) K)
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    (hfix : ∀ B : slPi π 2 (p ^ f) K, β (blockProj hK hh₀ B) = blockProj hK hh₀ B) :
    ∃ l : Kˣ, (π = false → (l : K) ^ (p ^ f + 1) = 1) ∧
      ∀ m : projImage (slPi π 3 (p ^ f) K), (β m : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹) * m *
          (ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹))⁻¹ := by
  obtain ⟨A, hA, σ, hβA⟩ := aut_semilinear hK hq2 β hβ
  have hcoe : ∀ B : slPi π 2 (p ^ f) K,
      ((β (blockProj hK hh₀ B) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) := by
    intro B
    rw [hfix B]
    rfl
  have hblockσ : ∀ B : slPi π 2 (p ^ f) K,
      A * frobGL σ (blockConj hK hh₀ B : slPi π 3 (p ^ f) K) * A⁻¹ =
        ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) := by
    intro B
    refine eq_of_mk_eq_block hK hq hq2 hh₀ ((MulAut.conj A).toMonoidHom.comp (frobGL σ))
      (fun B => ?_) B
    change ProjGenLinGroup.mk (A * frobGL σ ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) :
      GL (Fin 3) K) * A⁻¹) = _
    rw [← hβA _ (blockConj hK hh₀ B).2]
    exact hcoe B
  have hinner : ∃ A' ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
      (β m : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk A' * m * (ProjGenLinGroup.mk A')⁻¹ := by
    cases π
    · exact exists_inner_of_sq hK β hβ hA (mul_self_eq_one_of_trace hK hq hh₀ hblockσ) hβA
    · exact exists_inner_of_sq hK β hβ hA (by rw [eq_one_of_trace hK hh₀ hblockσ, mul_one]) hβA
  obtain ⟨A', hA', hβA'⟩ := hinner
  have hblock' : ∀ B : slPi π 2 (p ^ f) K,
      A' * ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * A'⁻¹ =
        ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) := by
    intro B
    refine eq_of_mk_eq_block hK hq hq2 hh₀ (MulAut.conj A').toMonoidHom (fun B => ?_) B
    change ProjGenLinGroup.mk (A' * ((blockConj hK hh₀ B : slPi π 3 (p ^ f) K) :
      GL (Fin 3) K) * A'⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    have h1 := hβA' (blockProj hK hh₀ B)
    rw [hcoe B] at h1
    exact h1.symm
  have hcomm : ∀ B : slPi π 2 (p ^ f) K,
      (h₀⁻¹ * A' * h₀) * blockHom (B : GL (Fin 2) K) =
        blockHom (B : GL (Fin 2) K) * (h₀⁻¹ * A' * h₀) := by
    intro B
    have h1 := hblock' B
    rw [coe_blockConj] at h1
    calc (h₀⁻¹ * A' * h₀) * blockHom (B : GL (Fin 2) K) =
        h₀⁻¹ * (A' * (h₀ * blockHom (B : GL (Fin 2) K) * h₀⁻¹) * A'⁻¹) * A' * h₀ := by group
      _ = h₀⁻¹ * (h₀ * blockHom (B : GL (Fin 2) K) * h₀⁻¹) * A' * h₀ := by rw [h1]
      _ = blockHom (B : GL (Fin 2) K) * (h₀⁻¹ * A' * h₀) := by group
  obtain ⟨a, b, hab⟩ := exists_diag_of_commute_block hK hq hq2 hcomm
  refine ⟨a * b⁻¹, ?_, fun m => ?_⟩
  · intro hπf
    subst hπf
    have h := hK.unitary
    have hmem : h₀⁻¹ * A' * h₀ ∈ glPi false 3 (p ^ f) K :=
      mul_mem (mul_mem (inv_mem hh₀) hA') hh₀
    rw [hab, mem_glPi_false h, coe_diagUnits] at hmem
    have e0 := congrFun (congrFun hmem 0) 0
    have e1 := congrFun (congrFun hmem 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, h.bar_apply] at e0 e1
    have ha1 : (a : K) ^ (p ^ f + 1) = 1 := by rw [pow_succ]; exact e0
    have hb1 : (b : K) ^ (p ^ f + 1) = 1 := by rw [pow_succ]; exact e1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow, ha1, hb1, inv_one, mul_one]
  · rw [hβA' m]
    have hmk : ProjGenLinGroup.mk A' = ProjGenLinGroup.mk (h₀ * diagE (a * b⁻¹) * h₀⁻¹) := by
      have e : A' = h₀ * (h₀⁻¹ * A' * h₀) * h₀⁻¹ := by group
      have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar b h₀).eq
      have e3 : h₀ * (GeneralLinearGroup.scalar (Fin 3) b * diagE (a * b⁻¹)) * h₀⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) b * (h₀ * diagE (a * b⁻¹) * h₀⁻¹) := by
        rw [← mul_assoc, hc]
        group
      rw [e, hab, diagUnits_eq_scalar_mul, e3, map_mul,
        mk_eq_one_iff_mem_statedScalars.mpr ⟨b, rfl⟩, one_mul]
    rw [hmk]

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
