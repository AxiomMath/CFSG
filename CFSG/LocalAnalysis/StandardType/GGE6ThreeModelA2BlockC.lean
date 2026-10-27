module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockB

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open scoped MatrixGroups
open Matrix


theorem commute_diagSL3_mem_range {Ω : Type} [Field Ω]
    {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL Tag.E6 Ω}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) {d : Fin 3 → Ωˣ}
    (hd : (d 0 : Ω) * d 1 * d 2 = 1) (hdist : ∀ i j : Fin 3, i ≠ j → d i ≠ d j)
    {u : ModGL Tag.E6 Ω} (hu : u ∈ rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)))
    (hcomm : u * ρ (diagSL3 d hd) = ρ (diagSL3 d hd) * u) :
    ∃ (d' : Fin 3 → Ωˣ) (hd' : (d' 0 : Ω) * d' 1 * d' 2 = 1), u = ρ (diagSL3 d' hd') := by
  obtain ⟨A, rfl⟩ := (rootSpan_a2Roots_eq_range hfr) ▸ hu
  have hAcomm : A * diagSL3 d hd = diagSL3 d hd * A := by
    apply hfr.injective
    rw [map_mul, map_mul]
    exact hcomm
  have hmat : ((A : Matrix (Fin 3) (Fin 3) Ω) * Matrix.diagonal (fun i => (d i : Ω)) =
      Matrix.diagonal (fun i => (d i : Ω)) * (A : Matrix (Fin 3) (Fin 3) Ω)) := by
    have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) Ω =>
      (B : Matrix (Fin 3) (Fin 3) Ω)) hAcomm
    simpa [coe_diagSL3] using h
  have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) Ω) i j = 0 :=
    fun i j hij =>
      offDiag_eq_zero_of_commute_diagonal hmat (fun h => hdist i j hij (Units.ext h))
  let ad : Fin 3 → Ω := fun i => (A : Matrix (Fin 3) (Fin 3) Ω) i i
  have hAeq : (A : Matrix (Fin 3) (Fin 3) Ω) = Matrix.diagonal ad := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [ad]
    · rw [hoff i j hij]
      exact (Matrix.diagonal_apply_ne ad hij).symm
  have hprod : ad 0 * ad 1 * ad 2 = 1 := by
    have hdet : (A : Matrix (Fin 3) (Fin 3) Ω).det = 1 := A.2
    rw [hAeq, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    exact hdet
  have hunit : ∀ i, ad i ≠ 0 := by
    have hne : ad 0 * ad 1 * ad 2 ≠ 0 := by rw [hprod]; exact one_ne_zero
    have h01 : ad 0 * ad 1 ≠ 0 := by
      intro h
      exact hne (by rw [h, zero_mul])
    have h0 : ad 0 ≠ 0 := fun h => h01 (by rw [h, zero_mul])
    have h1 : ad 1 ≠ 0 := fun h => h01 (by rw [h, mul_zero])
    have h2 : ad 2 ≠ 0 := by
      intro h
      exact hne (by rw [h, mul_zero])
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  let d' : Fin 3 → Ωˣ := fun i => Units.mk0 (ad i) (hunit i)
  have hd' : (d' 0 : Ω) * d' 1 * d' 2 = 1 := by
    simp only [d', Units.val_mk0]
    exact hprod
  have hdiagSL : diagSL3 d' hd' = A := by
    apply Subtype.ext
    rw [coe_diagSL3, hAeq]
    rfl
  exact ⟨d', hd', by rw [hdiagSL]⟩

theorem exists_diagSL3_pow {Ω : Type} [Field Ω] [IsAlgClosed Ω] (d' : Fin 3 → Ωˣ)
    (hd' : (d' 0 : Ω) * d' 1 * d' 2 = 1) {m : ℕ} (hm : m ≠ 0) :
    ∃ (s : Fin 3 → Ωˣ) (hs : (s 0 : Ω) * s 1 * s 2 = 1), ∀ i, s i ^ m = d' i := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq (d' 0 : Ω) hmpos
  obtain ⟨s1, hs1⟩ := IsAlgClosed.exists_pow_nat_eq (d' 1 : Ω) hmpos
  have hs0ne : s0 ≠ 0 := by
    intro h
    rw [h, zero_pow hm] at hs0
    exact (d' 0).ne_zero hs0.symm
  have hs1ne : s1 ≠ 0 := by
    intro h
    rw [h, zero_pow hm] at hs1
    exact (d' 1).ne_zero hs1.symm
  let s0u : Ωˣ := Units.mk0 s0 hs0ne
  let s1u : Ωˣ := Units.mk0 s1 hs1ne
  refine ⟨![s0u, s1u, (s0u * s1u)⁻¹], ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    exact mul_inv_cancel₀ (mul_ne_zero hs0ne hs1ne)
  · intro i
    fin_cases i
    · show s0u ^ m = d' 0
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact hs0
    · show s1u ^ m = d' 1
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact hs1
    · show ((s0u * s1u)⁻¹) ^ m = d' 2
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul,
        Units.val_mk0]
      rw [inv_pow, mul_pow]
      change (s0 ^ m * s1 ^ m)⁻¹ = (d' 2 : Ω)
      rw [hs0, hs1]
      exact inv_eq_of_mul_eq_one_right hd'

theorem frobE6_rho_diagSL3 {Ω : Type} [Field Ω]
    {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL Tag.E6 Ω}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {d : Fin 3 → Ωˣ} (hd : (d 0 : Ω) * d 1 * d 2 = 1) :
    frobE6 Fr (ρ (diagSL3 d hd)) = ρ (diagSL3 d hd) ^ q := by
  have hT : ρ (diagSL3 d hd) ∈ torusGroup Tag.E6 Ω :=
    hfr.diag (diagSL3 d hd) (fun i j hij => by simp [coe_diagSL3, hij])
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  rw [hb]
  change Units.map (entrywiseHom Fr) (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b ^ q
  rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr b, rootDiagUnit_pow]

end CFSG.StandardType.E6ThreeModel
