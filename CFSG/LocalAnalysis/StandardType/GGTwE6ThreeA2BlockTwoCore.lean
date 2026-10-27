module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwist
public import CFSG.Quasithin.Vol2.F134LieOddMatrix

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2
open scoped MatrixGroups
open Matrix


theorem rootSpan_a2Roots_eq_range {Ω : Type} [Field Ω]
    {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL Tag.E6 Ω}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) :
    rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)) = ρ.range := by
  rw [hfr.range]
  congr 1
  rw [frame_roots_eq (hneg := hfr.neg) (hadd := hfr.add) rfl rfl]
  ext r
  simp [a2Roots, e6A2Roots, neg_add]
  tauto

theorem exists_block_conj_diag {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (h3 : (3 : Ω) ≠ 0) {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL Tag.E6 Ω}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ)
    {t : ModGL Tag.E6 Ω} (ht : t ∈ torusGroup Tag.E6 Ω) :
    ∃ (d : Fin 3 → Ωˣ) (hd : (d 0 : Ω) * d 1 * d 2 = 1),
      (∀ i j : Fin 3, i ≠ j → d i ≠ d j) ∧
      ∃ (y : ModGL Tag.E6 Ω) (t₁ : ModGL Tag.E6 Ω),
        y ∈ rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)) ∧
        t₁ ∈ torusGroup Tag.E6 Ω ∧
        (∀ A : Matrix.SpecialLinearGroup (Fin 3) Ω, t₁ * ρ A = ρ A * t₁) ∧
        y * (ρ coxSL3 * t) * y⁻¹ = ρ (diagSL3 d hd) * t₁ := by
  classical
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial Ω)
    (by rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial Ω).degree = 2 by
      compute_degree!]; norm_num)
  have hω' : ω ^ 2 + ω + 1 = 0 := by simpa [Polynomial.IsRoot, Polynomial.eval_add] using hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω'
  have hω1 : ω ≠ 1 := by
    intro h; rw [h] at hω'; exact h3 (by linear_combination hω')
  have hωne : ω ≠ 0 := by intro h; rw [h] at hω3; norm_num at hω3
  have hω2ne : ω ^ 2 ≠ 1 := by
    intro h
    have h1 : ω = 1 := by
      have h2 : (1 : Ω) = ω := by
        calc (1 : Ω) = ω ^ 3 := hω3.symm
          _ = ω * ω ^ 2 := by ring
          _ = ω * 1 := by rw [h]
          _ = ω := mul_one ω
      exact h2.symm
    exact hω1 h1
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    apply hω2ne
    calc ω ^ 2 = ω ^ 3 := by linear_combination ω * h
      _ = 1 := hω3
  set ωu : Ωˣ := Units.mk0 ω hωne with hωu
  set d : Fin 3 → Ωˣ := ![1, ωu, ωu ^ 2] with hd
  have hdval : ∀ i, (d i : Ω) = ![1, ω, ω ^ 2] i := by
    intro i; fin_cases i <;> simp [hd, hωu]
  have hddet : (d 0 : Ω) * d 1 * d 2 = 1 := by
    simp only [hdval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination hω3
  have hddist : ∀ i j : Fin 3, i ≠ j → d i ≠ d j := by
    intro i j hij h
    have h' := congrArg (fun u : Ωˣ => (u : Ω)) h
    rw [hdval i, hdval j] at h'
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h'
         first
         | exact hω1 h'
         | exact hω1 h'.symm
         | exact hω2ne h'
         | exact hω2ne h'.symm
         | exact hωω2 h'
         | exact hωω2 h'.symm)
  obtain ⟨β, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set dd : Fin 3 → Ωˣ := fun i => rootChar β (σ i 0) with hdd
  have hddA : ∀ A, rootDiagUnit Tag.E6 β * ρ A * (rootDiagUnit Tag.E6 β)⁻¹ =
      ρ (conjDiag3 dd A) := fun A => hfr.torus β A
  have hdet0 : ((dd 0 : Ω) * dd 1 * dd 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (dd 0).ne_zero (dd 1).ne_zero) (dd 2).ne_zero
  obtain ⟨z0, hz0⟩ := IsAlgClosed.exists_pow_nat_eq (((dd 0 : Ω) * dd 1 * dd 2)⁻¹)
    (by norm_num : 0 < 3)
  have hz0ne : z0 ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
  set z : Ωˣ := Units.mk0 z0 hz0ne with hz
  set d' : Fin 3 → Ωˣ := fun i => z * dd i with hd'
  have hd'det : (d' 0 : Ω) * d' 1 * d' 2 = 1 := by
    simp only [hd', Units.val_mul, hz, Units.val_mk0]
    calc z0 * (dd 0 : Ω) * (z0 * dd 1) * (z0 * dd 2) = z0 ^ 3 * ((dd 0 : Ω) * dd 1 * dd 2) := by ring
      _ = 1 := by rw [hz0, inv_mul_cancel₀ hdet0]
  set D' : Matrix.SpecialLinearGroup (Fin 3) Ω := diagSL3 d' hd'det with hD'
  have hD'T : ρ D' ∈ torusGroup Tag.E6 Ω := hfr.diag D' (fun i j hij => by
    simp [hD', coe_diagSL3, hij])
  set t₂ : ModGL Tag.E6 Ω := (ρ D')⁻¹ * rootDiagUnit Tag.E6 β with ht₂
  have ht₂T : t₂ ∈ torusGroup Tag.E6 Ω := mul_mem (inv_mem hD'T) (rootDiagUnit_mem_torusGroup β)
  have ht₂c : ∀ A : Matrix.SpecialLinearGroup (Fin 3) Ω, t₂ * ρ A = ρ A * t₂ := by
    intro A
    have h1 : rootDiagUnit Tag.E6 β * ρ A * (rootDiagUnit Tag.E6 β)⁻¹ =
        ρ D' * ρ A * (ρ D')⁻¹ := by
      rw [hddA A, ← map_mul, ← map_inv, ← map_mul, diagSL3_conj dd z hd'det A]
    calc t₂ * ρ A = (ρ D')⁻¹ * (rootDiagUnit Tag.E6 β * ρ A * (rootDiagUnit Tag.E6 β)⁻¹) *
          rootDiagUnit Tag.E6 β := by rw [ht₂]; group
      _ = (ρ D')⁻¹ * (ρ D' * ρ A * (ρ D')⁻¹) * rootDiagUnit Tag.E6 β := by rw [h1]
      _ = ρ A * t₂ := by rw [ht₂]; group
  have hmD' : ((coxSL3 * D' : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      monoM₁ ((-1 : Ω) * (d' 0 : Ω)) ((-1 : Ω) * (d' 1 : Ω)) ((1 : Ω) * (d' 2 : Ω)) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_coxSL3, hD', coe_diagSL3, monoM₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have habc : ((-1 : Ω) * (d' 0 : Ω)) * ((-1 : Ω) * d' 1) * ((1 : Ω) * d' 2) = 1 := by
    calc ((-1 : Ω) * (d' 0 : Ω)) * ((-1) * d' 1) * ((1) * d' 2)
        = ((d' 0 : Ω) * d' 1 * d' 2) := by ring
      _ = 1 := hd'det
  obtain ⟨g', hg'⟩ : ∃ g' : Matrix.SpecialLinearGroup (Fin 3) Ω,
      ((g'⁻¹ * (coxSL3 * D') * g' : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) = Matrix.diagonal (fun i => (d i : Ω)) := by
    have hdiag : Matrix.diagonal (fun i => (d i : Ω)) = Matrix.diagonal ![1, ω, ω ^ 2] := by
      congr 1; funext i; exact hdval i
    rw [hdiag]
    exact exists_sl3_conj_M₁ hω' h3 habc (coxSL3 * D') hmD'
  set Hdiag : Matrix.SpecialLinearGroup (Fin 3) Ω := diagSL3 d hddet with hHdiag
  have hHdiagT : ρ Hdiag ∈ torusGroup Tag.E6 Ω := hfr.diag Hdiag (fun i j hij => by
    simp [hHdiag, coe_diagSL3, hij])
  have hconv : ρ (g'⁻¹ * (coxSL3 * D') * g') = ρ Hdiag := by
    apply congrArg ρ
    apply Subtype.ext
    rw [hg']
    show (Matrix.diagonal fun i => (d i : Ω)) =
      ((Hdiag : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)
    rw [hHdiag, coe_diagSL3]
  have hspan := rootSpan_a2Roots_eq_range hfr
  refine ⟨d, hddet, hddist, ρ (g'⁻¹), t₂, ?_, ht₂T, ht₂c, ?_⟩
  · rw [hspan]
    exact ⟨g'⁻¹, rfl⟩
  · have hstep : ρ (g'⁻¹) * (ρ coxSL3 * rootDiagUnit Tag.E6 β) * (ρ (g'⁻¹))⁻¹ =
        ρ (g'⁻¹ * (coxSL3 * D') * g') * (ρ D')⁻¹ * rootDiagUnit Tag.E6 β := by
      rw [show (ρ (g'⁻¹))⁻¹ = ρ g' by rw [← map_inv, inv_inv]]
      have h1 : ρ g'⁻¹ * (ρ coxSL3 * rootDiagUnit Tag.E6 β) * ρ g' =
          ρ g'⁻¹ * ρ coxSL3 *
            (rootDiagUnit Tag.E6 β * ρ g' * (rootDiagUnit Tag.E6 β)⁻¹) *
              rootDiagUnit Tag.E6 β := by
        group
      rw [h1, hddA g', ← diagSL3_conj dd z hd'det g']
      simp only [map_mul, map_inv]
      have hD'eq : diagSL3 (fun i => z * dd i) hd'det = D' := by
        rw [hD']
      rw [hD'eq]
      group
    rw [hstep, hconv, ht₂, hHdiag]
    group


theorem theta_eq_of_mem_torusGroup_pow_three {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    {u : ModGL Tag.E6 Ω} (hu : u ∈ torusGroup Tag.E6 Ω) (hu3 : u ^ 3 = 1) :
    TwistedDiag.theta Fr u = u := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hb3 : b ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [← rootDiagUnit_pow, hu3, rootDiagUnit_one]
    exact DiagTorus.rootDiagUnit_injective h1
  obtain ⟨m, hm⟩ := h3
  have hq : b ^ q = b⁻¹ := by
    have h1 : b ^ q * b = 1 := by
      rw [← pow_succ, show q + 1 = 3 * m by omega, pow_mul, hb3, one_pow]
    calc b ^ q = b ^ q * b * b⁻¹ := by group
      _ = 1 * b⁻¹ := by rw [h1]
      _ = b⁻¹ := one_mul _
  rw [TwistedDiag.theta_rootDiagUnit Fr hFr, hq, inv_inv]

theorem mem_torusGroup_of_mem_rootSpan_commute_diag {Ω : Type} [Field Ω]
    {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL Tag.E6 Ω}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ)
    {d : Fin 3 → Ωˣ} (hd : (d 0 : Ω) * d 1 * d 2 = 1)
    (hdist : ∀ i j : Fin 3, i ≠ j → d i ≠ d j)
    {q : ModGL Tag.E6 Ω}
    (hq : q ∈ rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)))
    (hcomm : q * ρ (diagSL3 d hd) = ρ (diagSL3 d hd) * q) :
    q ∈ torusGroup Tag.E6 Ω := by
  obtain ⟨A, rfl⟩ := (rootSpan_a2Roots_eq_range hfr) ▸ hq
  have hAcomm : A * diagSL3 d hd = diagSL3 d hd * A := by
    apply hfr.injective
    rw [map_mul, map_mul]
    exact hcomm
  have hmat : ((A : Matrix (Fin 3) (Fin 3) Ω) * Matrix.diagonal (fun i => (d i : Ω)) =
      Matrix.diagonal (fun i => (d i : Ω)) * (A : Matrix (Fin 3) (Fin 3) Ω)) := by
    have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) Ω =>
      (B : Matrix (Fin 3) (Fin 3) Ω)) hAcomm
    simpa [coe_diagSL3] using h
  exact hfr.diag A (fun i j hij => by
    exact offDiag_eq_zero_of_commute_diagonal hmat
      (fun h => hdist i j hij (Units.ext h)))

theorem exists_torus_lang {Ω : Type} [Field Ω] [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {u : ModGL Tag.E6 Ω} (hu : u ∈ torusGroup Tag.E6 Ω) :
    ∃ s ∈ torusGroup Tag.E6 Ω, ((TwistedDiag.theta Fr) s)⁻¹ * s = u := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hpow : ∀ i, ∃ b : Ω, b ^ (q + 1) = (c i : Ω) := fun i =>
    IsAlgClosed.exists_pow_nat_eq (c i : Ω) (Nat.succ_pos q)
  choose b hb using hpow
  have hbne : ∀ i, b i ≠ 0 := by
    intro i h
    have hbi := hb i
    rw [h] at hbi
    simp only [zero_pow (Nat.succ_ne_zero q)] at hbi
    exact (c i).ne_zero hbi.symm
  set bu : Fin Tag.E6.rank → Ωˣ := fun i => Units.mk0 (b i) (hbne i) with hbu
  refine ⟨rootDiagUnit Tag.E6 bu, rootDiagUnit_mem_torusGroup _, ?_⟩
  have htheta : TwistedDiag.theta Fr (rootDiagUnit Tag.E6 bu) =
      rootDiagUnit Tag.E6 (bu ^ q)⁻¹ :=
    TwistedDiag.theta_rootDiagUnit Fr hFr _
  conv_lhs => rw [htheta]
  change rootDiagUnit Tag.E6 (((bu ^ q)⁻¹)⁻¹) * rootDiagUnit Tag.E6 bu =
    rootDiagUnit Tag.E6 c
  rw [inv_inv, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp only [hbu, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_mk0, Units.ext_iff]
  have hbi := hb i
  rw [← hbi]
  ring

theorem exists_zetaVec_eq_of_mem_torusGroup_pow_three {Ω : Type} [Field Ω]
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {u : ModGL Tag.E6 Ω} (hu : u ∈ torusGroup Tag.E6 Ω) (hu3 : u ^ 3 = 1) :
    ∃ v, u = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hb : b ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [← rootDiagUnit_pow, hu3, rootDiagUnit_one]
    exact DiagTorus.rootDiagUnit_injective h1
  obtain ⟨v, rfl⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb
  exact ⟨v, rfl⟩
