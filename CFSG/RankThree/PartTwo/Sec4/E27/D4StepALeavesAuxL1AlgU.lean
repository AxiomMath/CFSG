module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Sc
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Alg

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix
open CFSG.RankThree.Classical2 (unitarySet)

section UnitaryRational

variable {ℓ f : ℕ} [Fact ℓ.Prime] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ]

noncomputable abbrev frobQ (ℓ f : ℕ) [Fact ℓ.Prime] (Ω : Type) [Field Ω] [CharP Ω ℓ] : Ω →+* Ω :=
  iterateFrobenius Ω ℓ f

theorem frobQ_apply (z : Ω) : frobQ ℓ f Ω z = z ^ (ℓ ^ f) := iterateFrobenius_def ℓ f z

noncomputable def barM (ℓ f : ℕ) [Fact ℓ.Prime] (Ω : Type) [Field Ω] [CharP Ω ℓ]
    (M : Matrix (Fin 3) (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω :=
  (M.map (frobQ ℓ f Ω))ᵀ

theorem barM_apply (M : Matrix (Fin 3) (Fin 3) Ω) (i j : Fin 3) :
    barM ℓ f Ω M i j = M j i ^ (ℓ ^ f) := by
  simp only [barM, Matrix.transpose_apply, Matrix.map_apply, frobQ_apply]

theorem barM_mul (M M' : Matrix (Fin 3) (Fin 3) Ω) :
    barM ℓ f Ω (M * M') = barM ℓ f Ω M' * barM ℓ f Ω M := by
  simp only [barM]
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem barM_one : barM ℓ f Ω (1 : Matrix (Fin 3) (Fin 3) Ω) = 1 := by
  simp only [barM]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem barM_smul (c : Ω) (M : Matrix (Fin 3) (Fin 3) Ω) :
    barM ℓ f Ω (c • M) = (c ^ (ℓ ^ f)) • barM ℓ f Ω M := by
  ext i j
  simp only [barM_apply, Matrix.smul_apply, smul_eq_mul, mul_pow]

theorem barM_barM_apply (M : Matrix (Fin 3) (Fin 3) Ω) (i j : Fin 3) :
    barM ℓ f Ω (barM ℓ f Ω M) i j = M i j ^ (ℓ ^ f) ^ 2 := by
  rw [barM_apply, barM_apply, ← pow_mul, sq]

theorem barM_mul_of_mem_unitarySet {Y : GL (Fin 3) Ω} (hY : Y ∈ unitarySet (ℓ ^ f) 3) :
    barM ℓ f Ω (Y : Matrix (Fin 3) (Fin 3) Ω) * (Y : Matrix (Fin 3) (Fin 3) Ω) = 1 := by
  have h := hY.2.2
  have hfun : (⇑(frobQ ℓ f Ω) : Ω → Ω) = fun z => z ^ (ℓ ^ f) := funext frobQ_apply
  simp only [barM, hfun]
  exact h

theorem exists_unitary_scalar_mul (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) (N : GL (Fin 3) Ω)
    (hN : ∀ Y : GL (Fin 3) Ω, Y ∈ unitarySet (ℓ ^ f) 3 → N * Y * N⁻¹ ∈ unitarySet (ℓ ^ f) 3) :
    ∃ (c : Ω) (A : Matrix (Fin 3) (Fin 3) Ω), c ≠ 0 ∧ (N : Matrix (Fin 3) (Fin 3) Ω) = c • A ∧
      (∀ i j, A i j ^ (ℓ ^ f) ^ 2 = A i j) ∧ barM ℓ f Ω A * A = 1 := by
  classical
  set A : Matrix (Fin 3) (Fin 3) Ω := (N : Matrix (Fin 3) (Fin 3) Ω) with hA
  set A' : Matrix (Fin 3) (Fin 3) Ω := ((N⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set bA := barM ℓ f Ω A with hbA
  set bA' := barM ℓ f Ω A' with hbA'
  have hbb : bA * bA' = 1 := by rw [hbA, hbA', ← barM_mul, hA'A, barM_one]
  have hbb' : bA' * bA = 1 := by rw [hbA, hbA', ← barM_mul, hAA', barM_one]
  have hcomm : ∀ Y : GL (Fin 3) Ω, Y ∈ unitarySet (ℓ ^ f) 3 →
      (bA * A) * (Y : Matrix (Fin 3) (Fin 3) Ω) = (Y : Matrix (Fin 3) (Fin 3) Ω) * (bA * A) := by
    intro Y hY
    set Ym : Matrix (Fin 3) (Fin 3) Ω := (Y : Matrix (Fin 3) (Fin 3) Ω) with hYm
    have hY1 : barM ℓ f Ω Ym * Ym = 1 := barM_mul_of_mem_unitarySet hY
    have hY2 : Ym * barM ℓ f Ω Ym = 1 := mul_eq_one_comm.1 hY1
    have hY' := barM_mul_of_mem_unitarySet (hN Y hY)
    rw [Units.val_mul, Units.val_mul, barM_mul, barM_mul] at hY'
    have h3 : barM ℓ f Ω Ym * (bA * A) * Ym = bA * A := by
      calc barM ℓ f Ω Ym * (bA * A) * Ym
          = (bA * bA') * (barM ℓ f Ω Ym * (bA * A) * Ym) * (A' * A) := by
            rw [hbb, hA'A, Matrix.one_mul, Matrix.mul_one]
        _ = bA * (bA' * (barM ℓ f Ω Ym * bA) * (A * Ym * A')) * A := by
            simp only [Matrix.mul_assoc]
        _ = bA * A := by rw [hY', Matrix.mul_one]
    calc (bA * A) * Ym = (Ym * barM ℓ f Ω Ym) * (bA * A) * Ym := by rw [hY2, Matrix.one_mul]
      _ = Ym * (barM ℓ f Ω Ym * (bA * A) * Ym) := by simp only [Matrix.mul_assoc]
      _ = Ym * (bA * A) := by rw [h3]
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Two.scalar_of_commute_unitarySet
    hℓ3 hq1 (M := bA * A) (fun Y hY => hcomm Y hY)
  have hμ' : bA * A = μ • (1 : Matrix (Fin 3) (Fin 3) Ω) := by
    rw [hμ]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ'
    have : (1 : Matrix (Fin 3) (Fin 3) Ω) = 0 := by
      calc (1 : Matrix (Fin 3) (Fin 3) Ω) = (bA' * bA) * (A * A') := by rw [hbb', hAA', Matrix.one_mul]
        _ = bA' * (bA * A) * A' := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hμ', Matrix.mul_zero, Matrix.zero_mul]
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq μ⁻¹ (n := ℓ ^ f + 1) (Nat.succ_pos _)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at hc
    exact inv_ne_zero hμ0 hc.symm
  set A₁ : Matrix (Fin 3) (Fin 3) Ω := c • A with hA₁
  have hcc : c ^ (ℓ ^ f) * c * μ = 1 := by
    calc c ^ (ℓ ^ f) * c * μ = c ^ (ℓ ^ f + 1) * μ := by rw [pow_succ]
      _ = μ⁻¹ * μ := by rw [hc]
      _ = 1 := inv_mul_cancel₀ hμ0
  have hA₁1 : barM ℓ f Ω A₁ * A₁ = 1 := by
    rw [hA₁, barM_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hbA, hμ', smul_smul, hcc,
      one_smul]
  have hbarbar : barM ℓ f Ω (barM ℓ f Ω A₁) = A₁ := by
    have h1 : barM ℓ f Ω A₁ * barM ℓ f Ω (barM ℓ f Ω A₁) = 1 := by
      have := congrArg (barM ℓ f Ω) hA₁1
      rwa [barM_mul, barM_one] at this
    have h2 : A₁ * barM ℓ f Ω A₁ = 1 := mul_eq_one_comm.1 hA₁1
    calc barM ℓ f Ω (barM ℓ f Ω A₁)
        = (A₁ * barM ℓ f Ω A₁) * barM ℓ f Ω (barM ℓ f Ω A₁) := by rw [h2, Matrix.one_mul]
      _ = A₁ * (barM ℓ f Ω A₁ * barM ℓ f Ω (barM ℓ f Ω A₁)) := by rw [Matrix.mul_assoc]
      _ = A₁ := by rw [h1, Matrix.mul_one]
  refine ⟨c⁻¹, A₁, inv_ne_zero hc0, ?_, ?_, hA₁1⟩
  · rw [hA₁, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · intro i j
    have := barM_barM_apply (ℓ := ℓ) (f := f) A₁ i j
    rw [hbarbar] at this
    exact this.symm

end UnitaryRational

section UnitaryAssembly

open CFSG.OddStandard.GH71.S55 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} [Fact ℓ.Prime] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ]

theorem unitaryFieldData_unitField (hf : 1 ≤ f) : UnitaryFieldData ℓ f (unitField Ω ℓ f) :=
  ⟨Fact.out, hf, by rw [card_unitField hf, ← pow_mul, mul_comm f 2]⟩

theorem mem_unitarySU_iff_pow {F : Type} [Field F] (hF : UnitaryFieldData ℓ f F) (B : GL (Fin 3) F) :
    B ∈ unitarySU ℓ f F 3 ↔ (B : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      ((B : Matrix (Fin 3) (Fin 3) F).map (· ^ ℓ ^ f))ᵀ * (B : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [mem_unitarySU_iff hF]
  have : (⇑hF.bar : F → F) = fun c => c ^ ℓ ^ f := funext hF.bar_apply
  simp only [this]

@[expose] noncomputable def unitGLEmb (ℓ f : ℕ) [Fact ℓ.Prime] (Ω : Type) [Field Ω] [CharP Ω ℓ] :
    GL (Fin 3) (unitField Ω ℓ f) →* GL (Fin 3) Ω :=
  Matrix.GeneralLinearGroup.map (unitField Ω ℓ f).subtype

theorem coe_unitGLEmb (B : GL (Fin 3) (unitField Ω ℓ f)) :
    ((unitGLEmb ℓ f Ω B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      (B : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f)).map (unitField Ω ℓ f).subtype := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply _ i j B

theorem unitGLEmb_injective : Function.Injective (unitGLEmb ℓ f Ω) := by
  intro A B h
  have h1 := congrArg (fun X : GL (Fin 3) Ω => (X : Matrix (Fin 3) (Fin 3) Ω)) h
  simp only [coe_unitGLEmb] at h1
  exact Units.ext (Matrix.map_injective Subtype.val_injective h1)

theorem unitGLEmb_mem_unitarySet (hf : 1 ≤ f) {B : GL (Fin 3) (unitField Ω ℓ f)}
    (hB : B ∈ unitarySU ℓ f (unitField Ω ℓ f) 3) : unitGLEmb ℓ f Ω B ∈ unitarySet (ℓ ^ f) 3 := by
  obtain ⟨hdet, horth⟩ := (mem_unitarySU_iff_pow (unitaryFieldData_unitField (Ω := Ω) hf) B).1 hB
  have hpow : ∀ M : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f),
      (M.map (unitField Ω ℓ f).subtype).map (· ^ ℓ ^ f) =
        (M.map (· ^ ℓ ^ f)).map (unitField Ω ℓ f).subtype := fun M => by
    ext i j
    simp
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [coe_unitGLEmb]
    exact (mem_unitField_iff _).1 (B i j).2
  · rw [coe_unitGLEmb, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · rw [coe_unitGLEmb, hpow, ← Matrix.transpose_map, ← Matrix.map_mul, horth,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_unitGLEmb_of_mem_unitarySet (hf : 1 ≤ f) {Y : GL (Fin 3) Ω}
    (hY : Y ∈ unitarySet (ℓ ^ f) 3) :
    ∃ B : GL (Fin 3) (unitField Ω ℓ f), B ∈ unitarySU ℓ f (unitField Ω ℓ f) 3 ∧
      unitGLEmb ℓ f Ω B = Y := by
  classical
  obtain ⟨hent, hdet, horth⟩ := hY
  set M : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f) := Matrix.of fun i j =>
    ⟨(Y : Matrix (Fin 3) (Fin 3) Ω) i j, (mem_unitField_iff _).2 (hent i j)⟩ with hMdef
  have hM : M.map (unitField Ω ℓ f).subtype = (Y : Matrix (Fin 3) (Fin 3) Ω) := by
    ext i j
    rfl
  have hMdet : M.det = 1 := by
    apply (unitField Ω ℓ f).subtype.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, hdet, map_one]
  set B := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero) with hBdef
  have hB : (B : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f)) = M := rfl
  have hpow : ∀ M : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f),
      (M.map (unitField Ω ℓ f).subtype).map (· ^ ℓ ^ f) =
        (M.map (· ^ ℓ ^ f)).map (unitField Ω ℓ f).subtype := fun M => by
    ext i j
    simp
  refine ⟨B, (mem_unitarySU_iff_pow (unitaryFieldData_unitField (Ω := Ω) hf) B).2
    ⟨by rw [hB, hMdet], ?_⟩, ?_⟩
  · apply Matrix.map_injective Subtype.val_injective
    change ((M.map (· ^ ℓ ^ f))ᵀ * M).map (unitField Ω ℓ f).subtype =
      (1 : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f)).map (unitField Ω ℓ f).subtype
    rw [Matrix.map_mul, Matrix.transpose_map, ← hpow, hM, horth,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · apply Units.ext
    rw [coe_unitGLEmb, hB, hM]

theorem unitary_layer_model_of_interface {G₀ : Type*} [Group G₀] (D C : Subgroup G₀)
    (hnorm : ∀ g ∈ C, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hq1 : ℓ ^ f % 3 = 2)
    (s : D →* GL (Fin 3) Ω) (hs : Function.Injective s)
    (hrange : ∀ Y : GL (Fin 3) Ω, Y ∈ s.range ↔ Y ∈ unitarySet (ℓ ^ f) 3)
    (hact : ∀ g ∈ C, ∃ N : GL (Fin 3) Ω, ∀ d d' : D, (d' : G₀) = g * d * g⁻¹ →
      s d' = N * s d * N⁻¹) :
    ∃ (F : Type) (_ : Field F) (hF : UnitaryFieldData ℓ f F) (e : D ≃* unitarySU ℓ f F 3),
      ∀ g ∈ C, ∃ A : unitaryIsom3 hF, ∀ d d' : D, (d' : G₀) = g * d * g⁻¹ →
        e d' = suConj hF A (e d) := by
  classical
  have hF := unitaryFieldData_unitField (Ω := Ω) (ℓ := ℓ) hf
  refine ⟨↥(unitField Ω ℓ f), inferInstance, hF, ?_⟩
  let φ : unitarySU ℓ f (unitField Ω ℓ f) 3 →* GL (Fin 3) Ω :=
    (unitGLEmb ℓ f Ω).comp (unitarySU ℓ f (unitField Ω ℓ f) 3).subtype
  have hφinj : Function.Injective φ := fun A B h =>
    Subtype.ext (unitGLEmb_injective h)
  have hφrange : ∀ Y : GL (Fin 3) Ω, Y ∈ φ.range ↔ Y ∈ unitarySet (ℓ ^ f) 3 := by
    intro Y
    constructor
    · rintro ⟨B, rfl⟩
      exact unitGLEmb_mem_unitarySet hf B.2
    · intro hY
      obtain ⟨B, hB, hBY⟩ := exists_unitGLEmb_of_mem_unitarySet hf hY
      exact ⟨⟨B, hB⟩, hBY⟩
  have hrange_eq : s.range = φ.range := Subgroup.ext fun Y => (hrange Y).trans (hφrange Y).symm
  let e : D ≃* unitarySU ℓ f (unitField Ω ℓ f) 3 :=
    ((MonoidHom.ofInjective hs).trans (MulEquiv.subgroupCongr hrange_eq)).trans
      (MonoidHom.ofInjective hφinj).symm
  have heD : ∀ d : D, φ (e d) = s d := fun d =>
    MonoidHom.apply_ofInjective_symm hφinj
      (MulEquiv.subgroupCongr hrange_eq (MonoidHom.ofInjective hs d))
  refine ⟨e, fun g hg => ?_⟩
  obtain ⟨N, hN⟩ := hact g hg
  have hNnorm : ∀ Y : GL (Fin 3) Ω, Y ∈ unitarySet (ℓ ^ f) 3 →
      N * Y * N⁻¹ ∈ unitarySet (ℓ ^ f) 3 := by
    intro Y hY
    obtain ⟨d, hd⟩ := (hrange Y).2 hY
    have hd' : g * (d : G₀) * g⁻¹ ∈ D := hnorm g hg d d.2
    have h1 := hN d ⟨_, hd'⟩ rfl
    rw [hd] at h1
    exact (hrange _).1 ⟨⟨_, hd'⟩, h1⟩
  obtain ⟨c, A₁, hc0, hNA, hent, hA₁1⟩ := exists_unitary_scalar_mul hℓ3 hq1 N hNnorm
  set Â : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f) := Matrix.of fun i j =>
    ⟨A₁ i j, (mem_unitField_iff _).2 (hent i j)⟩ with hÂdef
  have hÂmap : Â.map (unitField Ω ℓ f).subtype = A₁ := by
    ext i j
    rfl
  have hdetA₁ : A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA₁1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetÂ : Â.det ≠ 0 := by
    intro h0
    apply hdetA₁
    rw [← hÂmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  set B : GL (Fin 3) (unitField Ω ℓ f) := Matrix.GeneralLinearGroup.mkOfDetNeZero Â hdetÂ with hBdef
  have hBmat : (B : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f)) = Â := rfl
  have hB : B ∈ unitaryIsom3 hF := by
    rw [mem_unitaryIsom3, hBmat]
    apply Matrix.map_injective Subtype.val_injective
    have hfun : (⇑hF.bar : (unitField Ω ℓ f) → (unitField Ω ℓ f)) = fun z => z ^ ℓ ^ f :=
      funext hF.bar_apply
    have hpow : ∀ M : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f),
        (M.map (unitField Ω ℓ f).subtype).map (· ^ ℓ ^ f) =
          (M.map (· ^ ℓ ^ f)).map (unitField Ω ℓ f).subtype := fun M => by
      ext i j
      simp
    change ((Â.map hF.bar)ᵀ * Â).map (unitField Ω ℓ f).subtype =
      (1 : Matrix (Fin 3) (Fin 3) (unitField Ω ℓ f)).map (unitField Ω ℓ f).subtype
    rw [hfun, Matrix.map_mul, Matrix.transpose_map, ← hpow, hÂmap,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (A₁.map (· ^ ℓ ^ f))ᵀ * A₁ = 1 := by
      have h3 := hA₁1
      simp only [barM, frobQ] at h3
      have hfun2 : (⇑(iterateFrobenius Ω ℓ f) : Ω → Ω) = fun z => z ^ ℓ ^ f :=
        funext fun z => iterateFrobenius_def ℓ f z
      simpa [hfun2] using h3
    exact h2
  refine ⟨⟨B, hB⟩, fun d d' hdd' => ?_⟩
  have hBA : ((unitGLEmb ℓ f Ω B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = A₁ := by
    rw [coe_unitGLEmb, hBmat, hÂmap]
  have hBB' : ((unitGLEmb ℓ f Ω B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) *
      (((unitGLEmb ℓ f Ω B)⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNB : ∀ Y : GL (Fin 3) Ω, N * Y * N⁻¹ = unitGLEmb ℓ f Ω B * Y * (unitGLEmb ℓ f Ω B)⁻¹ := by
    intro Y
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
    have hNs : ((N : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = c • (A₁ : Matrix (Fin 3) (Fin 3) Ω) := hNA
    exact coe_conj_eq_of_eq_smul N _ _ c hc0 (by rw [hBA]; exact hNs) hBB' _
  have h1 := hN d d' hdd'
  rw [← heD d', ← heD d, hNB] at h1
  have h2 : unitGLEmb ℓ f Ω (e d' : GL (Fin 3) (unitField Ω ℓ f)) =
      unitGLEmb ℓ f Ω (B * (e d : GL (Fin 3) (unitField Ω ℓ f)) * B⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact h1
  apply Subtype.ext
  rw [coe_suConj]
  exact unitGLEmb_injective h2

end UnitaryAssembly

end CFSG.RankThree.PartTwo.Sec4.E27
