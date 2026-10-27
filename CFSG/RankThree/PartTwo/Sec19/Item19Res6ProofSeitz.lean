module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzAut
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitz
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryArith
public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitz199

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K}

section Pair

variable (h : UnitaryFieldData p f K) (h₀ : UnitaryFieldData p e k)
  (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

include hbar in
theorem eq_top_of_two_conj_su (hfe : f = 3 * e) (hq : p ^ e ≠ 2)
    {Y : Subgroup (unitarySU p f K 3)} (H H' : unitaryIsom3 h)
    (hY : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) → suConj h H g ∈ Y)
    (hY' : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) → suConj h H' g ∈ Y)
    (hne : ¬ ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        ∀ i j, (((suConj h (H'⁻¹ * H) g : unitarySU p f K 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) i j ∈ k) :
    Y = ⊤ := by
  classical
  have hbar' : ∀ c : k, ((h₀.bar c : k) : K) = h.bar (c : K) := fun c => (hbar c).symm
  set S := gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hS
  set ε : unitarySU p f K 3 ≃* S := suGramEquiv h with hε
  set A : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨((H⁻¹ * H' : unitaryIsom3 h) : GL (Fin 3) K), mem_primeFormUnitary_one (H⁻¹ * H').2⟩
    with hA
  set R := CFSG.RankThree.PartOne.CTP.suSub h h₀ hbar' 3 with hR
  set c := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjSU h
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A).toMonoidHom with hc
  have hcv : ∀ x : S, ((c x : S) : GL (Fin 3) K) =
      ((H⁻¹ * H' : unitaryIsom3 h) : GL (Fin 3) K) * x *
        ((H⁻¹ * H' : unitaryIsom3 h) : GL (Fin 3) K)⁻¹ :=
    fun x => rfl
  have hRk : ∀ x ∈ R, ∀ i j, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
    rintro _ ⟨z, rfl⟩ i j
    change ((CFSG.RankThree.Classical.subfieldGL k 3 (z : GL (Fin 3) k) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j ∈ k
    rw [CFSG.RankThree.Classical.coe_subfieldGL, Matrix.map_apply]
    exact ((z : GL (Fin 3) k) i j).2
  have hkR : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) → ε g ∈ R := by
    intro g hgk
    obtain ⟨z, hz, hzg⟩ := exists_unitarySU_of_mem h h₀ hbar g.2 hgk
    have hzS : z ∈ gramSU h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [← unitarySU_three_eq_gramSU h₀]
      exact hz
    refine ⟨⟨z, hzS⟩, Subtype.ext ?_⟩
    change GeneralLinearGroup.map k.subtype z = (g : GL (Fin 3) K)
    exact hzg
  have hneR : R.map c ≠ R := by
    intro heq
    apply hne
    intro g hg i j
    have hmem : ε g ∈ R.map c := by
      rw [heq]
      exact hkR g hg
    obtain ⟨y, hy, hyg⟩ := hmem
    have h1 : ((c y : S) : GL (Fin 3) K) = (g : GL (Fin 3) K) :=
      congrArg (fun x : S => (x : GL (Fin 3) K)) hyg
    rw [hcv] at h1
    have h2 : ((suConj h (H'⁻¹ * H) g : unitarySU p f K 3) : GL (Fin 3) K) =
        (y : GL (Fin 3) K) := by
      rw [coe_suConj, ← h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact hRk y hy i j
  have hgen := CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_ne_two p f e K h k h₀ hbar' 3
    Nat.prime_three (by norm_num) hfe hq 3 le_rfl A hneR
  set Y' : Subgroup S := (Y.comap (suConj h H).toMonoidHom).comap ε.symm.toMonoidHom with hY'def
  have hRY : R ≤ Y' := by
    intro x hx
    show suConj h H (ε.symm x) ∈ Y
    exact hY _ (hRk x hx)
  have hcRY : R.map c ≤ Y' := by
    rintro _ ⟨x, hx, rfl⟩
    show suConj h H (ε.symm (c x)) ∈ Y
    have he : suConj h H (ε.symm (c x)) = suConj h H' (ε.symm x) := by
      apply Subtype.ext
      rw [coe_suConj, coe_suConj]
      change (H : GL (Fin 3) K) * (((c x : S) : GL (Fin 3) K)) * ((H⁻¹ : unitaryIsom3 h) :
        GL (Fin 3) K) = (H' : GL (Fin 3) K) * (x : GL (Fin 3) K) *
          ((H'⁻¹ : unitaryIsom3 h) : GL (Fin 3) K)
      rw [hcv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [he]
    exact hY' _ (hRk x hx)
  have hYtop : Y' = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hRY hx
    · exact hcRY hx
  rw [eq_top_iff]
  intro y _
  have hy' : ε ((suConj h H).symm y) ∈ Y' := by rw [hYtop]; trivial
  change suConj h H (ε.symm (ε ((suConj h H).symm y))) ∈ Y at hy'
  rwa [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at hy'

end Pair

theorem swapMat_mem (i j : Fin 3) : swapMat K i j ∈ k := by
  fin_cases i <;> fin_cases j <;> simp [swapMat, k.zero_mem, k.one_mem, k.neg_mem]

theorem swapMat'_mem (i j : Fin 3) : swapMat' K i j ∈ k := by
  fin_cases i <;> fin_cases j <;> simp [swapMat', k.zero_mem, k.one_mem, k.neg_mem]

theorem closure_fixSet_eq_top_of_field {p f : ℕ}
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) (hq : 2 < p ^ f) (hQ8 : p ^ f ≠ 8)
    (D : Subgroup (MulAut (unitarySU p f K 3))) (hD3 : ∀ φ ∈ D, φ ^ 3 = 1)
    {φ : MulAut (unitarySU p f K 3)} (hφD : φ ∈ D) (hφ : φ ∉ (suConj h).range)
    {e : MulAut (unitarySU p f K 3)} (he : e ∈ D) {s : unitarySU p f K 3}
    (hsD : MulAut.conj s ∈ D) (hes : e s ≠ s) :
    Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤ := by
  classical
  have := h.finite
  have hsZ : s ∉ Subgroup.center (unitarySU p f K 3) := fun hs =>
    hes (apply_eq_of_mem_center h hq (hD3 e he) hs)
  obtain ⟨σ, hσ, H, hφH⟩ := eq_conj_suField_of_not_mem hq (hD3 φ hφD) hφ
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : MulAut (unitarySU p f K 3), ψ = φ * MulAut.conj s := ⟨_, rfl⟩
  have hψD : ψ ∈ D := hψdef ▸ D.mul_mem hφD hsD
  have hψ : ψ ∉ (suConj h).range := by
    rintro ⟨B, hB⟩
    apply hφ
    refine ⟨B * (⟨s, unitarySU_le_unitaryIsom3 s.2⟩ : unitaryIsom3 h)⁻¹, ?_⟩
    rw [map_mul, map_inv, hB, hψdef, conj_eq_suConj (h := h) s, mul_inv_cancel_right]
  obtain ⟨σ', hσ', H', hψH'⟩ := eq_conj_suField_of_not_mem hq (hD3 ψ hψD) hψ
  obtain ⟨e₀, hfe, he₀, hkcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p e₀ (fixedField σ) := ⟨h.prime, he₀, hkcard⟩
  have hbar := bar_coe_fixedField h hfe h₀
  have hk : ∀ x, x ∈ fixedField σ ↔ σ x = x := mem_fixedField_iff σ
  have hk' : ∀ x, x ∈ fixedField σ ↔ σ' x = x := by
    intro x
    rw [hk]
    rcases Sec14.Item148Rank.ringAut_eq_or_mul_eq_one148 h.prime (by have := h.one_le; omega)
      h.card hσ hσ' with h1 | h1
    · rw [h1]
    · have h2 : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hinv : ∀ y, σ⁻¹ (σ y) = y := fun y => by simp
      have hinv' : ∀ y, σ (σ⁻¹ y) = y := fun y => by simp
      rw [h2]
      constructor
      · intro hx
        calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hx]
          _ = x := hinv x
      · intro hx
        calc σ x = σ (σ⁻¹ x) := by rw [hx]
          _ = x := hinv' x
  have hq0 : p ^ e₀ ≠ 2 := by
    intro h2
    apply hQ8
    rw [hfe, pow_mul', h2]
    norm_num
  have hφ1 : φ ≠ 1 := fun h1 => hφ ⟨1, by rw [map_one, h1]⟩
  have hψ1 : ψ ≠ 1 := fun h1 => hψ ⟨1, by rw [map_one, h1]⟩
  have hY : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        suConj h H g ∈ Subgroup.closure
          (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) := by
    intro g hg
    refine Subgroup.subset_closure ⟨φ, hφD, hφ1, ?_⟩
    rw [hφH]
    exact conj_suField_fix H σ g fun i j => (hk _).1 (hg i j)
  have hY' : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        suConj h H' g ∈ Subgroup.closure
          (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) := by
    intro g hg
    refine Subgroup.subset_closure ⟨ψ, hψD, hψ1, ?_⟩
    rw [hψH']
    exact conj_suField_fix H' σ' g fun i j => (hk' _).1 (hg i j)
  refine eq_top_of_two_conj_su h h₀ hbar hfe hq0 H H' hY hY' ?_
  intro hall
  apply hsZ
  have hcomm : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        s * suConj h H g = suConj h H g * s := by
    intro g hg
    have hx1 : φ (suConj h H g) = suConj h H g := by
      rw [hφH]
      exact conj_suField_fix H σ g fun i j => (hk _).1 (hg i j)
    have hxH' : suConj h H g = suConj h H' (suConj h (H'⁻¹ * H) g) := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    have hx2 : ψ (suConj h H g) = suConj h H g := by
      rw [hxH', hψH']
      exact conj_suField_fix H' σ' _ fun i j => (hk' _).1 (hall g hg i j)
    have h3 : φ (MulAut.conj s (suConj h H g)) = φ (suConj h H g) := by
      rw [hx1]
      rw [hψdef, MulAut.mul_apply] at hx2
      exact hx2
    have h4 : MulAut.conj s (suConj h H g) = suConj h H g := φ.injective h3
    rw [MulAut.conj_apply] at h4
    calc s * suConj h H g = s * suConj h H g * s⁻¹ * s := by group
      _ = suConj h H g * s := by rw [h4]
  have hK3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
    rw [hpow]
    have h1 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hQ]
    have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ω, hω⟩ := Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωk : ω ∈ fixedField σ := (hk ω).2 (ringEquiv_fix_of_cube hσ3 hω3)
  have hωN : h.norm ω = 1 := by
    rw [UnitaryFieldData.norm, bar_eq_of_cube h hQ hω3, ← pow_succ']
    exact hω3
  have hω2N : h.norm (ω ^ 2) = 1 := by
    rw [UnitaryFieldData.norm, map_pow, bar_eq_of_cube h hQ hω3, ← pow_mul, ← pow_add]
    calc ω ^ (2 + 2 * 2) = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  obtain ⟨Dω, hDω⟩ := exists_diag_mem h ![ω, ω ^ 2, 1]
    (by
      intro i
      fin_cases i
      · exact hωN
      · exact hω2N
      · show h.norm 1 = 1
        simp [UnitaryFieldData.norm])
    (by
      show ω * ω ^ 2 * 1 = 1
      linear_combination hω3)
  set M : Matrix (Fin 3) (Fin 3) K := (((H : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) *
    (H : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMcomm : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
    intro g hg
    have h1 := congrArg (fun x : unitarySU p f K 3 => (x : GL (Fin 3) K)) (hcomm g hg)
    simp only [Subgroup.coe_mul, coe_suConj, Subgroup.coe_inv] at h1
    have h2 : ((H : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) * (H : GL (Fin 3) K)) *
        (g : GL (Fin 3) K) = (g : GL (Fin 3) K) *
          ((H : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) * (H : GL (Fin 3) K)) := by
      calc ((H : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) * (H : GL (Fin 3) K)) *
            (g : GL (Fin 3) K)
          = (H : GL (Fin 3) K)⁻¹ * ((s : GL (Fin 3) K) * ((H : GL (Fin 3) K) *
            (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹)) * (H : GL (Fin 3) K) := by group
        _ = (H : GL (Fin 3) K)⁻¹ * (((H : GL (Fin 3) K) * (g : GL (Fin 3) K) *
            (H : GL (Fin 3) K)⁻¹) * (s : GL (Fin 3) K)) * (H : GL (Fin 3) K) := by rw [h1]
        _ = _ := by group
    have h3 := congrArg Units.val h2
    simp only [Units.val_mul] at h3
    rw [hM, Units.val_mul, Units.val_mul]
    exact h3
  have hDωk : ∀ i j, ((Dω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ := by
    intro i j
    rw [hDω]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [hωk, (fixedField σ).one_mem, (fixedField σ).pow_mem hωk]
    · rw [diagonal_apply_ne _ hij]
      exact (fixedField σ).zero_mem
  have hE : ∃ g : unitarySU p f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat K := ⟨⟨swapGL K, swapGL_mem_unitarySU h⟩, rfl⟩
  have hE' : ∃ g : unitarySU p f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat' K := ⟨⟨swapGL' K, swapGL'_mem_unitarySU h⟩, rfl⟩
  obtain ⟨gE, hgE⟩ := hE
  obtain ⟨gE', hgE'⟩ := hE'
  have h1 := hMcomm Dω hDωk
  have h2 := hMcomm gE (by rw [hgE]; exact swapMat_mem)
  have h3 := hMcomm gE' (by rw [hgE']; exact swapMat'_mem)
  rw [hDω] at h1
  rw [hgE] at h2
  rw [hgE'] at h3
  obtain ⟨c0, hMs⟩ : ∃ c0 : K, M = c0 • (1 : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, eq_smul_one_of_commute M hω h1 h2 h3⟩
  have hsm : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c0 • 1 := by
    have e1 : (s : GL (Fin 3) K) = (H : GL (Fin 3) K) * ((H : GL (Fin 3) K)⁻¹ *
        (s : GL (Fin 3) K) * (H : GL (Fin 3) K)) * (H : GL (Fin 3) K)⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul, ← hM, hMs, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Units.mul_inv]
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hsm, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]

end Item19Res6Proof

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
@[expose] def Seitz199OuterUnitaryDiag : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), p ^ f % 3 = 2 → 2 < p ^ f →
    ∀ (D : Subgroup (MulAut (unitarySU p f K 3))), (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 →
      ¬ D ≤ (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range →
      (∃ e ∈ D, ∃ s : unitarySU p f K 3, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) →
      D ≤ (CFSG.RankThree.PartTwo.KFacts.suConj h).range →
      Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
@[expose] def Seitz199OuterUnitaryEight : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), p ^ f = 8 →
    ∀ (D : Subgroup (MulAut (unitarySU p f K 3))), (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 →
      ¬ D ≤ (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range →
      (∃ e ∈ D, ∃ s : unitarySU p f K 3, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) →
      ¬ D ≤ (CFSG.RankThree.PartTwo.KFacts.suConj h).range →
      Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤

open Item19Res5Proof Item19Res6Proof CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen in
theorem seitz199OuterUnitary_of_diag_eight
    (hA : Seitz199OuterUnitaryDiag) (hB : Seitz199OuterUnitaryEight) : Seitz199OuterUnitary := by
  intro X _ _ D hD3 hD9 hX hSU hinn hnfix
  obtain ⟨q, K, _, _, hKq, hq, ⟨ι⟩⟩ := hSU
  obtain ⟨p, f, h, hQ, hQ2, ⟨ι'⟩⟩ := Item19ResProof.exists_unitary_model hX hKq hq ι
  refine (closure_fixSet_mapAut_eq_top_iff ι' D).mp ?_
  have hD'3 : ∀ φ ∈ mapAut ι' D, φ ^ 3 = 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    change MulAut.congr ι' φ ^ 3 = 1
    rw [← map_pow, hD3 φ hφ, map_one]
  have hD'9 : Nat.card (mapAut ι' D) = 9 := by rw [card_mapAut, hD9]
  have hinn' : ¬ mapAut ι' D ≤ (MulAut.conj : CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 →*
      MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3)).range := fun h' =>
    hinn (le_range_conj_of_mapAut ι' h')
  have hnfix' := exists_moved_mapAut ι' hnfix
  by_cases hdiag : mapAut ι' D ≤ (CFSG.RankThree.PartTwo.KFacts.suConj h).range
  · exact hA p f K h hQ hQ2 _ hD'3 hD'9 hinn' hnfix' hdiag
  by_cases h8 : p ^ f = 8
  · exact hB p f K h h8 _ hD'3 hD'9 hinn' hnfix' hdiag
  obtain ⟨φ, hφD, hφ⟩ := Set.not_subset.1 hdiag
  obtain ⟨e, he, s, -, hsD, hes⟩ := hnfix'
  exact closure_fixSet_eq_top_of_field h hQ hQ2 h8 _ hD'3 hφD hφ he hsD hes

end CFSG.RankThree.PartTwo.Sec19
