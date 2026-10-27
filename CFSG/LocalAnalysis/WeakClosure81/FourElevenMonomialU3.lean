module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrCom
public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.SylowClauseTransport
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.Asc80 CFSG.RankThree.CentralCover
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

noncomputable def stdFourHat (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    Subgroup (SU3F p F) :=
  Subgroup.closure {suOdd₁ F hq, suOdd₂ F hq, suOdd₃ F hq}

noncomputable def stdFour (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    Subgroup (PSU3F p F) :=
  (stdFourHat (F := F) p hq).map (piU p F)

theorem matU_suOdd_one (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    matU (suOdd₁ F hq) = Matrix.diagonal ![1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₁, oddDiag₁, matU, Matrix.diagonal]

theorem matU_suOdd_two (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    matU (suOdd₂ F hq) = Matrix.diagonal ![-1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suOdd₂, oddDiag₂, matU, Matrix.diagonal]

theorem stdFour_eq_closure (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    stdFour (F := F) p hq =
      Subgroup.closure ({piU p F (suOdd₁ F hq), piU p F (suOdd₂ F hq),
        piU p F (suOdd₃ F hq)} : Set (PSU3F p F)) := by
  rw [stdFour, stdFourHat, MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, (rfl | rfl | rfl), rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨suOdd₁ F hq, by simp, rfl⟩
    · exact ⟨suOdd₂ F hq, by simp, rfl⟩
    · exact ⟨suOdd₃ F hq, by simp, rfl⟩

theorem stdFour_data (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hchar : ringChar F ≠ 2)
    (hq : Odd (p ^ 1)) :
    IsKleinFour (stdFour (F := F) p hq) ∧
      (stdFour (F := F) p hq : Set (PSU3F p F)) = {1, piU p F (suOdd₁ F hq), piU p F (suOdd₂ F hq),
        piU p F (suOdd₃ F hq)} ∧
      orderOf (piU p F (suOddA₀ F hq)) = 3 ∧
      piU p F (suOddA₀ F hq) * piU p F (suOdd₁ F hq) * (piU p F (suOddA₀ F hq))⁻¹ =
        piU p F (suOdd₂ F hq) ∧
      piU p F (suOddA₀ F hq) * piU p F (suOdd₂ F hq) * (piU p F (suOddA₀ F hq))⁻¹ =
        piU p F (suOdd₃ F hq) ∧
      piU p F (suOddA₀ F hq) * piU p F (suOdd₃ F hq) * (piU p F (suOddA₀ F hq))⁻¹ =
        piU p F (suOdd₁ F hq) ∧
      orderOf (piU p F (suOddB₀ F hq)) = 2 ∧
      (piU p F (suOddB₀ F hq))⁻¹ * piU p F (suOddA₀ F hq) * piU p F (suOddB₀ F hq) =
        (piU p F (suOddA₀ F hq))⁻¹ ∧
      piU p F (suOddA₀ F hq) ∈ Subgroup.normalizer (stdFour (F := F) p hq : Set (PSU3F p F)) ∧
      piU p F (suOdd₁ F hq) ≠ piU p F (suOdd₂ F hq) := by
  have hcyc := suOddCycled (F := F) (q := p ^ 1) hchar hq
  have hbconj := suOddB₀_conj (F := F) (q := p ^ 1) hq
  have hbsq := suOddB₀_sq (F := F) (q := p ^ 1) hq
  have hker : (piU p F).ker ≤ center (SU3F p F) := ker_statedProjMk_le_center _
  have hp := hcyc.quotient_package hbconj hbsq (piU p F) hker
  obtain ⟨hK4, hset, -, -, -, h12, -, -, ha3, hac1, hac2, hac3, hb2, hbc, haN, -, -, -, -⟩ := hp
  exact ⟨hK4, hset, ha3, hac1, hac2, hac3, hb2, hbc, haN, h12⟩

theorem matrix_isDiag_of_commute_signs {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    {A : Matrix (Fin 3) (Fin 3) F}
    (h1 : A * Matrix.diagonal ![1, -1, -1] = Matrix.diagonal ![1, -1, -1] * A)
    (h2' : A * Matrix.diagonal ![-1, 1, -1] = Matrix.diagonal ![-1, 1, -1] * A) :
    ∀ i j : Fin 3, i ≠ j → A i j = 0 := by
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    exact h2 (by linear_combination -h)
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h2'.symm (by simpa using hneg)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h1.symm (by simpa using hneg.symm)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h2'.symm (by simpa using hneg.symm)
  · exact absurd rfl hij
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h2'.symm (by simpa using hneg.symm)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h1.symm (by simpa using hneg)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal h2'.symm (by simpa using hneg)
  · exact absurd rfl hij

theorem commute_of_proj_commute_sign (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ 2) {A x : SU3F p F}
    (hxdiag : (matU x).IsDiag) (hxentry : ∀ i, matU x i i = 1 ∨ matU x i i = -1)
    (hcomm : piU p F A * piU p F x = piU p F x * piU p F A) :
    matU A * matU x = matU x * matU A := by
  have hqmem : A * x * A⁻¹ * x⁻¹ ∈ (piU p F).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  obtain ⟨c, hc3, hc⟩ := exists_scalar_of_mem_ker hF hqmem
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hc3
    exact zero_ne_one hc3
  let cu : Fˣ := Units.mk0 c hc0
  have hcGL : ((A * x * A⁻¹ * x⁻¹ : SU3F p F) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) cu := by
    have hcu : (cu : F) = c := rfl
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, hcu]
    exact hc
  have hAx : matU A * matU x = Matrix.scalar (Fin 3) c * matU x * matU A := by
    have hgroup : (A * x * A⁻¹ * x⁻¹ : SU3F p F) * x * A = A * x := by group
    have hgroupGL : (((A * x * A⁻¹ * x⁻¹ : SU3F p F) : GL (Fin 3) F) *
        (x : GL (Fin 3) F) * (A : GL (Fin 3) F)) =
        (A : GL (Fin 3) F) * (x : GL (Fin 3) F) := by
      simp
    have hAxGL : (A : GL (Fin 3) F) * (x : GL (Fin 3) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) cu * (x : GL (Fin 3) F) *
          (A : GL (Fin 3) F) := by
      calc (A : GL (Fin 3) F) * (x : GL (Fin 3) F)
          = ((A * x * A⁻¹ * x⁻¹ : SU3F p F) : GL (Fin 3) F) * (x : GL (Fin 3) F) *
              (A : GL (Fin 3) F) := hgroupGL.symm
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) cu * (x : GL (Fin 3) F) *
              (A : GL (Fin 3) F) := by rw [hcGL]
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hAxGL
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      show (cu : F) = c from rfl] at this
    simpa [matU] using this
  let d : Fin 3 → F := fun i => matU x i i
  have hxd : matU x = Matrix.diagonal d := (Matrix.IsDiag.diagonal_diag hxdiag).symm
  have hA0 : matU A ≠ 0 := by
    intro hz
    have hdet : (matU A).det = 1 := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU A.2
    rw [hz, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 3, matU A a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hA0 (by ext i j; exact h i j)
  have hentry : d b = c * d a := by
    have h := congrFun (congrFun hAx a) b
    rw [hxd, Matrix.mul_diagonal, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul] at h
    have h' : d b * matU A a b = (c * d a) * matU A a b := by
      rw [mul_comm (d b) (matU A a b)]
      exact h.trans (by ring)
    exact mul_right_cancel₀ hab h'
  have hda : d a * d a = 1 := by
    change matU x a a * matU x a a = 1
    rcases hxentry a with ha | ha <;> rw [ha] <;> norm_num
  have hdb : d b * d b = 1 := by
    change matU x b b * matU x b b = 1
    rcases hxentry b with hb | hb <;> rw [hb] <;> norm_num
  have hc_sq : c * c = 1 := by
    have hc_eq : c = d b * d a := by
      calc c = c * (d a * d a) := by rw [hda]; ring
        _ = (c * d a) * d a := by ring
        _ = d b * d a := by rw [← hentry]
    rw [hc_eq]
    calc (d b * d a) * (d b * d a) = (d b * d b) * (d a * d a) := by ring
      _ = 1 := by rw [hdb, hda]; ring
  have hc_one : c = 1 := by
    have hc_cube : c ^ 3 = c := by rw [pow_three, hc_sq]; ring
    rw [hc_cube] at hc3
    exact hc3
  rw [hc_one] at hAx
  simpa [Matrix.scalar_apply] using hAx

theorem centralizer_stdFour_eq_diagCU (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hchar : ringChar F ≠ 2) (hq : Odd (p ^ 1)) :
    Subgroup.centralizer (stdFour (F := F) p hq : Set (PSU3F p F)) = diagCU hF := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_u hp2 hF
  have hx1_diag : suOdd₁ F hq ∈ diagU hF := by
    rw [mem_diagU_iff, matU_suOdd_one]
    simp [Matrix.diagonal]
  have hx2_diag : suOdd₂ F hq ∈ diagU hF := by
    rw [mem_diagU_iff, matU_suOdd_two]
    simp [Matrix.diagonal]
  have hx3_diag : suOdd₃ F hq ∈ diagU hF := by
    rw [mem_diagU_iff]
    have hmul : matU (suOdd₃ F hq) = matU (suOdd₁ F hq) * matU (suOdd₂ F hq) := by
      have hcyc := suOddCycled (F := F) (q := p ^ 1) hchar hq
      have h := (congrArg matU hcyc.mul_eq).symm
      simpa [matU_mul] using h
    rw [hmul]
    rw [matU_suOdd_one, matU_suOdd_two]
    simp [Matrix.mul_apply, Matrix.diagonal]
  have hWle : stdFour (F := F) p hq ≤ diagCU hF := by
    rw [stdFour_eq_closure, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.mem_map_of_mem (piU p F) hx1_diag
    · exact Subgroup.mem_map_of_mem (piU p F) hx2_diag
    · exact Subgroup.mem_map_of_mem (piU p F) hx3_diag
  apply le_antisymm
  · intro g hg
    obtain ⟨A, rfl⟩ := piU_surjective g
    have hx1mem : piU p F (suOdd₁ F hq) ∈ stdFour (F := F) p hq := by
      rw [stdFour_eq_closure]
      exact Subgroup.subset_closure (by simp)
    have hx2mem : piU p F (suOdd₂ F hq) ∈ stdFour (F := F) p hq := by
      rw [stdFour_eq_closure]
      exact Subgroup.subset_closure (by simp)
    have hc1 : piU p F (suOdd₁ F hq) * piU p F A = piU p F A * piU p F (suOdd₁ F hq) :=
      Subgroup.mem_centralizer_iff.mp hg _ hx1mem
    have hc2 : piU p F (suOdd₂ F hq) * piU p F A = piU p F A * piU p F (suOdd₂ F hq) :=
      Subgroup.mem_centralizer_iff.mp hg _ hx2mem
    have hA1 : matU A * matU (suOdd₁ F hq) = matU (suOdd₁ F hq) * matU A :=
      commute_of_proj_commute_sign p hF (x := suOdd₁ F hq)
        (by rw [matU_suOdd_one]; exact Matrix.isDiag_diagonal _)
        (by intro i; rw [matU_suOdd_one]; fin_cases i <;> simp) hc1.symm
    have hA2 : matU A * matU (suOdd₂ F hq) = matU (suOdd₂ F hq) * matU A :=
      commute_of_proj_commute_sign p hF (x := suOdd₂ F hq)
        (by rw [matU_suOdd_two]; exact Matrix.isDiag_diagonal _)
        (by intro i; rw [matU_suOdd_two]; fin_cases i <;> simp) hc2.symm
    have hA1' : matU A * Matrix.diagonal ![1, -1, -1] =
        Matrix.diagonal ![1, -1, -1] * matU A := by
      rwa [matU_suOdd_one] at hA1
    have hA2' : matU A * Matrix.diagonal ![-1, 1, -1] =
        Matrix.diagonal ![-1, 1, -1] * matU A := by
      rwa [matU_suOdd_two] at hA2
    have hoff := matrix_isDiag_of_commute_signs h2 hA1' hA2'
    refine Subgroup.mem_map.mpr ⟨A, ?_, rfl⟩
    rw [mem_diagU_iff]
    exact ⟨hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
      hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact diagCU_comm (hWle hw) hg

theorem matU_suOddB0 (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (hq : Odd (p ^ 1)) :
    matU (suOddB₀ F hq) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suOddB₀, oddB₀, matU]

theorem suOddB0_conj_suOdd_one (p : ℕ) [Fact p.Prime] {F : Type} [Field F]
    (hq : Odd (p ^ 1)) :
    suOddB₀ F hq * suOdd₁ F hq * (suOddB₀ F hq)⁻¹ = suOdd₂ F hq ∧
      suOddB₀ F hq * suOdd₂ F hq * (suOddB₀ F hq)⁻¹ = suOdd₁ F hq := by
  have hbsq := suOddB₀_sq (F := F) (q := p ^ 1) hq
  have hbinv : (suOddB₀ F hq)⁻¹ = suOddB₀ F hq :=
    inv_eq_of_mul_eq_one_right (by simpa [sq] using hbsq)
  have hb1 : suOddB₀ F hq * suOdd₁ F hq * (suOddB₀ F hq)⁻¹ = suOdd₂ F hq := by
    apply ext_matU
    rw [matU_mul, matU_mul, hbinv, matU_suOddB0, matU_suOdd_one, matU_suOdd_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul]
  have hbb : suOddB₀ F hq * suOddB₀ F hq = 1 := by
    rw [← sq]
    exact hbsq
  have hb2 : suOddB₀ F hq * suOdd₂ F hq * (suOddB₀ F hq)⁻¹ = suOdd₁ F hq := by
    calc suOddB₀ F hq * suOdd₂ F hq * (suOddB₀ F hq)⁻¹
        = suOddB₀ F hq * (suOddB₀ F hq * suOdd₁ F hq * (suOddB₀ F hq)⁻¹) *
            (suOddB₀ F hq)⁻¹ := by rw [hb1]
      _ = (suOddB₀ F hq * suOddB₀ F hq) * suOdd₁ F hq *
            (suOddB₀ F hq * suOddB₀ F hq)⁻¹ := by group
      _ = suOdd₁ F hq := by rw [hbb]; group
  exact ⟨hb1, hb2⟩

theorem suOddB0_normalizes_stdFourHat (p : ℕ) [Fact p.Prime] {F : Type} [Field F]
    (hF : Nat.card F = p ^ 2) (hchar : ringChar F ≠ 2) (hq : Odd (p ^ 1)) :
    suOddB₀ F hq ∈ Subgroup.normalizer (stdFourHat (F := F) p hq : Set (SU3F p F)) := by
  obtain ⟨hb1, hb2⟩ := suOddB0_conj_suOdd_one (F := F) p hq
  have hbsq := suOddB₀_sq (F := F) (q := p ^ 1) hq
  have hbinv : (suOddB₀ F hq)⁻¹ = suOddB₀ F hq :=
    inv_eq_of_mul_eq_one_right (by simpa [sq] using hbsq)
  have hcyc := suOddCycled (F := F) (q := p ^ 1) hchar hq
  have hx1_diag : suOdd₁ F hq ∈ diagU hF := by
    rw [mem_diagU_iff, matU_suOdd_one]
    simp [Matrix.diagonal]
  have hx2_diag : suOdd₂ F hq ∈ diagU hF := by
    rw [mem_diagU_iff, matU_suOdd_two]
    simp [Matrix.diagonal]
  have hm1 : (matU (suOdd₁ F hq)).IsDiag := by
    rw [matU_suOdd_one]
    exact Matrix.isDiag_diagonal _
  have hm2 : (matU (suOdd₂ F hq)).IsDiag := by
    rw [matU_suOdd_two]
    exact Matrix.isDiag_diagonal _
  have hcomm12 : suOdd₁ F hq * suOdd₂ F hq = suOdd₂ F hq * suOdd₁ F hq := by
    apply ext_matU
    rw [matU_mul, matU_mul]
    exact CFSG.GH74.Generic.BProg.B2.FixFourS3.matrix_diag_comm hm1 hm2
  have hb3 : suOddB₀ F hq * suOdd₃ F hq * (suOddB₀ F hq)⁻¹ = suOdd₃ F hq := by
    have hx3eq : suOdd₃ F hq = suOdd₁ F hq * suOdd₂ F hq := hcyc.mul_eq.symm
    rw [hx3eq]
    calc suOddB₀ F hq * (suOdd₁ F hq * suOdd₂ F hq) * (suOddB₀ F hq)⁻¹
        = (suOddB₀ F hq * suOdd₁ F hq * (suOddB₀ F hq)⁻¹) *
            (suOddB₀ F hq * suOdd₂ F hq * (suOddB₀ F hq)⁻¹) := by group
      _ = suOdd₂ F hq * suOdd₁ F hq := by rw [hb1, hb2]
      _ = suOdd₁ F hq * suOdd₂ F hq := hcomm12.symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, stdFourHat, MonoidHom.map_closure]
  change Subgroup.closure (Set.image
      (fun z : SU3F p F => MulAut.conj (suOddB₀ F hq) z)
      ({suOdd₁ F hq, suOdd₂ F hq, suOdd₃ F hq} : Set (SU3F p F))) =
    Subgroup.closure {suOdd₁ F hq, suOdd₂ F hq, suOdd₃ F hq}
  have hset : Set.image (fun z : SU3F p F => MulAut.conj (suOddB₀ F hq) z)
      ({suOdd₁ F hq, suOdd₂ F hq, suOdd₃ F hq} : Set (SU3F p F)) =
      {suOdd₁ F hq, suOdd₂ F hq, suOdd₃ F hq} := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, MulAut.conj_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hg with rfl | rfl | rfl
      · exact Or.inr (Or.inl hb1)
      · exact Or.inl hb2
      · exact Or.inr (Or.inr hb3)
    · rintro (rfl | rfl | rfl)
      · exact ⟨suOdd₂ F hq, by simp, hb2⟩
      · exact ⟨suOdd₁ F hq, by simp, hb1⟩
      · exact ⟨suOdd₃ F hq, by simp, hb3⟩
  rw [hset]

def MonomialFrame {G : Type*} [Group G] (W : Subgroup G) : Prop :=
  ⁅Subgroup.centralizer (W : Set G), Subgroup.centralizer (W : Set G)⁆ = ⊥ ∧
    (Subgroup.centralizer (W : Set G)).relIndex
        (Subgroup.normalizer (W : Set G)) = 6 ∧
      ∃ X₀ : Subgroup G, X₀ ≤ Subgroup.normalizer (W : Set G) ∧
        X₀ ⊓ Subgroup.centralizer (W : Set G) =
            pCoreOf 2 (Subgroup.centralizer (W : Set G)) ∧
          X₀ ⊔ Subgroup.centralizer (W : Set G) = Subgroup.normalizer (W : Set G)

def MonomialFrameIn {G : Type*} [Group G] (L W : Subgroup G) : Prop :=
  ⁅L ⊓ Subgroup.centralizer (W : Set G), L ⊓ Subgroup.centralizer (W : Set G)⁆ = ⊥ ∧
    (L ⊓ Subgroup.centralizer (W : Set G)).relIndex
        (L ⊓ Subgroup.normalizer (W : Set G)) = 6 ∧
      ∃ X₀ : Subgroup G, X₀ ≤ L ⊓ Subgroup.normalizer (W : Set G) ∧
        X₀ ⊓ (L ⊓ Subgroup.centralizer (W : Set G)) =
            pCoreOf 2 (L ⊓ Subgroup.centralizer (W : Set G)) ∧
          X₀ ⊔ (L ⊓ Subgroup.centralizer (W : Set G)) =
            L ⊓ Subgroup.normalizer (W : Set G)

theorem monomialFrame_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {W : Subgroup G} (h : MonomialFrame W) :
    MonomialFrame (W.map e.toMonoidHom) := by
  obtain ⟨hcomm, hrel, X₀, hXle, hXinf, hXsup⟩ := h
  have hC : (Subgroup.centralizer (W : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (W.map e.toMonoidHom : Set H) := by
    rw [Subgroup.coe_map]
    exact CFSG.AGLEmbeddingD2.Wilson.Proving.map_centralizer_eq_image e (W : Set G)
  have hN : (Subgroup.normalizer (W : Set G)).map e.toMonoidHom =
      Subgroup.normalizer (W.map e.toMonoidHom : Set H) :=
    Subgroup.map_equiv_normalizer_eq W e
  refine ⟨?_, ?_, ⟨X₀.map e.toMonoidHom, ?_, ?_, ?_⟩⟩
  · rw [← hC, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  · rw [← hC, ← hN, Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _
      e.injective]
    exact hrel
  · rw [← hN]
    exact Subgroup.map_mono hXle
  · rw [← hC, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective, hXinf,
      ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e]
  · rw [← hN, ← hC, ← Subgroup.map_sup, hXsup]

theorem monomialFrameIn_subtype {G : Type*} [Group G] {L : Subgroup G} {W : Subgroup L}
    (h : MonomialFrame W) : MonomialFrameIn L (W.map L.subtype) := by
  obtain ⟨hcomm, hrel, X₀, hXle, hXinf, hXsup⟩ := h
  let WL : Subgroup G := W.map L.subtype
  have hWLle : WL ≤ L := Subgroup.map_subtype_le W
  have hWLsub : WL.subgroupOf L = W := by
    change (W.map L.subtype).subgroupOf L = W
    rw [Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective W
  have hCsub0 : (Subgroup.centralizer (WL : Set G)).subgroupOf L =
      Subgroup.centralizer ((WL.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    ext x
    constructor
    · intro hx y hy
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_centralizer_iff] at hx
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hx y (Subgroup.mem_subgroupOf.mp hy)
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hyL : y ∈ L := hWLle hy
      have := hx ⟨y, hyL⟩ (Subgroup.mem_subgroupOf.mpr hy)
      simpa using congrArg (fun z : ↥L => (z : G)) this
  have hCsub : (Subgroup.centralizer (WL : Set G)).subgroupOf L =
      Subgroup.centralizer (W : Set ↥L) := by
    rw [hCsub0, hWLsub]
  have hCmap : (Subgroup.centralizer (W : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer (WL : Set G) := by
    rw [← hCsub, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hNsub : (Subgroup.normalizer (WL : Set G)).subgroupOf L =
      Subgroup.normalizer (W : Set ↥L) := by
    rw [Subgroup.subgroupOf_normalizer_eq hWLle, hWLsub]
  have hNmap : (Subgroup.normalizer (W : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer (WL : Set G) := by
    rw [← hNsub, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcomm' : ⁅L ⊓ Subgroup.centralizer (WL : Set G),
      L ⊓ Subgroup.centralizer (WL : Set G)⁆ = ⊥ := by
    rw [← hCmap, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  have hrel' : (L ⊓ Subgroup.centralizer (WL : Set G)).relIndex
      (L ⊓ Subgroup.normalizer (WL : Set G)) = 6 := by
    rw [← hCmap, ← hNmap]
    rw [Subgroup.relIndex_map_map_of_injective (f := L.subtype) _ _ L.subtype_injective]
    exact hrel
  have hpcmap : pCoreOf 2 ((Subgroup.centralizer (W : Set ↥L)).map L.subtype) =
      (pCoreOf 2 (Subgroup.centralizer (W : Set ↥L))).map L.subtype :=
    CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 L.subtype L.subtype_injective _
  refine ⟨hcomm', hrel', ⟨X₀.map L.subtype, ?_, ?_, ?_⟩⟩
  · rw [← hNmap]
    exact Subgroup.map_mono hXle
  · rw [← hCmap, ← Subgroup.map_inf _ _ L.subtype L.subtype_injective, hXinf,
      hpcmap]
  · rw [← hNmap, ← hCmap, ← Subgroup.map_sup, hXsup]

theorem monomialFrame_stdFour (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hchar : ringChar F ≠ 2)
    (hq : Odd (p ^ 1)) : MonomialFrame (stdFour (F := F) p hq) := by
  obtain ⟨hK4, hVset, ha3_0, hac1_0, hac2_0, hac3_0, hb2_0, hbc_0, haN_0, h12_0⟩ :=
    stdFour_data p hchar hq
  have hK4inst : IsKleinFour (stdFour (F := F) p hq) := hK4
  let C : Subgroup (PSU3F p F) :=
    Subgroup.centralizer (stdFour (F := F) p hq : Set (PSU3F p F))
  let N : Subgroup (PSU3F p F) :=
    Subgroup.normalizer (stdFour (F := F) p hq : Set (PSU3F p F))
  have hCeq : C = diagCU hF := centralizer_stdFour_eq_diagCU p hp2 hF hchar hq
  have hcomm : ⁅C, C⁆ = ⊥ := by
    rw [hCeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact diagCU_comm hb ha
  set xa : PSU3F p F := piU p F (suOddA₀ F hq) with hxadef
  set xb : PSU3F p F := piU p F (suOddB₀ F hq) with hxbdef
  have ha3 : orderOf xa = 3 := by rw [hxadef]; exact ha3_0
  have hb2 : orderOf xb = 2 := by rw [hxbdef]; exact hb2_0
  have hac1 : xa * piU p F (suOdd₁ F hq) * xa⁻¹ = piU p F (suOdd₂ F hq) := by
    rw [hxadef]; exact hac1_0
  have hb_x1 : xb * piU p F (suOdd₁ F hq) * xb⁻¹ = piU p F (suOdd₂ F hq) := by
    rw [hxbdef]
    obtain ⟨hb1, -⟩ := suOddB0_conj_suOdd_one (F := F) p hq
    have h := congrArg (piU p F) hb1
    simpa [map_mul, map_inv] using h
  have hx1W : piU p F (suOdd₁ F hq) ∈ stdFour (F := F) p hq := by
    show piU p F (suOdd₁ F hq) ∈ (stdFour (F := F) p hq : Set (PSU3F p F))
    rw [hVset]
    simp
  have haN : xa ∈ N := by
    simpa [N] using haN_0
  have hbN : xb ∈ N := by
    have h := Subgroup.le_normalizer_map (piU p F) (H := stdFourHat (F := F) p hq)
      ⟨suOddB₀ F hq, suOddB0_normalizes_stdFourHat p hF hchar hq, rfl⟩
    simpa [N, stdFour, hxbdef] using h
  let K : Subgroup (PSU3F p F) := Subgroup.closure ({xa, xb} : Set (PSU3F p F))
  have hKsup : K = Subgroup.zpowers xa ⊔ Subgroup.zpowers xb := by
    change Subgroup.closure ({xa, xb} : Set (PSU3F p F)) =
      Subgroup.zpowers xa ⊔ Subgroup.zpowers xb
    have hpair : ({xa, xb} : Set (PSU3F p F)) = ({xa} : Set (PSU3F p F)) ∪ {xb} := by
      ext z
      simp [or_comm]
    rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure xa,
      ← Subgroup.zpowers_eq_closure xb]
  have hxbsq : xb ^ 2 = 1 := by
    simpa [hb2] using pow_orderOf_eq_one xb
  have hbb : xb * xb = 1 := by
    rw [← sq]
    exact hxbsq
  have hbinv : xb⁻¹ = xb := inv_eq_of_mul_eq_one_right hbb
  have hb_conj : xb * xa * xb = xa⁻¹ := by
    have h : xb⁻¹ * xa * xb = xa⁻¹ := by
      rw [hxadef, hxbdef]
      exact hbc_0
    rwa [← hbinv] at h
  have hconj_zpow : ∀ n : ℤ, xb * xa ^ n * xb⁻¹ = (xa⁻¹) ^ n := by
    intro n
    rw [hbinv]
    calc xb * xa ^ n * xb = (xb * xa * xb) ^ n :=
          (conj_zpow (a := xb) (b := xa) (i := n)).symm
      _ = (xa⁻¹) ^ n := by rw [hb_conj]
  have hb_norm_zp : Subgroup.zpowers xb ≤
      Subgroup.normalizer (Subgroup.zpowers xa : Set (PSU3F p F)) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨-n, ?_⟩
      calc xa ^ (-n) = (xa⁻¹) ^ n := by rw [inv_zpow, zpow_neg]
        _ = xb * xa ^ n * xb⁻¹ := (hconj_zpow n).symm
    · rintro ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      calc xa ^ (-m) = (xa⁻¹) ^ m := by rw [inv_zpow, zpow_neg]
        _ = xb * xa ^ m * xb⁻¹ := (hconj_zpow m).symm
        _ = xb * (xb * g * xb⁻¹) * xb⁻¹ := by rw [← hm]
        _ = g := by
          have h1 : xb * (xb * g * xb⁻¹) * xb⁻¹ = (xb * xb) * g * (xb⁻¹ * xb⁻¹) := by
            group
          rw [h1, hbb, hbinv, hbb]
          group
  have hKdisj : Subgroup.zpowers xa ⊓ Subgroup.zpowers xb = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
      rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hb2]
      norm_num))
  have hKcard : Nat.card K = 6 := by
    rw [hKsup, card_sup_eq_mul_of_le_normalizer hb_norm_zp hKdisj,
      Nat.card_zpowers, Nat.card_zpowers, ha3, hb2]
  have hKleN : K ≤ N := by
    rw [show K = Subgroup.closure ({xa, xb} : Set (PSU3F p F)) from rfl,
      Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact haN
    · exact hbN
  have hCleN : C ≤ N := Subgroup.centralizer_le_normalizer _
  let KN : Subgroup N := K.subgroupOf N
  let φ : N →* MulAut (stdFour (F := F) p hq) :=
    (stdFour (F := F) p hq).normalizerMonoidHom
  let H : Subgroup (MulAut (stdFour (F := F) p hq)) := KN.map φ
  have haKN : (⟨xa, haN⟩ : N) ∈ KN := by
    change (⟨xa, haN⟩ : N) ∈ K.subgroupOf N
    rw [Subgroup.mem_subgroupOf]
    show xa ∈ K
    change xa ∈ Subgroup.closure ({xa, xb} : Set (PSU3F p F))
    exact Subgroup.subset_closure (by simp)
  have hbKN : (⟨xb, hbN⟩ : N) ∈ KN := by
    change (⟨xb, hbN⟩ : N) ∈ K.subgroupOf N
    rw [Subgroup.mem_subgroupOf]
    show xb ∈ K
    change xb ∈ Subgroup.closure ({xa, xb} : Set (PSU3F p F))
    exact Subgroup.subset_closure (by simp)
  have hphi_a_ne : φ ⟨xa, haN⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨xa, haN⟩ ⟨piU p F (suOdd₁ F hq), hx1W⟩ =
        ⟨piU p F (suOdd₁ F hq), hx1W⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    change xa * piU p F (suOdd₁ F hq) * xa⁻¹ = piU p F (suOdd₁ F hq) at h2
    rw [hac1] at h2
    exact h12_0 h2.symm
  have hphi_b_ne : φ ⟨xb, hbN⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨xb, hbN⟩ ⟨piU p F (suOdd₁ F hq), hx1W⟩ =
        ⟨piU p F (suOdd₁ F hq), hx1W⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    change xb * piU p F (suOdd₁ F hq) * xb⁻¹ = piU p F (suOdd₁ F hq) at h2
    rw [hb_x1] at h2
    exact h12_0 h2.symm
  have hphi_a3 : orderOf (φ ⟨xa, haN⟩) = 3 := by
    have hdvd : orderOf (φ ⟨xa, haN⟩) ∣ 3 := by
      have := orderOf_map_dvd φ ⟨xa, haN⟩
      rwa [Subgroup.orderOf_mk, ha3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hphi_a_ne
    · exact h3
  have hphi_b2 : orderOf (φ ⟨xb, hbN⟩) = 2 := by
    have hdvd : orderOf (φ ⟨xb, hbN⟩) ∣ 2 := by
      have := orderOf_map_dvd φ ⟨xb, hbN⟩
      rwa [Subgroup.orderOf_mk, hb2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact absurd (orderOf_eq_one_iff.mp h1) hphi_b_ne
    · exact h2'
  have hcardH : Nat.card H = 2 ∨ Nat.card H = 6 :=
    kleinFour_automorphism_subgroup_card (stdFour (F := F) p hq) H (φ ⟨xb, hbN⟩)
      (Subgroup.mem_map_of_mem φ hbKN) hphi_b2
  have hcardH6 : Nat.card H = 6 := by
    rcases hcardH with h2' | h6
    · have hdvd : orderOf (φ ⟨xa, haN⟩) ∣ Nat.card H := by
        let hx : H := ⟨φ ⟨xa, haN⟩, Subgroup.mem_map_of_mem φ haKN⟩
        have h := orderOf_dvd_natCard hx
        rwa [Subgroup.orderOf_mk] at h
      rw [h2', hphi_a3] at hdvd
      exact absurd hdvd (by norm_num)
    · exact h6
  have hHtop : H = ⊤ :=
    kleinFour_automorphism_subgroup_eq_top_of_card_six (stdFour (F := F) p hq) H hcardH6
  have hKC : N ≤ K ⊔ C := by
    intro n hn
    have hmem : φ ⟨n, hn⟩ ∈ H := by
      rw [hHtop]
      exact Subgroup.mem_top _
    obtain ⟨kn, hkn, hkneq⟩ := Subgroup.mem_map.mp hmem
    have hkK : (kn : PSU3F p F) ∈ K := Subgroup.mem_subgroupOf.mp hkn
    have hker : (⟨n, hn⟩ : N) * kn⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkneq, mul_inv_cancel]
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    have hmemC : ((⟨n, hn⟩ : N) * kn⁻¹ : N) ∈ C.subgroupOf N := hker
    have hmemC' : n * (kn : PSU3F p F)⁻¹ ∈ C :=
      Subgroup.mem_subgroupOf.mp hmemC
    have hn_eq : n = (n * (kn : PSU3F p F)⁻¹) * (kn : PSU3F p F) := by group
    rw [hn_eq, sup_comm]
    exact Subgroup.mul_mem_sup hmemC' hkK
  have hKCeq : K ⊔ C = N := le_antisymm (sup_le hKleN hCleN) hKC
  have hKNcard : Nat.card KN = 6 := by
    change Nat.card (K.subgroupOf N) = 6
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleN).toEquiv).trans hKcard
  let f : KN →* MulAut (stdFour (F := F) p hq) := φ.comp KN.subtype
  have hfrange : f.range = H := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardker : Nat.card f.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfrange, hcardH6, hKNcard] at h
    have h' : Nat.card f.ker * 6 = 1 * 6 := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hkerbot : f.ker = ⊥ := f.ker.eq_bot_of_card_eq hcardker
  have hKinfC : K ⊓ C = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzK, hzC⟩ := hz
    have hzKN : (⟨⟨z, hKleN hzK⟩, Subgroup.mem_subgroupOf.mpr hzK⟩ : KN) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      show φ ⟨z, hKleN hzK⟩ = 1
      have hzphi : (⟨z, hKleN hzK⟩ : N) ∈ φ.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact Subgroup.mem_subgroupOf.mpr hzC
      exact MonoidHom.mem_ker.mp hzphi
    rw [hkerbot, Subgroup.mem_bot] at hzKN
    rw [Subgroup.mem_bot]
    exact congrArg (fun x : KN => ((x : N) : PSU3F p F)) hzKN
  let O : Subgroup (PSU3F p F) := pCoreOf 2 C
  let X₀ : Subgroup (PSU3F p F) := K ⊔ O
  have hCleNO : Subgroup.normalizer (C : Set (PSU3F p F)) ≤
      Subgroup.normalizer (O : Set (PSU3F p F)) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C
  have hKleNC : K ≤ Subgroup.normalizer (C : Set (PSU3F p F)) := by
    have hNormal : (C.subgroupOf N).Normal := inferInstance
    exact hKleN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hCleN).mp inferInstance)
  have hKleNO : K ≤ Subgroup.normalizer (O : Set (PSU3F p F)) :=
    hKleNC.trans hCleNO
  have hXleN : X₀ ≤ N := by
    change K ⊔ O ≤ N
    exact sup_le hKleN ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2) C).trans hCleN)
  have hXOinfC : X₀ ⊓ C = O := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hzX, hzC⟩ := hz
      have hXset : (X₀ : Set (PSU3F p F)) = (K : Set (PSU3F p F)) * (O : Set (PSU3F p F)) := by
        change ((K ⊔ O : Subgroup (PSU3F p F)) : Set (PSU3F p F)) =
          (K : Set (PSU3F p F)) * (O : Set (PSU3F p F))
        rw [Subgroup.coe_mul_of_left_le_normalizer_right K O hKleNO]
      change z ∈ (X₀ : Set (PSU3F p F)) at hzX
      rw [hXset] at hzX
      obtain ⟨k, hkK, o, hoO, rfl⟩ := Set.mem_mul.mp hzX
      have hoC : o ∈ C := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) C hoO
      have hkC : k ∈ C := by
        have : k = (k * o) * o⁻¹ := by group
        rw [this]
        exact C.mul_mem hzC (C.inv_mem hoC)
      have hkbot : k ∈ (⊥ : Subgroup (PSU3F p F)) := by
        rw [← hKinfC]
        exact ⟨hkK, hkC⟩
      rw [Subgroup.mem_bot] at hkbot
      rw [hkbot, one_mul]
      exact hoO
    · intro z hz
      exact ⟨Subgroup.mem_sup_right hz, CFSG.LieType.BorelTits.pCoreOf_le (r := 2) C hz⟩
  have hXOsupC : X₀ ⊔ C = N := by
    change (K ⊔ O) ⊔ C = N
    rw [sup_assoc, sup_eq_right.mpr (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) C)]
    exact hKCeq
  have h6 : C.relIndex N = 6 := by
    have hcardN : Nat.card N = 6 * Nat.card C := by
      rw [← hKCeq, sup_comm,
        card_sup_eq_mul_of_le_normalizer (N := C) (H := K) hKleNC
          (by rw [inf_comm, hKinfC]), hKcard, Nat.mul_comm]
    have hrelmul := Subgroup.relIndex_mul_card (H := C) (K := N)
    rw [inf_eq_left.mpr hCleN] at hrelmul
    have hCne : Nat.card C ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1, C.one_mem⟩, inferInstance⟩
    have h' : C.relIndex N * Nat.card C = 6 * Nat.card C := by
      rw [hrelmul, hcardN]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hCne) h'
  exact ⟨hcomm, h6, X₀, hXleN, hXOinfC, hXOsupC⟩

omit [Finite Q] in
theorem exists_monomial_frame_psu3 {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ 2) {L : Subgroup Q} (ψ : PSU3F p F ≃* ↥L) {W : Subgroup Q}
    (hWL : W ≤ L) (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) :
    ⁅L ⊓ centralizer (W : Set Q), L ⊓ centralizer (W : Set Q)⁆ = ⊥ ∧
      (L ⊓ centralizer (W : Set Q)).relIndex (L ⊓ normalizer (W : Set Q)) = 6 ∧
      ∃ X₀ : Subgroup Q, X₀ ≤ L ⊓ normalizer (W : Set Q) ∧
        X₀ ⊓ (L ⊓ centralizer (W : Set Q)) = pCoreOf 2 (L ⊓ centralizer (W : Set Q)) ∧
        X₀ ⊔ (L ⊓ centralizer (W : Set Q)) = L ⊓ normalizer (W : Set Q) := by
  have hFiniteF : Finite F := by
    apply Nat.finite_of_card_ne_zero
    rw [hF]
    exact (pow_pos (Fact.out : p.Prime).pos 2).ne'
  have hq : Odd (p ^ 1) := by
    simpa using (Fact.out : p.Prime).odd_of_ne_two hp2
  have hchar : ringChar F ≠ 2 :=
    ringChar_ne_two_of_card_eq_sq (q := p ^ 1) hq (by simpa using hF)
  change MonomialFrameIn L W
  let WL : Subgroup ↥L := W.subgroupOf L
  let W' : Subgroup (PSU3F p F) := WL.map ψ.symm.toMonoidHom
  have hW'card : Nat.card W' = 4 := by
    calc Nat.card W' = Nat.card WL := Subgroup.card_map_of_injective ψ.symm.injective
      _ = Nat.card W := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
      _ = 4 := hW4
  have hW'elem : IsElemAbelian 2 W' :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf hW L) ψ.symm.toMonoidHom
  have hW'class : CFSG.IsElementaryAbelian 2 W' := IsElemAbelian.isElementaryAbelian hW'elem
  have hK4std : IsKleinFour (stdFour (F := F) p hq) := (stdFour_data p hchar hq).1
  have hstdclass : CFSG.IsElementaryAbelian 2 (stdFour (F := F) p hq) :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp [IsKleinFour.exponent_two] }
  have hstdcard : Nat.card (stdFour (F := F) p hq) = 4 := IsKleinFour.card_four
  obtain ⟨s, hs⟩ := CFSG.GH74.Generic.BProg.B2.FixFourS3.exists_conj_four_statedSU3
    (K := F) (p := p) (f := 1) (Fact.out) hp2
    (by simpa using hF) hstdclass hstdcard hW'class hW'card
  have hframeStd : MonomialFrame (stdFour (F := F) p hq) :=
    monomialFrame_stdFour p hp2 hF hchar hq
  have hframeW' : MonomialFrame W' := by
    rw [hs]
    exact monomialFrame_map_mulEquiv (MulAut.conj (QuotientGroup.mk s)) hframeStd
  have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id ↥L := by
    ext x
    simp
  have hW'ψ : W'.map ψ.toMonoidHom = WL := by
    change (WL.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = WL
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hframeWL : MonomialFrame WL := by
    have := monomialFrame_map_mulEquiv ψ hframeW'
    rwa [hW'ψ] at this
  have hIn := monomialFrameIn_subtype hframeWL
  rwa [Subgroup.map_subgroupOf_eq_of_le hWL] at hIn

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
